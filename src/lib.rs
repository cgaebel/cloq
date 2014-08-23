//! A queue of unboxed closures. CloQ for short.
#![feature(unboxed_closures)]
#![deny(missing_doc)]

#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variable)]

// TODO(cgaebel): Protect against integer overflow leading to heap corruption.
// TODO(cgaebel): Security audit, remove as much unsafety as possible, etc.

// Ideally we'd use allocators instead of the `alloc` library directly.
extern crate alloc;
extern crate core;

use alloc::heap::{allocate,deallocate,reallocate};
use core::intrinsics::{copy_memory,copy_nonoverlapping_memory};
use core::mem;
use core::num;
use core::ptr::RawPtr;
use core::raw;

use serialize::{Serializer,FnSerializer,FnMutSerializer,FnOnceSerializer,call};

pub mod serialize;

/// A closure can either be removed from the queue, or be moved to the back.
/// The closure itself is allowed to dictate this behavior, so it must return
/// an element of this enum.
#[deriving(PartialEq, Eq, Show)]
pub enum StopCondition {
  /// Do not reschedule the closure at the end of the queue. Drop it.
  Stop,
  /// Reschedule the closure at the end of the queue. Do not drop it.
  KeepGoing,
}

/// The number of bytes that need to be allocated in the buffer for a closure
/// with a payload of size `len`.
///
/// We need space for the code ptr, the length of the data buffer, and the
/// buffer itself.
fn byte_len(len: uint) -> uint {
  ptr_size() + len_size() + len
}

/// The size of a pointer on this architecture.
fn ptr_size() -> uint {
  mem::size_of::<*const ()>()
}

/// The size of a buffer length on this architecture.
fn len_size() -> uint {
  mem::size_of::<uint>()
}

/// The preferred alignment of every data element in the CloQ.
fn align() -> uint {
  mem::align_of::<*const ()>()
}

/// Copy some immediate value (ex. u8, u32, etc.) into a byte buffer.
unsafe fn serialize_imm<T>(dst: &mut [u8], t: T) {
  let t_ptr: *const u8 = mem::transmute(&t);
  let t_len: uint      = mem::size_of_val(&t);
  copy_nonoverlapping_memory(dst.as_mut_ptr(), t_ptr, t_len);
}

/// Copy an immediate value (ex. u8, u32, etc.) out of a byte buffer, and return
/// it.
unsafe fn read_imm<T>(src: &mut [u8]) -> T {
  let t: T           = mem::uninitialized();
  let t_ptr: *mut u8 = mem::transmute(&t);
  let t_len: uint    = mem::size_of_val(&t);
  copy_nonoverlapping_memory(t_ptr, src.as_mut_ptr() as *const u8, t_len);
  t
}

/// Used to ensure that all the closures are size-aligned properly, to keep
/// all their internal pointers correctly aligned.
fn round_up_to_next(unrounded: uint, target_alignment: uint) -> uint {
  assert!(num::is_power_of_two(target_alignment));
  (unrounded + target_alignment - 1) & !(target_alignment - 1)
}

#[test]
fn test_rounding() {
  assert_eq!(round_up_to_next(0, 4), 0);
  assert_eq!(round_up_to_next(1, 4), 4);
  assert_eq!(round_up_to_next(2, 4), 4);
  assert_eq!(round_up_to_next(3, 4), 4);
  assert_eq!(round_up_to_next(4, 4), 4);
  assert_eq!(round_up_to_next(5, 4), 8);
}

/// A CloQ is a packed queue of unboxed closures. Any unboxed closure may be
/// stored and later removed and called from this array, all without boxing.
///
/// The only allocations performed by this module are those required to keep
/// the underlying buffer appropriately sized, and there is no dependency on
/// libstd.
#[unsafe_no_drop_flag]
pub struct CloQ {
  buf: *mut u8, // raw data storage
  msk: uint,   // capacity (power of two) - 1
  len: uint,   // number of valid bytes in the buffer
  fst: uint,   // index of the first element (next to pop)
}

/// The default bytesize of the buffer.
static DEFAULT_SIZE: uint = 64;

impl CloQ {
  /// Creates a new `CloQ`.
  pub fn new() -> CloQ {
    unsafe {
      CloQ {
        buf: allocate(DEFAULT_SIZE, align()),
        msk: DEFAULT_SIZE - 1,
        len: 0,
        fst: 0,
      }
    }
  }

  /// Returns true `iff` the data in the buffer falls off the rhs and wraps back
  /// around to the lhs.
  fn wraps_around(&self) -> bool {
    self.fst + self.len > self.cap()
  }

  /// Grows the underlying buffer to some power-of-two new size, greater than
  /// the current size.
  ///
  /// This will correctly set `buf`, `msk`, and `fst`, without touching `len`.
  #[cold]
  unsafe fn grow_to(&mut self, target_size: uint) {
    assert!(num::is_power_of_two(target_size));
    assert!(target_size > self.cap());

    let needs_shuffle = self.wraps_around();
    let rhs_len       = self.cap() - self.fst;

    self.buf = reallocate(self.buf, target_size, align(), self.cap());
    self.msk = target_size - 1;

    if needs_shuffle {
      let old_fst = mem::replace(&mut self.fst, target_size - rhs_len);
      // since the new memory is more than twice the size, we know for a fact
      // that there's enough room to copy the old rhs without it overlapping
      // with the new rhs. Therefore, use memcpy instead of memmove.
      copy_nonoverlapping_memory(
        self.buf.offset(self.fst as int),
        self.buf.offset(old_fst as int) as *const u8,
        rhs_len);
    }

    // If it didn't wrap around, it won't now, and we don't need to change `fst`.
  }

  /// Grow the underlying buffer to fit at least `new_size` elements.
  unsafe fn grow_to_fit(&mut self, new_size: uint) {
    assert!(new_size > self.len);
    if new_size > self.cap() {
      self.grow_to(num::next_power_of_two(new_size - 1))
    }
  }

  /// Shrinks the underlying buffer to some power-of-two new size, less than
  /// the current size.
  ///
  /// This will correctly set `buf`, `msk`, and `fst`, without touching `len`.
  #[cold]
  unsafe fn shrink_to(&mut self, target_size: uint) {
    if self.wraps_around() {
      let rhs_len = self.cap() - self.fst;
      let old_fst = mem::replace(&mut self.fst, target_size - rhs_len);
      // The old and new rhs may overlap!
      copy_memory(
        self.buf.offset(self.fst as int),
        self.buf.offset(old_fst as int) as *const u8,
        rhs_len);
    } else {
      // Shuffle all the elements down to the beginning, so we can shrink off of
      // the back. There may be overlap here, so unfortunately we have to
      // memmove.
      copy_memory(
        self.buf,
        self.buf.offset(self.fst as int) as *const u8,
        self.len);
      self.fst = 0;
    }
    self.buf = reallocate(self.buf, target_size, align(), self.cap());
    self.msk = target_size - 1;
    // If it didn't wrap around, it won't now and we don't need to change `fst`.
  }

  /// Shrinks the underlying buffer to not be too big for `new_size` elements.
  unsafe fn shrink_to_fit(&mut self, new_size: uint) {
    // Resize policy: If we're less than or equal to 1/4 full, cut the size of
    // the buffer in half.
    assert!(new_size >= self.len);
    if new_size <= self.cap() >> 2 {
      let want_to_shrink_to = num::next_power_of_two(new_size - 1) << 1;

      if want_to_shrink_to >= DEFAULT_SIZE {
        self.shrink_to(want_to_shrink_to)
      }
    }
  }

  /// The capacity of the underlying buffer.
  fn cap(&self) -> uint {
    self.msk + 1
  }

  /// Take an index that may have walked off the end of an array and wrap it
  /// back into the buffer from the other side.
  fn mask(&self, idx: uint) -> uint {
    idx & self.msk
  }

  // If we don't wrap around, but a push is about to force a wrap around,
  // shuffle the elements in the buffer right until they hit the right hand wall.
  // This ensures there's no dead space in the rhs of the buffer, even though
  // our elements have variable length.
  //
  // This function only makes sense if the buffer does not wrap around.
  // If it does wrap around, then it is an invariant that this operation is
  // unnecessary, as it has already been performed.
  unsafe fn pack_rhs(&mut self) {
    debug_assert!(!self.wraps_around());
    let dist_to_shuffle = self.cap() - (self.fst + self.len);
    copy_memory(
      self.buf.offset((self.fst + dist_to_shuffle) as int),
      self.buf.offset(self.fst as int) as *const u8,
      self.len);
    self.fst += dist_to_shuffle;
  }

  /// Allocate space for at least num_bytes, returning a slice to the allocated,
  /// contiguous space.
  unsafe fn reserve_bytes(&mut self, num_bytes: uint) -> &mut [u8] {
    let new_len = self.len + num_bytes;
    self.grow_to_fit(new_len);
    // If we don't wrap around, but this push will force a wrap around, shuffle
    // the elements right until they hit the right hand wall, then return a
    // slice to the start. This ensures that we don't have a random hole that
    // nothing fits into on the right.
    if !self.wraps_around() && self.fst + self.len + num_bytes > self.cap() {
      self.pack_rhs();

      // slice this is the push that will cause the buffer to wrap, the new
      // elements go at the very front.
      let slice: raw::Slice<u8> =
        raw::Slice {
          data: self.buf as *const u8,
          len:  num_bytes,
        };
      self.len += num_bytes;

      return mem::transmute(slice);
    }

    // At this point, we know two things:
    //
    // 1) There's enough space in the queue for the new bytes (grow_to_fit).
    // 2) There's no random unused bytes at the end of the buffer (pack_rhs).

    let raw_data_ptr = self.buf.offset(self.mask(self.fst + self.len) as int);

    let slice: raw::Slice<u8> =
      raw::Slice {
        data: raw_data_ptr as *const u8,
        len:  num_bytes,
      };
    self.len += num_bytes;
    mem::transmute(slice)
  }

  /// Get a pointer to the code_ptr and raw data of the closure at the head of
  /// the queue. If the queue is empty, `None` is returned.
  unsafe fn view_head(&self) -> Option<(*mut (), &mut [u8])> {
    if self.len == 0 { return None; }

    let raw_code_ptr = self.buf.offset(self.fst as int);
    let raw_len_ptr  = raw_code_ptr.offset(ptr_size() as int);
    let raw_data_ptr = raw_len_ptr.offset(len_size() as int);

    let code_ptr_slice: raw::Slice<u8> =
      raw::Slice {
        data: raw_code_ptr as *const u8,
        len:  ptr_size(),
      };
    let len_slice: raw::Slice<u8> =
      raw::Slice {
        data: raw_len_ptr as *const u8,
        len:  len_size(),
      };

    let code_ptr = read_imm::<*mut ()>(mem::transmute(code_ptr_slice));
    let len  = read_imm::<uint>(mem::transmute(len_slice));

    let data_slice: raw::Slice<u8> =
      raw::Slice {
        data: raw_data_ptr as *const u8,
        len:  len,
      };

    Some((code_ptr, mem::transmute(data_slice)))
  }

  // The below two functions take the length of the closure at the head to avoid
  // having to re-compute it.

  /// Remove the first closure from the queue, optionally shrinking the queue if
  /// necessary.
  ///
  /// The only time you don't want to shrink the queue is when dropping, where
  /// we'll be deallocating the whole buffer at once anyhow at the end.
  unsafe fn pop_head(&mut self, len: uint, shrink: bool) {
    assert!(self.len > 0);

    let byte_len = byte_len(len);
    self.fst = self.mask(self.fst + byte_len);
    self.len -= byte_len;

    if shrink {
      let new_len = self.len;
      self.shrink_to_fit(new_len);
    }
  }

  /// Move the closure that was at the front of the queue to the back of the
  /// queue. No resize will be triggered.
  unsafe fn recycle_head(&mut self, len: uint) {
    assert!(self.len > 0);

    let byte_len = byte_len(len);

    if !self.wraps_around() && self.fst + self.len + byte_len > self.cap() {
      self.pack_rhs();
    }

    // Overlap is possible, if the buffer is really full. Hell, we might even be
    // copying to and from the same location!
    copy_memory(
      self.buf.offset(self.mask(self.fst + self.len) as int),
      self.buf.offset(self.fst as int) as *const u8,
      byte_len);
    self.fst = self.mask(self.fst + byte_len);
  }

  /// Drops the closure at the front of the queue.
  /// This will not remove the closure from the queue itself. If you want to do
  /// that, use `pop_head`.
  unsafe fn drop_head(&mut self) {
    assert!(self.len > 0);
    let raw_call_ptr = self.buf.offset(self.fst as int);
    let raw_data_ptr = self.buf.offset((self.fst + ptr_size() + len_size()) as int);
    let call_ptr_slice: raw::Slice<u8> =
      raw::Slice {
        data: raw_call_ptr as *const u8,
        len:  ptr_size(),
      };
    let code_ptr = read_imm::<*mut ()>(mem::transmute(call_ptr_slice));
    let data_ptr: *mut () = mem::transmute(raw_data_ptr);
    call(data_ptr, code_ptr, true);
  }

  /// Reserves space for closure data, and puts the code_ptr and len in the
  /// space in front of it.
  unsafe fn reserve(&mut self, code_ptr: *mut (), len: uint) -> &mut [u8] {
    let dst = self.reserve_bytes(byte_len(len));

    let (code_dst, rest    ) = dst.mut_split_at(ptr_size());
    let (len_dst,  data_dst) = rest.mut_split_at(len_size());

    serialize_imm(code_dst, code_ptr);
    serialize_imm(len_dst,  len);

    data_dst
  }

  /// Adds a serialized closure to the queue.
  pub fn push<S: Serializer>(&mut self, s: S) {
    unsafe {
      let code_ptr = s.code_ptr();
      let len      = round_up_to_next(s.required_len(), align());
      s.serialize_data(self.reserve(code_ptr, len));
    }
  }

  /// Pushes an unboxed `Fn` closure onto the back of the queue.
  pub fn push_fn<F: Fn<(), StopCondition>>(&mut self, f: F) {
    self.push(FnSerializer::new(f))
  }

  /// Pushes an unboxed `FnMut` closure onto the back of the queue.
  pub fn push_fnmut<F: FnMut<(), StopCondition>>(&mut self, f: F) {
    self.push(FnMutSerializer::new(f))
  }

  /// Pushes an unboxed `FnOnce` closure onto the back of the queue.
  pub fn push_fnonce<F: FnOnce<(), ()>>(&mut self, f: F) {
    self.push(FnOnceSerializer::new(f))
  }

  /// Tries to pop a closure off the queue and run it. Returns `false` iff the
  /// queue is empty and no closure can be run.
  pub fn try_pop_and_run(&mut self) -> bool {
    unsafe {
      let (call_result, len) = {
        let (code_ptr, data_src) =
          match self.view_head() {
            None => return false,
            Some(x) => x,
          };

        let data_len = data_src.len();

        let data_ptr: *mut () = {
          let data_slice: raw::Slice<u8> = mem::transmute(data_src);
          mem::transmute(data_slice.data)
        };

        (call(data_ptr, code_ptr, false), data_len)
      };

      match call_result {
        Stop      => self.pop_head(len, true),
        KeepGoing => self.recycle_head(len),
      }

      true
    }
  }

  /// Is the queue empty?
  pub fn is_empty(&self) -> bool {
    self.len == 0
  }
}

impl Drop for CloQ {
  fn drop(&mut self) {
    unsafe {
      loop {
        let len =
          match self.view_head() {
            None => break,
            Some((_, data)) => data.len()
          };
        self.drop_head();
        self.pop_head(len, false);
      }

      // Need to null check since we don't have a drop flag, and drop may be
      // called multiple times, but will zero the structure when it's done.
      if !self.buf.is_null() {
        deallocate(self.buf, self.cap(), align());
      }
    }
  }
}

#[cfg(test)]
mod test {
  use super::{CloQ,StopCondition,Stop,KeepGoing};
  use std::cell::RefCell;
  use std::rc::Rc;

  #[test]
  fn add_and_run_some_closures() {
    let k: Rc<RefCell<int>> = Rc::new(RefCell::new(0));
    let k1 = k.clone();
    let k2 = k.clone();
    let k3 = k.clone();

    let mut cq = CloQ::new();

    cq.push_fn(|&:| -> StopCondition {
      let mut my_k = k1.try_borrow_mut().unwrap();
      let k = my_k.deref_mut();
      let r = if *k == 1 { Stop } else { KeepGoing };
      *k = 1;
      r
    });

    cq.push_fnmut(|&mut:| -> StopCondition {
      let mut my_k = k2.try_borrow_mut().unwrap();
      let k = my_k.deref_mut();
      *k = 2;
      Stop
    });

    cq.push_fnonce(|:| {
      let mut my_k = k3.try_borrow_mut().unwrap();
      let k = my_k.deref_mut();
      *k = 3;
    });

    assert_eq!(*k.borrow(), 0);
    assert!(cq.try_pop_and_run());
    assert_eq!(*k.borrow(), 1);
    assert!(cq.try_pop_and_run());
    assert_eq!(*k.borrow(), 2);
    assert!(cq.try_pop_and_run());
    assert_eq!(*k.borrow(), 3);
    assert!(cq.try_pop_and_run());
    assert_eq!(*k.borrow(), 1);
    assert!(cq.try_pop_and_run());
    assert_eq!(*k.borrow(), 1);
    assert!(!cq.try_pop_and_run());
  }

  #[test]
  fn leave_a_closure_behind() {
    let k: Rc<int> = Rc::new(3);

    let mut cq = CloQ::new();

    cq.push_fn(|&:| -> StopCondition {
      assert_eq!(*k, 3);
      Stop
    });
  }
}
