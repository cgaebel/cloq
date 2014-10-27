//! A queue of unboxed closures. CloQ for short.
//!
//! This module interacts badly with GC, thanks to all the structs being marked
//! `NoSend`, and having a destructor. I had to add the dreaded
//! `#[unsafe_destructor]` tag to everything. The implications of this are that
//! you must never add a closure which closes over GC'd values to a `CloQ` or
//! `CloSet`, and never build a GC'd `CloQ` or `CloSet`. As a rule of thumb,
//! just don't use GC. It will void your warranty.
#![feature(phase)]
#![feature(unboxed_closures)]
#![feature(unsafe_destructor)]
#![license = "MIT"]
#![no_std]
#![deny(missing_doc)]

// TODO(cgaebel): This does a LOT of memmove instead of memcpy out of necessity,
// so that we can use realloc. It might be better to just suck it up and
// malloc the new buffer, memcpy, then free the old buffer.

// TODO(cgaebel): Ideally we'd use allocators instead of the `alloc` library
// directly.
extern crate alloc;
extern crate core;

#[cfg(test)] #[phase(plugin,link)] extern crate std;
#[cfg(test)] extern crate native;
#[cfg(test)] extern crate test;

use alloc::heap::{allocate,deallocate,reallocate};
use core::cmp;
use core::collections::Collection;
use core::fmt;
use core::intrinsics::{copy_memory,copy_nonoverlapping_memory};
use core::iter::Iterator;
use core::kinds::marker;
use core::mem;
use core::num;
use core::ops::{Fn,FnMut,FnOnce,Drop};
use core::option::{Option,Some,None};
use core::ptr;
use core::ptr::RawPtr;
use core::raw;
use core::slice::{MutableSlice,ImmutableSlice};
use core::str::StrSlice;

use serialize::{Serializer,FnSerializer,FnMutSerializer,FnOnceSerializer,call};

pub mod serialize;

/// A closure can either be removed from the queue, or be moved to the back.
/// The closure itself is allowed to dictate this behavior, so it must return
/// an element of this enum.
pub enum StopCondition {
  /// Do not reschedule the closure at the end of the queue. Drop it.
  Stop,
  /// Reschedule the closure at the end of the queue. Do not drop it.
  KeepGoing,
}

// Can't derive the following since there's no std.

impl cmp::PartialEq for StopCondition {
  #[inline]
  fn eq(&self, other: &StopCondition) -> bool {
    match (*self, *other) {
      (Stop, Stop) => true,
      (KeepGoing, KeepGoing) => true,
      _ => false,
    }
  }
}

impl cmp::Eq for StopCondition {}

impl fmt::Show for StopCondition {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    let to_write =
      match *self {
        Stop => "Stop",
        KeepGoing => "KeepGoing",
      };

    f.write(to_write.as_bytes())
  }
}

/// The number of bytes that need to be allocated in the buffer for a closure
/// with a payload of size `len`.
///
/// We need space for the code ptr, the length of the data buffer, and the
/// buffer itself.
#[inline(always)]
fn byte_len(len: uint) -> uint {
  ptr_size() + len_size() + len
}

/// The size of a pointer on this architecture.
#[inline(always)]
fn ptr_size() -> uint {
  mem::size_of::<*const ()>()
}

/// The size of a buffer length on this architecture.
#[inline(always)]
fn len_size() -> uint {
  mem::size_of::<uint>()
}

/// Keeps each closure ptr-aligned, so that we don't accidentally un-align
/// any of the closure's internal pointers.
#[inline(always)]
fn align() -> uint {
  mem::align_of::<*const ()>()
}

/// Copy some immediate value (ex. u8, u32, etc.) into a byte buffer.
#[inline(always)]
unsafe fn serialize_imm<T>(dst: &mut [u8], t: T) {
  ptr::write(dst.as_mut_ptr() as *mut T, t)
}

/// Copy an immediate value (ex. u8, u32, etc.) out of a byte buffer, and return
/// it.
#[inline(always)]
unsafe fn read_imm<T>(src: &mut [u8]) -> T {
  ptr::read(src.as_ptr() as *const T)
}

#[inline(always)]
unsafe fn raw_slice_of_buf<'a>(buf: *mut u8, len: uint) -> raw::Slice<u8> {
  raw::Slice {
    data: buf as *const u8,
    len:  len,
  }
}

#[inline(always)]
unsafe fn slice_of_buf<'a>(buf: *mut u8, len: uint) -> &'a mut [u8] {
  mem::transmute(raw_slice_of_buf(buf, len))
}

/// Used to ensure that all the closures are size-aligned properly, to keep
/// all their internal pointers correctly aligned.
fn round_up_to_next(unrounded: uint, target_alignment: uint) -> uint {
  (unrounded + target_alignment - 1) & !(target_alignment - 1)
}

#[test]
#[cfg(test)]
fn test_rounding() {
  assert_eq!(round_up_to_next(0, 4), 0);
  assert_eq!(round_up_to_next(1, 4), 4);
  assert_eq!(round_up_to_next(2, 4), 4);
  assert_eq!(round_up_to_next(3, 4), 4);
  assert_eq!(round_up_to_next(4, 4), 4);
  assert_eq!(round_up_to_next(5, 4), 8);
}

/// The default bytesize of the buffers.
static DEFAULT_SIZE: uint = 64;

#[test]
#[cfg(test)]
fn test_default_size() {
  assert!(num::is_power_of_two(DEFAULT_SIZE));
}

/// A `CloSet` is a packed set of unboxed closures.
///
/// This can be used to keep some closuers in limbo before being added to a
/// proper `CloQ`. They cannot be popped or run directly from the `CloSet`, but
/// you can use the `CloSet` for temporary storage of closures you might want to
/// add to a `CloQ` later.
#[unsafe_no_drop_flag]
pub struct CloSet {
  buf:    *mut u8,   // raw data storage
  cap:    uint,      // capacity
  len:    uint,      // the number of valid bytes in the buffer
  nosend: marker::NoSend,
  nosync: marker::NoSync,
}

impl CloSet {
  /// Creates a new `CloSet`.
  pub fn new() -> CloSet {
    CloSet {
      buf: 0 as *mut u8,
      cap: 0,
      len: 0,
      nosend: marker::NoSend,
      nosync: marker::NoSync,
    }
  }

  /// Grows the underlying buffer to some power-of-two new size, greater than
  /// the current size.
  ///
  /// This will correctly set `buf` and `cap`, without touching `len`.
  #[cold]
  unsafe fn grow_to(&mut self, target_size: uint) {
    if self.cap == 0 {
      let new_cap = cmp::max(target_size, DEFAULT_SIZE);
      self.buf = allocate(new_cap, align());
      self.cap = new_cap;
    } else {
      self.buf = reallocate(self.buf, target_size, align(), self.cap);
      self.cap = target_size;
    }
  }

  /// Grow the underlying buffer to fit at least `new_size` elements.
  #[inline]
  unsafe fn grow_to_fit(&mut self, new_size: uint) {
    if new_size > self.cap {
      self.grow_to(num::next_power_of_two(new_size))
    }
  }

  #[inline]
  unsafe fn reserve_bytes(&mut self, num_bytes: uint) -> &mut [u8] {
    let old_len = self.len;
    let new_len = old_len + num_bytes;
    self.grow_to_fit(new_len);
    self.len = new_len;
    slice_of_buf(self.buf.offset(old_len as int), num_bytes)
  }

  /// Reserves space for closure data, and puts the code_ptr and len in the
  /// space in front of it.
  #[inline]
  unsafe fn reserve(&mut self, code_ptr: *mut (), len: uint) -> &mut [u8] {
    let dst = self.reserve_bytes(byte_len(len));

    let (code_dst, rest    ) = dst.split_at_mut(ptr_size());
    let (len_dst,  data_dst) = rest.split_at_mut(len_size());

    serialize_imm(code_dst, code_ptr);
    serialize_imm(len_dst,  len);

    data_dst
  }

  fn iter(&self) -> CloSetIterator {
    CloSetIterator {
      buf: self.buf,
      idx: 0,
      len: self.len,
    }
  }

  /// Adds a serialized closure to the queue.
  #[inline]
  fn push<S: Serializer>(&mut self, s: S) {
    unsafe {
      let code_ptr = s.code_ptr();
      let len      = round_up_to_next(s.required_len(), align());
      s.serialize_data(self.reserve(code_ptr, len));
    }
  }

  /// Pushes an unboxed `Fn` closure into the `CloSet`.
  #[inline]
  pub fn push_fn<F: Fn<(), StopCondition>>(&mut self, f: F) {
    self.push(FnSerializer::new(f))
  }

  /// Pushes an unboxed `FnMut` closure into the `CloSet`.
  #[inline]
  pub fn push_fnmut<F: FnMut<(), StopCondition>>(&mut self, f: F) {
    self.push(FnMutSerializer::new(f))
  }

  /// Pushes an unboxed `FnOnce` closure into the `CloSet`.
  #[inline]
  pub fn push_fnonce<F: FnOnce<(), ()>>(&mut self, f: F) {
    self.push(FnOnceSerializer::new(f))
  }

  /// Pushes a closure in a `CloB` into the `CloSet`. This will take any closure
  /// in the bucket and place it in the set, emptying the bucket.
  ///
  /// Pushing an empty bucket is a no-op.
  pub fn push_b(&mut self, b: &mut CloB) {
    if b.is_empty() { return; }

    unsafe {
      let dst_slice = self.reserve(b.code, b.len);
      let dst: raw::Slice<u8> = mem::transmute(dst_slice);
      copy_nonoverlapping_memory(
        dst.data as *mut   u8,
          b.data as *const u8,
          b.len);
    }

    b.mark_empty();
  }

  /// Returns `true` iff the `CloSet` is empty.
  #[inline(always)]
  pub fn is_empty(&self) -> bool {
    self.len == 0
  }
}

#[unsafe_destructor]
impl Drop for CloSet {
  fn drop(&mut self) {
    unsafe {
      if self.buf.is_null() { return; }

      for (call_ptr, data) in self.iter() {
        call(data.data as *mut (), call_ptr, true);
      }

      deallocate(self.buf, self.cap, align());
    }
  }
}

struct CloSetIterator {
  buf: *mut u8,
  idx: uint,
  len: uint,
}

impl Iterator<(*mut (), raw::Slice<u8>)> for CloSetIterator {
  fn next(&mut self) -> Option<(*mut (), raw::Slice<u8>)> {
    unsafe {
      let idx =
        if self.idx == self.len {
          return None;
        } else {
          self.idx
        };

      let raw_code_ptr = self.buf.offset(idx as int);
      let raw_len_ptr  = raw_code_ptr.offset(ptr_size() as int);
      let raw_data_ptr = raw_len_ptr.offset(len_size() as int);

      let code_ptr: *mut () = read_imm(slice_of_buf(raw_code_ptr, ptr_size()));
      let len:      uint    = read_imm(slice_of_buf(raw_len_ptr,  len_size()));

      self.idx += byte_len(len);

      Some((code_ptr, raw_slice_of_buf(raw_data_ptr, len)))
    }
  }
}

/// A `CloQ` is a packed queue of unboxed closures.
///
/// Any unboxed closure may be and later removed and called from this array,
/// with no boxing in the middle. A corallary to this is that the only
/// allocations performed by this module are those required to keep the
/// underlying buffer appropriately sized.
///
/// There is no dependency on libstd.
#[unsafe_no_drop_flag]
pub struct CloQ {
  buf:    *mut u8, // raw data storage
  msk:    uint,    // capacity (power of two) - 1
  len:    uint,    // number of valid bytes in the buffer
  fst:    uint,    // index of the first element (next to pop)
  nosend: marker::NoSend,
  nosync: marker::NoSync,
}

impl CloQ {
  /// Creates a new `CloQ`.
  pub fn new() -> CloQ {
    CloQ {
      buf:    0 as *mut u8,
      msk:    0,
      len:    0,
      fst:    0,
      nosend: marker::NoSend,
      nosync: marker::NoSync,
    }
  }

  /// Returns true `iff` the data in the buffer falls off the rhs and wraps back
  /// around to the lhs.
  #[inline(always)]
  fn wraps_around(&self) -> bool {
    self.fst + self.len > self.cap()
  }

  /// Grows the underlying buffer to some power-of-two new size, greater than
  /// the current size.
  ///
  /// This will correctly set `buf`, `msk`, and `fst`, without touching `len`.
  #[cold]
  unsafe fn grow_to(&mut self, target_size: uint) {
    if self.buf.is_null() {
      let new_cap = cmp::max(target_size, DEFAULT_SIZE);
      self.buf = allocate(new_cap, align());
      self.msk = new_cap - 1;
      return;
    }

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
  #[inline]
  unsafe fn grow_to_fit(&mut self, new_size: uint) {
    if self.msk == 0 || new_size > self.cap() {
      self.grow_to(num::next_power_of_two(new_size))
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
  }

  /// Shrinks the underlying buffer to not be too big for `new_size` elements.
  #[inline]
  unsafe fn shrink_to_fit(&mut self, new_size: uint) {
    // Resize policy: If we're less than or equal to 1/4 full, cut the size of
    // the buffer in half.
    if new_size <= self.cap() >> 2 {
      let want_to_shrink_to = num::next_power_of_two(new_size) << 1;

      if want_to_shrink_to >= DEFAULT_SIZE {
        self.shrink_to(want_to_shrink_to)
      }
    }
  }

  /// The capacity of the underlying buffer.
  #[inline(always)]
  fn cap(&self) -> uint {
    self.msk + 1
  }

  /// Take an index that may have walked off the end of an array and wrap it
  /// back into the buffer from the other side.
  #[inline(always)]
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
    let raw_data_ptr =
      // If we don't wrap around, but this push will force a wrap around, shuffle
      // the elements right until they hit the right hand wall, then return a
      // slice to the start. This ensures that we don't have a random hole that
      // nothing fits into on the right.
      if !self.wraps_around() && self.fst + self.len + num_bytes > self.cap() {
        self.pack_rhs();

        // slice this is the push that will cause the buffer to wrap, the new
        // elements go at the very front.
        self.buf
      } else {
        // At this point, we know two things:
        //
        // 1) There's enough space in the queue for the new bytes (grow_to_fit).
        // 2) There's no random unused bytes at the end of the buffer (pack_rhs).
        self.buf.offset(self.mask(self.fst + self.len) as int)
      };

    self.len += num_bytes;
    slice_of_buf(raw_data_ptr, num_bytes)
  }

  /// Get a pointer to the code_ptr and raw data of the closure at the head of
  /// the queue. If the queue is empty, `None` is returned.
  #[inline]
  unsafe fn view_head(&self) -> Option<(*mut (), &mut [u8])> {
    if self.len == 0 { return None; }

    let raw_code_ptr = self.buf.offset(self.fst as int);
    let raw_len_ptr  = raw_code_ptr.offset(ptr_size() as int);
    let raw_data_ptr = raw_len_ptr.offset(len_size() as int);

    let code_ptr: *mut () = read_imm(slice_of_buf(raw_code_ptr, ptr_size()));
    let len:      uint    = read_imm(slice_of_buf(raw_len_ptr,  len_size()));

    Some((code_ptr, slice_of_buf(raw_data_ptr, len)))
  }

  // The below two functions take the length of the closure at the head to avoid
  // having to re-compute it.

  /// Remove the first closure from the queue, optionally shrinking the queue if
  /// necessary.
  ///
  /// The only time you don't want to shrink the queue is when dropping, where
  /// we'll be deallocating the whole buffer at once anyhow at the end.
  #[inline]
  unsafe fn pop_head(&mut self, len: uint, shrink: bool) {
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
    let raw_call_ptr = self.buf.offset(self.fst as int);
    let raw_data_ptr = self.buf.offset((self.fst + ptr_size() + len_size()) as int);
    let code_ptr: *mut () = read_imm(slice_of_buf(raw_call_ptr, ptr_size()));
    let data_ptr: *mut () = raw_data_ptr as *mut ();
    call(data_ptr, code_ptr, true);
  }

  /// Reserves space for closure data, and puts the code_ptr and len in the
  /// space in front of it.
  #[inline]
  unsafe fn reserve(&mut self, code_ptr: *mut (), len: uint) -> &mut [u8] {
    let dst = self.reserve_bytes(byte_len(len));

    let (code_dst, rest    ) = dst.split_at_mut(ptr_size());
    let (len_dst,  data_dst) = rest.split_at_mut(len_size());

    serialize_imm(code_dst, code_ptr);
    serialize_imm(len_dst,  len);

    data_dst
  }

  /// Adds a serialized closure to the queue.
  #[inline]
  fn push<S: Serializer>(&mut self, s: S) {
    unsafe {
      let code_ptr = s.code_ptr();
      let len      = round_up_to_next(s.required_len(), align());
      s.serialize_data(self.reserve(code_ptr, len));
    }
  }

  /// Pushes an unboxed `Fn` closure onto the back of the queue.
  #[inline]
  pub fn push_fn<F: Fn<(), StopCondition>>(&mut self, f: F) {
    self.push(FnSerializer::new(f))
  }

  /// Pushes an unboxed `FnMut` closure onto the back of the queue.
  #[inline]
  pub fn push_fnmut<F: FnMut<(), StopCondition>>(&mut self, f: F) {
    self.push(FnMutSerializer::new(f))
  }

  /// Pushes an unboxed `FnOnce` closure onto the back of the queue.
  #[inline]
  pub fn push_fnonce<F: FnOnce<(), ()>>(&mut self, f: F) {
    self.push(FnOnceSerializer::new(f))
  }

  /// Pushes all the closures ever added to a `CloSet` into the `CloQ`.
  ///
  /// The order in which closures are added into the `CloQ` will be the same
  /// as the order they were added into the `CloSet`.
  pub fn push_set(&mut self, s: CloSet) {
    unsafe {
      let dst: raw::Slice<u8> = mem::transmute(self.reserve_bytes(s.len));
      let dst = dst.data as *mut   u8;
      let src = s.buf    as *const u8;
      copy_nonoverlapping_memory(dst, src, s.len);
      deallocate(s.buf, s.cap, align());
      mem::forget(s);
    }
  }

  /// Pushes all the closures ever added to a `CloQ` into another `CloQ`.
  ///
  /// The order in which the the closures are added to the current CloQ will be
  /// the same as the order they were added to the original `CloQ`.
  pub fn push_q(&mut self, q: CloQ) {
    unsafe {
      let dst: raw::Slice<u8> = mem::transmute(self.reserve_bytes(q.len));
      let dst = dst.data as *mut u8;

      if q.wraps_around() {
        let rhs_len = q.cap() - q.fst;
        let lhs_len = q.len - rhs_len;
        copy_nonoverlapping_memory(dst, q.buf.offset(q.fst as int) as *const u8, rhs_len);
        copy_nonoverlapping_memory(dst.offset(rhs_len as int), q.buf as *const u8, lhs_len);
      } else {
        copy_nonoverlapping_memory(dst, q.buf.offset(q.fst as int) as *const u8, q.len);
      }

      deallocate(q.buf, q.cap(), align());
      mem::forget(q);
    }
  }

  /// Pushes a closure in a `CloB` into the `CloQ`. This will take any closure
  /// in the bucket and place it in the queue, emptying the bucket.
  ///
  /// Pushing an empty bucket is a no-op.
  pub fn push_b(&mut self, b: &mut CloB) {
    if b.is_empty() { return; }

    unsafe {
      let dst_slice = self.reserve(b.code, b.len);
      let dst: raw::Slice<u8> = mem::transmute(dst_slice);
      copy_nonoverlapping_memory(
        dst.data as *mut   u8,
          b.data as *const u8,
          b.len);
    }

    b.mark_empty();
  }

  /// Tries to pop a closure off the queue and run it. Returns `false` iff the
  /// queue is empty and no closure can be run.
  ///
  /// If the closure returns `KeepGoing`, it will be pushed back onto the
  /// end of the queue after it's run.
  #[inline]
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
          data_slice.data as *mut ()
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

  /// Returns `true` iff the `CloQ` is empty.
  #[inline]
  pub fn is_empty(&self) -> bool {
    self.len == 0
  }
}

#[unsafe_destructor]
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

/// A `CloB` is a "closure bucket". It can hold either no closure, or one
/// closure.
///
/// A `CloB` will never shrink its backing store for closure data. This is done
/// for efficiency, but may or may not lead to memory leaks in your application.
///
/// The primary use case for a `CloB` is temporary storage when popping out of
/// a `CloQ`, so that the closure that was just popped may push into the queue
/// it was just popped out of, as it runs.
#[unsafe_no_drop_flag]
pub struct CloB {
  code: *mut (),
  data: *mut u8,
  len:  uint,
  cap:  uint,
}

impl CloB {
  /// Creates a new closure bucket (or `CloB`, for short).
  pub fn new() -> CloB {
    CloB {
      code: 0 as *mut (),
      data: 0 as *mut u8,
      len:  0,
      cap:  0,
    }
  }

  /// Returns `true` iff the `CloB` is not currently holding a closure.
  #[inline(always)]
  pub fn is_empty(&self) -> bool {
    self.code.is_null()
  }

  /// Returns `true` iff the `CloB` is currently holding a closure.
  #[inline(always)]
  pub fn is_full(&self) -> bool {
    !self.is_empty()
  }

  #[inline]
  fn mark_empty(&mut self) {
    self.code = 0 as *mut ();
  }

  /// Note: Be very careful when using this. The data contents are thrown away.
  /// If you want to keep them around for whatever reason, consider writing a
  /// similar function that uses realloc.
  #[cold]
  unsafe fn grow_to(&mut self, len: uint) {
    deallocate(self.data, self.cap, align());
    self.data = allocate(len, align());
    self.cap = len;
  }

  #[inline]
  unsafe fn grow_to_fit(&mut self, len: uint) {
    if len > self.cap {
      self.grow_to(len);
    }
  }

  #[inline]
  fn fill(&mut self, code: *mut (), data: *const u8, len: uint) {
    unsafe {
      self.destroy_contents();
      self.code = code;
      self.grow_to_fit(len);
      self.len  = len;
      copy_nonoverlapping_memory(self.data, data, len);
    }
  }

  /// Fills a `CloB` by popping the first closure out of a `CloQ` and placing it
  /// in the bucket.
  ///
  /// If the bucket was filled when this function was called, the closure
  /// filling it will be destroyed safely. The closure that was just popped out
  /// of the `CloQ` will take its place.
  #[inline]
  pub fn fill_from(&mut self, cloq: &mut CloQ) {
    unsafe {
      let len =
        match cloq.view_head() {
          None => return,
          Some((call_ptr, data_slice)) => {
            let raw_slice: raw::Slice<u8> = mem::transmute(data_slice);
            self.fill(call_ptr, raw_slice.data, raw_slice.len);
            raw_slice.len
          }
        };

      cloq.pop_head(len, true);
    }
  }

  /// Attempts to run the closure in the `CloB`.
  ///
  /// If the bucket is empty, `None` will be returned.
  /// Otherwise, `Some(the return value of the closure)` will be returned.
  ///
  /// If the closure returned `Stop`, the bucket will be empty at the end of
  /// this function. If the closure returned `KeepGoing`, the bucket will be
  /// full.
  #[inline(always)]
  pub fn try_pop_and_run(&mut self) -> Option<StopCondition> {
    if self.is_empty() { return None; }

    unsafe {
      let r = call(self.data as *mut (), self.code as *mut (), false);
      match r {
        KeepGoing => {}
        Stop => {
          self.mark_empty();
        }
      }

      Some(r)
    }
  }

  #[inline]
  fn destroy_contents(&mut self) {
    if self.is_empty() { return; }

    unsafe {
      call(self.data as *mut (), self.code as *mut (), true);
      self.mark_empty();
    }
  }
}

impl Drop for CloB {
  fn drop(&mut self) {
    if self.data.is_null() { return; }
    unsafe {
      self.destroy_contents();
      deallocate(self.data, self.cap, align());
      self.data = 0 as *mut u8;
    }
  }
}

// Tests are split out into a seperate module so that we only depend on libstd
// for testing.
#[cfg(test)]
mod my_test {
  use super::{CloQ,CloSet,CloB,StopCondition,Stop,KeepGoing};
  use std::clone::Clone;
  use std::cell::RefCell;
  use std::ops::DerefMut;
  use std::option::Some;
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

  #[test]
  fn use_a_closet() {
    let mut closet = CloSet::new();

    let k: Rc<RefCell<int>> = Rc::new(RefCell::new(0));
    let k1 = k.clone();
    let k2 = k.clone();
    let k3 = k.clone();
    let k4 = k.clone();

    closet.push_fn(|&:| -> StopCondition {
      let mut my_k = k1.try_borrow_mut().unwrap();
      let k = my_k.deref_mut();
      let r = if *k == 1 { Stop } else { KeepGoing };
      *k = 1;
      r
    });

    closet.push_fnmut(|&mut:| -> StopCondition {
      let mut my_k = k2.try_borrow_mut().unwrap();
      let k = my_k.deref_mut();
      *k = 2;
      Stop
    });

    closet.push_fnonce(|:| {
      let mut my_k = k3.try_borrow_mut().unwrap();
      let k = my_k.deref_mut();
      *k = 3;
    });

    let mut cq = CloQ::new();

    cq.push_fnonce(|:| {
      let mut my_k = k4.try_borrow_mut().unwrap();
      let k = my_k.deref_mut();
      *k = 10;
    });

    cq.push_set(closet);

    assert_eq!(*k.borrow(), 0);
    assert!(cq.try_pop_and_run());
    assert_eq!(*k.borrow(), 10);
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
  fn something_that_looks_like_a_scheduler() {
    let cloq = Rc::new(RefCell::new(CloQ::new()));
    let cloq1 = cloq.clone();

    let was_run = Rc::new(RefCell::new(false));
    let was_run1 = was_run.clone();

    {
      let mut my_cloq = cloq.try_borrow_mut().unwrap();
      my_cloq.push_fnonce(|:| {
        let mut my_cloq = cloq1.try_borrow_mut().unwrap();
        my_cloq.deref_mut().push_fnonce(|:| {
          let mut my_was_run = was_run1.try_borrow_mut().unwrap();
          *my_was_run.deref_mut() = true;
        });
      });
    }

    let mut clob = CloB::new();
    assert!(clob.is_empty());

    let mut loops = 0u;

    loop {
      loops += 1;

      {
        let mut my_cloq = cloq.try_borrow_mut().unwrap();
        if my_cloq.is_empty() { break; }
        clob.fill_from(my_cloq.deref_mut());
      }

      assert!(clob.is_full());
      assert_eq!(clob.try_pop_and_run(), Some(Stop));
      assert!(clob.is_empty());
    }

    assert_eq!(loops, 3);
    assert!(*was_run.borrow_mut() == true);
  }
}

#[cfg(test)]
mod bench {
  use test::Bencher;
  use super::{CloQ,StopCondition,Stop};
  use std::iter::range;

  #[bench]
  fn push_3(b: &mut Bencher) {
    let mut cq = CloQ::new();
    // Uhh this can grow without bound if the bencher wants it to. Oh well.
    // Hasn't been a problem yet!
    b.iter(|| {
      cq.push_fn(|&:| -> StopCondition {
        Stop
      });

      cq.push_fnmut(|&mut:| -> StopCondition {
        Stop
      });

      cq.push_fnonce(|:| {
      });
    });
  }

  #[bench]
  fn rotate_once(b: &mut Bencher) {
    let mut cq = CloQ::new();

    // add a few KB of closures to try and throw things out of cache.
    for _ in range(0i, 10*1024) {
      cq.push_fn(|&:| -> StopCondition { Stop });
    }

    b.iter(|| {
      cq.push_fn(|&:| -> StopCondition { Stop });
      assert!(cq.try_pop_and_run());
    });
  }
}
