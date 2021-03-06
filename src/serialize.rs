//! Closure serialization.
use core::mem;
use core::ops::{Fn,FnMut,FnOnce};
use core::ptr;
use core::raw;
use core::slice::bytes::copy_memory;

use super::{StopCondition,Stop,KeepGoing};

/// Calls the function, and drops it if it's time to stop.
/// If you want to avoid the call and just do the drop, set `just_drop` to true.
unsafe fn my_call_fn<F: Fn<(), StopCondition>>(
    x: *mut F, just_drop: bool) -> StopCondition {
  if just_drop {
    ptr::read(x as *const F);
    return Stop;
  }

  let mut_ref: &mut F = mem::transmute(x);
  let r = mut_ref.call(());

  match r {
    KeepGoing => {},
    Stop => { ptr::read(x as *const F); },
  }

  r
}

/// Calls the function, and drops it if it's time to stop.
///
/// If you want to avoid the call and just do the drop, set `just_drop` to true.
unsafe fn my_call_mut<F: FnMut<(), StopCondition>>(
    x: *mut F, just_drop: bool) -> StopCondition {
  if just_drop {
    ptr::read(x as *const F);
    return Stop;
  }

  let mut_ref: &mut F = mem::transmute(x);
  let r = mut_ref.call_mut(());

  match r {
    KeepGoing => {},
    Stop => { ptr::read(x as *const F); },
  }

  r
}

/// Calls a `FnOnce` closure, and drops it when done.
///
/// If you want to avoid the call and just do the drop, set `just_drop` to true.
///
/// `Stop` is always returned, since a `FnOnce` closure may only be called once.
unsafe fn my_call_once<F: FnOnce<(), ()>>(
    x: *mut F, just_drop: bool)  -> StopCondition {
  if just_drop {
    ptr::read(x as *const F);
    return Stop;
  }

  ptr::read(x as *const F).call_once(());
  Stop
}

/// A struct which can fully encode an unboxed closure -- both the code pointer
/// and the data itself.
///
/// The length and code pointers are not serialized. If you want them, pack it
/// in yourself. This will only serialize the closure's data payload.
pub trait Serializer {
  /// Gets a pointer to the little trampoline which calls the closure, and
  /// possibly drops it if it's time. See: `my_call_fn`, `my_call_mut`, and
  /// `my_call_once`.
  unsafe fn code_ptr(&self) -> *mut ();

  /// How much storage in a u8 array is needed to store the data.
  fn required_len(&self) -> uint;

  /// Serializes the closure's capture data.
  unsafe fn serialize_data(self, dst: &mut [u8]);
}

/// A simple wrapper class used to serialize unboxed closures of type `Fn`.
pub struct FnSerializer<F> {
  f: F,
}

impl<F: Fn<(), StopCondition>> FnSerializer<F> {
  /// Creates a new FnSerializer, taking ownership of the `Fn`.
  #[inline(always)]
  pub fn new(f: F) -> FnSerializer<F> {
    FnSerializer { f: f }
  }
}

impl<F: Fn<(), StopCondition>> Serializer for FnSerializer<F> {
  #[inline(always)]
  fn required_len(&self) -> uint {
    mem::size_of::<F>()
  }

  #[inline(always)]
  unsafe fn code_ptr(&self) -> *mut () {
    mem::transmute(my_call_fn::<F>)
  }

  #[inline]
  unsafe fn serialize_data(self, dst: &mut [u8]) {
    let len = self.required_len();

    let slice_of_self: raw::Slice<u8> =
      raw::Slice {
        data: mem::transmute(&self.f),
        len:  len,
      };

     copy_memory(dst, mem::transmute(slice_of_self));
     mem::forget(self.f);
  }
}

/// Calls a serialized closure, as long as you have the data and code pointers
/// from a `Serializer`.
///
/// Set `just_drop` to true if you want to avoid the call, and just drop the
/// closure.
#[inline(always)]
pub unsafe fn call(
    data: *mut (), code: *mut (), just_drop: bool) -> StopCondition {
  let f: fn(*mut (), bool) -> StopCondition =
    mem::transmute(code);
  f(data, just_drop)
}

/// A simple wrapper class used to serialize unboxed closures of type `FnMut`.
pub struct FnMutSerializer<F> {
  f: F,
}

impl<F: FnMut<(), StopCondition>> FnMutSerializer<F> {
  /// Creates a new `FnMutSerializer`, taking ownership of the `FnMut`.
  #[inline(always)]
  pub fn new(f: F) -> FnMutSerializer<F> {
    FnMutSerializer { f: f }
  }
}

impl<F: FnMut<(), StopCondition>> Serializer for FnMutSerializer<F> {
  #[inline(always)]
  fn required_len(&self) -> uint {
    mem::size_of::<F>()
  }

  #[inline(always)]
  unsafe fn code_ptr(&self) -> *mut () {
    mem::transmute(my_call_mut::<F>)
  }

  #[inline]
  unsafe fn serialize_data(self, dst: &mut [u8]) {
    let len = self.required_len();

    let slice_of_self: raw::Slice<u8> =
      raw::Slice {
        data: mem::transmute(&self.f),
        len:  len,
      };

     copy_memory(dst, mem::transmute(slice_of_self));
     mem::forget(self.f);
  }
}

/// A simple wrapper class used to serialize unboxed closures of type `FnOnce`.
pub struct FnOnceSerializer<F> {
  f: F,
}

impl<F: FnOnce<(), ()>> FnOnceSerializer<F> {
  /// Creates a new `FnOnceSerializer`, taking ownership of the `FnMut`.
  #[inline(always)]
  pub fn new(f: F) -> FnOnceSerializer<F> {
    FnOnceSerializer { f: f }
  }
}

impl<F: FnOnce<(), ()>> Serializer for FnOnceSerializer<F> {
  #[inline(always)]
  fn required_len(&self) -> uint {
    mem::size_of::<F>()
  }

  #[inline(always)]
  unsafe fn code_ptr(&self) -> *mut () {
    mem::transmute(my_call_once::<F>)
  }

  #[inline]
  unsafe fn serialize_data(self, dst: &mut [u8]) {
    let len = self.required_len();

    let slice_of_self: raw::Slice<u8> =
      raw::Slice {
        data: mem::transmute(&self.f),
        len:  len,
      };

     copy_memory(dst, mem::transmute(slice_of_self));
     mem::forget(self.f);
  }
}

#[cfg(test)]
mod test {
  use super::{Serializer,FnSerializer,call};
  use super::super::{Stop,KeepGoing};
  use std::cell::RefCell;
  use std::clone::Clone;
  use std::mem;
  use std::raw;
  use std::rc::Rc;
  use std::vec::Vec;

  #[test]
  fn serialize_a_function() {
    let n = 4u64;

    let c0 = Rc::new(RefCell::new(0u));
    let c1 = c0.clone();

    let f = |&:| {
        let mut c = c1.borrow_mut();
        *c += 1;
        if n == 1 { KeepGoing } else { Stop }
      };

    unsafe {
      let s = FnSerializer::new(f);

      let len = s.required_len();
      let code_ptr = s.code_ptr();

      let mut buf = Vec::from_elem(len, 0u8);

      s.serialize_data(buf.as_mut_slice());
      let buf_slice: raw::Slice<u8> = mem::transmute(buf.as_mut_slice());

      let r = call(mem::transmute(buf_slice.data), code_ptr, false);

      assert_eq!(r, Stop);
      assert_eq!(*c0.borrow(), 1);
    }
  }
}
