//! A queue of unboxed closures. CloQ for short.
#![feature(unboxed_closures)]
#![deny(missing_doc)]
// TODO(cgaebel): Remove this. This is just for while I'm building the damn
// thing.
#![allow(dead_code)]

use std::mem;
use std::ptr;
use std::raw;

use serialize::{Serializer,FnSerializer,FnMutSerializer,FnOnceSerializer,call};

mod serialize;

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

pub struct CloQ {
  buf: Vec<u8>,
}

impl CloQ {
  pub fn new() -> CloQ {
    CloQ {
      buf: Vec::new(),
    }
  }

  fn reserve_bytes(&mut self, num_bytes: uint) -> &mut [u8] {
    self.buf.as_mut_slice()
  }

  fn view_head(&mut self) -> Option<(*mut (), &mut [u8])> {
    None
  }

  fn recycle_head(&mut self) {
  }

  fn reserve(&mut self, code_ptr: *mut (), len: uint) -> &mut [u8] {
    let ptr_size = mem::size_of_val(&code_ptr);
    let dst = self.reserve_bytes(ptr_size + len);
    let (code_dst, data_dst) = dst.mut_split_at(ptr_size);

    code_dst.copy_memory(mem::transmute(Slice {
      data: mem::transmute(&code_ptr),
      len:  ptr_size,
    }));

    data_dst
  }

  pub fn push_fn<F: Fn<(), StopCondition>>(&mut self, f: F) {
    unsafe {
      let s = FnSerializer::new(f);
      let code_ptr = s.code_ptr();
      let len = s.required_len();
      s.serialize_data(self.reserve(code_ptr, len));
    }
  }

  pub fn push_fnmut<F: FnMut<(), StopCondition>>(&mut self, f: F) {
    unsafe {
      let s = FnMutSerializer::new(f);
      let code_ptr = s.code_ptr();
      let len = s.required_len();
      s.serialize_data(self.reserve(code_ptr, len));
    }
  }

  pub fn push_fnonce<F: FnOnce<(), StopCondition>>(&mut self, f: F) {
    unsafe {
      let s = FnOnceSerializer::new(f);
      let code_ptr = s.code_ptr();
      let len = s.required_len();
      s.serialize_data(self.reserve(code_ptr, len));
    }
  }

  /// Tries to pop a closure off the queue and run it. Returns `false` iff the
  /// queue is empty and no closure can be run.
  pub fn try_pop_and_run(&mut self) -> bool {
    unsafe {
      let (code_ptr, data_src) =
        match self.view_head() {
          None => return false,
          Some(x) => x,
        };

      let data_ptr: *mut () = {
        let data_slice: Slice = mem::transmute(data_src);
        mem::transmute(data_slice.data)
      };

      match call(data_ptr, code_ptr) {
        Stop => {},
        KeepGoing => {
          self.recycle_head();
        },
      }

      true
    }
  }
}
