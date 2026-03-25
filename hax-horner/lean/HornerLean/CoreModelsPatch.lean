import Hax

open Rust_primitives.Hax

namespace Core_models.Slice.Impl

def is_empty (α : Type) (a : Array α) : RustM Bool := do
  let n ← Core_models.Slice.Impl.len α a
  Rust_primitives.Hax.Machine_int.eq n (0 : usize)

end Core_models.Slice.Impl
