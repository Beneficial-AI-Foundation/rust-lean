import Hax.Lib
import Hax.Rust_primitives

open Rust_primitives.Hax

namespace Core

/- ------------------------------------------------------------
   AssociatedTypes stubs expected by extracted code
   ------------------------------------------------------------ -/

namespace Clone
namespace Clone
class AssociatedTypes (Self : Type) : Type where
end Clone
end Clone

namespace Marker

class Copy (Self : Type) : Type where

namespace Copy
class AssociatedTypes (Self : Type) : Type where
end Copy

class StructuralPartialEq (Self : Type) : Type where

namespace StructuralPartialEq
class AssociatedTypes (Self : Type) : Type where
end StructuralPartialEq

end Marker

namespace Fmt

class Debug (Self : Type) : Type where

namespace Debug
class AssociatedTypes (Self : Type) : Type where
end Debug

end Fmt

/- ------------------------------------------------------------
   Core.Cmp (minimal, shape compatible with hax output)
   ------------------------------------------------------------ -/

namespace Cmp

/-- Marker trait: no fields, so extracted empty instances typecheck. -/
class PartialEq (A B : Type) : Type where

namespace PartialEq
class AssociatedTypes (A B : Type) : Type where

/-- Uninterpreted equality operator used by extracted code. -/
opaque eq (A B : Type) (a : A) (b : B) : RustM Bool

@[simp] axiom eq_refl (A : Type) (a : A) : eq A A a a = pure true
end PartialEq

class Eq (Self : Type) : Type where
namespace Eq
class AssociatedTypes (Self : Type) : Type where
end Eq

end Cmp

/- ------------------------------------------------------------
   Core.Iter (minimal, uninterpreted; shape compatible with hax output)
   ------------------------------------------------------------ -/

namespace Iter
namespace Traits

namespace Iterator

universe u v

/-- This is the type `Core.Iter.Traits.Iterator.Iterator`. -/
structure Iterator (Item : Type u) where
  dummy : Unit := ()

/--
This is the function `Core.Iter.Traits.Iterator.Iterator.fold`.
Important: define it as `Iterator.fold`, not just `fold`.
-/
def Iterator.fold {Item : Type u} {Acc : Type v} :
  Iterator Item →
  Acc →
  (Acc → Item → RustM Acc) →
  RustM Acc := by
  -- Stub for now (we only need typechecking)
  sorry

end Iterator

namespace Collect
namespace IntoIterator

universe u v

/--
This matches the call shape in extracted code:
`Core.Iter.Traits.Collect.IntoIterator.into_iter (RustSlice α) digests`

So `into_iter` takes the *container type* explicitly first.
-/
def into_iter (C : Type u) {Item : Type v} :
  C → RustM (Core.Iter.Traits.Iterator.Iterator Item) := by
  -- Stub for now (we only need typechecking)
  sorry

end IntoIterator
end Collect

end Traits
end Iter


end Core
