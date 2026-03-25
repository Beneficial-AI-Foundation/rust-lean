
-- Experimental lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/lean
import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

structure Merkle_root_rs.Digest where
  _0 : (RustArray u32 8)

instance Merkle_root_rs.Impl.AssociatedTypes :
  Core.Clone.Clone.AssociatedTypes Merkle_root_rs.Digest
  where

instance Merkle_root_rs.Impl : Core.Clone.Clone Merkle_root_rs.Digest where

instance Merkle_root_rs.Impl_1.AssociatedTypes :
  Core.Marker.Copy.AssociatedTypes Merkle_root_rs.Digest
  where

instance Merkle_root_rs.Impl_1 : Core.Marker.Copy Merkle_root_rs.Digest where

instance Merkle_root_rs.Impl_2.AssociatedTypes :
  Core.Marker.StructuralPartialEq.AssociatedTypes Merkle_root_rs.Digest
  where

instance Merkle_root_rs.Impl_2 :
  Core.Marker.StructuralPartialEq Merkle_root_rs.Digest
  where

instance Merkle_root_rs.Impl_3.AssociatedTypes :
  Core.Cmp.PartialEq.AssociatedTypes Merkle_root_rs.Digest Merkle_root_rs.Digest
  where

instance Merkle_root_rs.Impl_3 :
  Core.Cmp.PartialEq Merkle_root_rs.Digest Merkle_root_rs.Digest
  where

instance Merkle_root_rs.Impl_4.AssociatedTypes :
  Core.Cmp.Eq.AssociatedTypes Merkle_root_rs.Digest
  where

instance Merkle_root_rs.Impl_4 : Core.Cmp.Eq Merkle_root_rs.Digest where

instance Merkle_root_rs.Impl_5.AssociatedTypes :
  Core.Fmt.Debug.AssociatedTypes Merkle_root_rs.Digest
  where

instance Merkle_root_rs.Impl_5 : Core.Fmt.Debug Merkle_root_rs.Digest where

noncomputable def Merkle_root_rs.merkle_root_from_path
  (leaf : Merkle_root_rs.Digest)
  (index : u32)
  (digests : (RustSlice Merkle_root_rs.Digest))
  (hash_pair :
  (Merkle_root_rs.Digest
  -> Merkle_root_rs.Digest
  -> RustM Merkle_root_rs.Digest))
  : RustM Merkle_root_rs.Digest
  := do
  let cur : Merkle_root_rs.Digest := leaf;
  let cur_index : u32 := index;
  let ⟨cur, cur_index⟩ ←
    (Core.Iter.Traits.Iterator.Iterator.fold
      (← (Core.Iter.Traits.Collect.IntoIterator.into_iter
        (RustSlice Merkle_root_rs.Digest) digests))
      (Rust_primitives.Hax.Tuple2.mk cur cur_index)
      (fun ⟨cur, cur_index⟩ sibling => (do
        let cur : Merkle_root_rs.Digest ←
          if
          (← (Rust_primitives.Hax.Machine_int.eq
            (← (cur_index &&&? (1 : u32)))
            (0 : u32))) then
            (hash_pair cur sibling)
          else
            (hash_pair sibling cur);
        let cur_index : u32 ← (cur_index >>>? (1 : i32));
        (pure (Rust_primitives.Hax.Tuple2.mk cur cur_index)) : RustM
        (Rust_primitives.Hax.Tuple2 Merkle_root_rs.Digest u32))));
  (pure cur)

noncomputable def Merkle_root_rs.merkle_verify_from_path
  (leaf : Merkle_root_rs.Digest)
  (index : u32)
  (digests : (RustSlice Merkle_root_rs.Digest))
  (expected_root : Merkle_root_rs.Digest)
  (hash_pair :
  (Merkle_root_rs.Digest
  -> Merkle_root_rs.Digest
  -> RustM Merkle_root_rs.Digest))
  : RustM Bool
  := do
  (Core.Cmp.PartialEq.eq
    Merkle_root_rs.Digest
    Merkle_root_rs.Digest
    (← (Merkle_root_rs.merkle_root_from_path leaf index digests hash_pair))
    expected_root)
