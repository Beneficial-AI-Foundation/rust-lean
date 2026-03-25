
-- Experimental lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/lean
import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import Mersenne31.HaxPatch
open HaxPatch
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false


namespace mersenne31.unimplemented

--  Dummy `Iterator` placeholder trait
class Iterator.AssociatedTypes (Self : Type) where
  Item : Type

attribute [reducible] Iterator.AssociatedTypes.Item

abbrev Iterator.Item :=
  Iterator.AssociatedTypes.Item

class Iterator (Self : Type)
  [associatedTypes : outParam (Iterator.AssociatedTypes (Self : Type))]
  where

--  Copied `Sum` trait
class Sum.AssociatedTypes (Self : Type) (A : Type) where

class Sum (Self : Type) (A : Type)
  [associatedTypes : outParam (Sum.AssociatedTypes (Self : Type) (A : Type))]
  where
  sum (Self) (A)
    (I : Type)
    [trait_constr_sum_associated_type_i1 : Iterator.AssociatedTypes I]
    [trait_constr_sum_i1 : Iterator
      I
      (associatedTypes := {
        show Iterator.AssociatedTypes I
        by infer_instance
        with Item := A})] :
    (I -> RustM Self)

--  Copied `Product` trait
class Product.AssociatedTypes (Self : Type) (A : Type) where

class Product (Self : Type) (A : Type)
  [associatedTypes : outParam (Product.AssociatedTypes (Self : Type) (A :
      Type))]
  where
  product (Self) (A)
    (I : Type)
    [trait_constr_product_associated_type_i1 : Iterator.AssociatedTypes I]
    [trait_constr_product_i1 : Iterator
      I
      (associatedTypes := {
        show Iterator.AssociatedTypes I
        by infer_instance
        with Item := A})] :
    (I -> RustM Self)

end mersenne31.unimplemented


namespace mersenne31.mersenne31

--  The Mersenne31 prime
def P : u32 :=
  RustM.of_isOk (do ((← ((1 : u32) <<<? (31 : i32))) -? (1 : u32))) (by rfl)

--  The Mersenne31 prime as u64 to avoid casting `P`
def P64 : u64 :=
  RustM.of_isOk (do ((← ((1 : u64) <<<? (31 : i32))) -? (1 : u64))) (by rfl)

--  The prime field `F_p` where `p = 2^31 - 1`.
structure Mersenne31 where
  value : u32

@[instance] opaque Impl_14.AssociatedTypes :
  core_models.clone.Clone.AssociatedTypes Mersenne31 :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_14 :
  core_models.clone.Clone Mersenne31 :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_13.AssociatedTypes :
  core_models.marker.Copy.AssociatedTypes Mersenne31 :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_13 :
  core_models.marker.Copy Mersenne31 :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_15.AssociatedTypes :
  core_models.default.Default.AssociatedTypes Mersenne31 :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_15 :
  core_models.default.Default Mersenne31 :=
  by constructor <;> exact Inhabited.default

--  Create a new field element from any `u32`.
-- 
--  Any `u32` value is accepted and automatically reduced modulo P.
@[spec]
def Impl.new (value : u32) : RustM Mersenne31 := do
  (pure (Mersenne31.mk (value := (← (value %? P)))))

--  Create a field element from a value assumed to be < 2^31.
-- 
--  # Safety
--  The element must lie in the range: `[0, 2^31 - 1]`.
@[spec]
def Impl.new_reduced (value : u32) : RustM Mersenne31 := do
  let _ ← (hax_lib.assert (← ((← (value >>>? (31 : i32))) ==? (0 : u32))));
  (pure (Mersenne31.mk (value := value)))

--  Convert a u32 element into a Mersenne31 element.
-- 
--  Returns `None` if the element does not lie in the range: `[0, 2^31 - 1]`.
@[spec]
def Impl.new_checked (value : u32) :
    RustM (core_models.option.Option Mersenne31) := do
  if (← ((← (value >>>? (31 : i32))) ==? (0 : u32))) then do
    (pure (core_models.option.Option.Some (Mersenne31.mk (value := value))))
  else do
    (pure core_models.option.Option.None)

--  NOTE: Placeholder dummy impl
@[reducible] instance Impl_11.AssociatedTypes :
  mersenne31.unimplemented.Sum.AssociatedTypes Mersenne31 Mersenne31
  where

instance Impl_11 : mersenne31.unimplemented.Sum Mersenne31 Mersenne31 where
  sum :=
    fun
      (I : Type)
      [trait_constr_sum_associated_type_i0 :
        mersenne31.unimplemented.Iterator.AssociatedTypes
        I]
      [trait_constr_sum_i0 : mersenne31.unimplemented.Iterator
        I
        (associatedTypes := {
          show mersenne31.unimplemented.Iterator.AssociatedTypes I
          by infer_instance
          with Item := Mersenne31})] (iter : I) => do
    (Impl.new (0 : u32))

--  NOTE: Placeholder dummy impl. Unclear atm where the source is.
@[reducible] instance Impl_12.AssociatedTypes :
  mersenne31.unimplemented.Product.AssociatedTypes Mersenne31 Mersenne31
  where

instance Impl_12 : mersenne31.unimplemented.Product Mersenne31 Mersenne31 where
  product :=
    fun
      (I : Type)
      [trait_constr_product_associated_type_i0 :
        mersenne31.unimplemented.Iterator.AssociatedTypes
        I]
      [trait_constr_product_i0 : mersenne31.unimplemented.Iterator
        I
        (associatedTypes := {
          show mersenne31.unimplemented.Iterator.AssociatedTypes I
          by infer_instance
          with Item := Mersenne31})] (iter : I) => do
    (Impl.new (0 : u32))

end mersenne31.mersenne31


namespace mersenne31.koalabear

structure KoalaBearParameters where
  -- no fields

@[instance] opaque Impl_2.AssociatedTypes :
  core_models.clone.Clone.AssociatedTypes KoalaBearParameters :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_2 :
  core_models.clone.Clone KoalaBearParameters :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_1.AssociatedTypes :
  core_models.marker.Copy.AssociatedTypes KoalaBearParameters :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_1 :
  core_models.marker.Copy KoalaBearParameters :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_3.AssociatedTypes :
  core_models.default.Default.AssociatedTypes KoalaBearParameters :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_3 :
  core_models.default.Default KoalaBearParameters :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_4.AssociatedTypes :
  core_models.fmt.Debug.AssociatedTypes KoalaBearParameters :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_4 :
  core_models.fmt.Debug KoalaBearParameters :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_6.AssociatedTypes :
  core_models.hash.Hash.AssociatedTypes KoalaBearParameters :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_6 :
  core_models.hash.Hash KoalaBearParameters :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_7.AssociatedTypes :
  core_models.marker.StructuralPartialEq.AssociatedTypes KoalaBearParameters :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_7 :
  core_models.marker.StructuralPartialEq KoalaBearParameters :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_8.AssociatedTypes :
  core_models.cmp.PartialEq.AssociatedTypes
  KoalaBearParameters
  KoalaBearParameters :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_8 :
  core_models.cmp.PartialEq KoalaBearParameters KoalaBearParameters :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_5.AssociatedTypes :
  core_models.cmp.Eq.AssociatedTypes KoalaBearParameters :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_5 :
  core_models.cmp.Eq KoalaBearParameters :=
  by constructor <;> exact Inhabited.default

end mersenne31.koalabear


namespace mersenne31.field

--  NOTE: DUMMY PLACEHOLDER. Missing `PrimeField`
--  A prime field `ℤ/p` with order, `p < 2^64`.
class PrimeField64.AssociatedTypes (Self : Type) where

class PrimeField64 (Self : Type)
  [associatedTypes : outParam (PrimeField64.AssociatedTypes (Self : Type))]
  where
  ORDER_U64 (Self) : u64
  as_canonical_u64 (Self) : (Self -> RustM u64)
  to_unique_u64 (Self) (self : Self) :RustM u64 := do
    (as_canonical_u64 self)

--  NOTE: DUMMY PLACEHOLDER. Missing `PrimeField` and `PrimeField64`
--  NOTE: `PrimeField64` supertrait removed to avoid circularities in the implementation
--  A prime field `ℤ/p` with order `p < 2^32`.
class PrimeField32.AssociatedTypes (Self : Type) where

class PrimeField32 (Self : Type)
  [associatedTypes : outParam (PrimeField32.AssociatedTypes (Self : Type))]
  where
  ORDER_U32 (Self) : u32
  as_canonical_u32 (Self) : (Self -> RustM u32)
  to_unique_u32 (Self) (self : Self) :RustM u32 := do
    (as_canonical_u32 self)

--  NOTE: Removed the equality constraint of associated type for supertraits
class PrimeCharacteristicRing.AssociatedTypes (Self : Type) where
  [trait_constr_PrimeCharacteristicRing_i0 :
  core_models.default.Default.AssociatedTypes
  Self]
  [trait_constr_PrimeCharacteristicRing_i1 :
  core_models.clone.Clone.AssociatedTypes
  Self]
  [trait_constr_PrimeCharacteristicRing_i2 :
  core_models.ops.arith.Add.AssociatedTypes
  Self
  Self]
  [trait_constr_PrimeCharacteristicRing_i3 :
  core_models.ops.arith.AddAssign.AssociatedTypes
  Self
  Self]
  [trait_constr_PrimeCharacteristicRing_i4 :
  core_models.ops.arith.Sub.AssociatedTypes
  Self
  Self]
  [trait_constr_PrimeCharacteristicRing_i5 :
  core_models.ops.arith.SubAssign.AssociatedTypes
  Self
  Self]
  [trait_constr_PrimeCharacteristicRing_i6 :
  core_models.ops.arith.Neg.AssociatedTypes
  Self]
  [trait_constr_PrimeCharacteristicRing_i7 :
  core_models.ops.arith.Mul.AssociatedTypes
  Self
  Self]
  [trait_constr_PrimeCharacteristicRing_i8 :
  core_models.ops.arith.MulAssign.AssociatedTypes
  Self
  Self]
  [trait_constr_PrimeCharacteristicRing_i9 :
  mersenne31.unimplemented.Sum.AssociatedTypes
  Self
  Self]
  [trait_constr_PrimeCharacteristicRing_i10 :
  mersenne31.unimplemented.Product.AssociatedTypes
  Self
  Self]
  PrimeSubfield : Type

attribute [instance_reducible, instance]
  PrimeCharacteristicRing.AssociatedTypes.trait_constr_PrimeCharacteristicRing_i0

attribute [instance_reducible, instance]
  PrimeCharacteristicRing.AssociatedTypes.trait_constr_PrimeCharacteristicRing_i1

attribute [instance_reducible, instance]
  PrimeCharacteristicRing.AssociatedTypes.trait_constr_PrimeCharacteristicRing_i2

attribute [instance_reducible, instance]
  PrimeCharacteristicRing.AssociatedTypes.trait_constr_PrimeCharacteristicRing_i3

attribute [instance_reducible, instance]
  PrimeCharacteristicRing.AssociatedTypes.trait_constr_PrimeCharacteristicRing_i4

attribute [instance_reducible, instance]
  PrimeCharacteristicRing.AssociatedTypes.trait_constr_PrimeCharacteristicRing_i5

attribute [instance_reducible, instance]
  PrimeCharacteristicRing.AssociatedTypes.trait_constr_PrimeCharacteristicRing_i6

attribute [instance_reducible, instance]
  PrimeCharacteristicRing.AssociatedTypes.trait_constr_PrimeCharacteristicRing_i7

attribute [instance_reducible, instance]
  PrimeCharacteristicRing.AssociatedTypes.trait_constr_PrimeCharacteristicRing_i8

attribute [instance_reducible, instance]
  PrimeCharacteristicRing.AssociatedTypes.trait_constr_PrimeCharacteristicRing_i9

attribute [instance_reducible, instance]
  PrimeCharacteristicRing.AssociatedTypes.trait_constr_PrimeCharacteristicRing_i10

attribute [reducible] PrimeCharacteristicRing.AssociatedTypes.PrimeSubfield

abbrev PrimeCharacteristicRing.PrimeSubfield :=
  PrimeCharacteristicRing.AssociatedTypes.PrimeSubfield

class PrimeCharacteristicRing (Self : Type)
  [associatedTypes : outParam (PrimeCharacteristicRing.AssociatedTypes (Self :
      Type))]
  where
  [trait_constr_PrimeCharacteristicRing_i0 : core_models.default.Default Self]
  [trait_constr_PrimeCharacteristicRing_i1 : core_models.clone.Clone Self]
  [trait_constr_PrimeCharacteristicRing_i2 :
  core_models.ops.arith.Add
  Self
  Self]
  [trait_constr_PrimeCharacteristicRing_i3 :
  core_models.ops.arith.AddAssign
  Self
  Self]
  [trait_constr_PrimeCharacteristicRing_i4 :
  core_models.ops.arith.Sub
  Self
  Self]
  [trait_constr_PrimeCharacteristicRing_i5 :
  core_models.ops.arith.SubAssign
  Self
  Self]
  [trait_constr_PrimeCharacteristicRing_i6 : core_models.ops.arith.Neg Self]
  [trait_constr_PrimeCharacteristicRing_i7 :
  core_models.ops.arith.Mul
  Self
  Self]
  [trait_constr_PrimeCharacteristicRing_i8 :
  core_models.ops.arith.MulAssign
  Self
  Self]
  [trait_constr_PrimeCharacteristicRing_i9 :
  mersenne31.unimplemented.Sum
  Self
  Self]
  [trait_constr_PrimeCharacteristicRing_i10 :
  mersenne31.unimplemented.Product
  Self
  Self]
  ZERO (Self) : Self
  ONE (Self) : Self
  TWO (Self) : Self
  NEG_ONE (Self) : Self
  from_prime_subfield (Self) : (associatedTypes.PrimeSubfield -> RustM Self)
  from_bool (Self) (b : Bool) :RustM Self := do
    if b then do
      (pure  ONE)
    else do
      (pure  ZERO)
  double (Self)
    (A : Type)
    [trait_constr_double_associated_type_i1 :
      core_models.clone.Clone.AssociatedTypes
      A]
    [trait_constr_double_i1 : core_models.clone.Clone A ]
    [trait_constr_double_associated_type_i2 :
      core_models.ops.arith.Add.AssociatedTypes
      A
      A]
    [trait_constr_double_i2 : core_models.ops.arith.Add A A ] (a : A) :RustM
    (core_models.ops.arith.Add.Output A A) := do
    (core_models.ops.arith.Add.add
      A
      A
      (← (core_models.clone.Clone.clone A a))
      (← (core_models.clone.Clone.clone A a)))
  halve (Self) (self : Self) :RustM Self := do
    (core_models.clone.Clone.clone Self self)

attribute [instance_reducible, instance]
  PrimeCharacteristicRing.trait_constr_PrimeCharacteristicRing_i0

attribute [instance_reducible, instance]
  PrimeCharacteristicRing.trait_constr_PrimeCharacteristicRing_i1

attribute [instance_reducible, instance]
  PrimeCharacteristicRing.trait_constr_PrimeCharacteristicRing_i2

attribute [instance_reducible, instance]
  PrimeCharacteristicRing.trait_constr_PrimeCharacteristicRing_i3

attribute [instance_reducible, instance]
  PrimeCharacteristicRing.trait_constr_PrimeCharacteristicRing_i4

attribute [instance_reducible, instance]
  PrimeCharacteristicRing.trait_constr_PrimeCharacteristicRing_i5

attribute [instance_reducible, instance]
  PrimeCharacteristicRing.trait_constr_PrimeCharacteristicRing_i6

attribute [instance_reducible, instance]
  PrimeCharacteristicRing.trait_constr_PrimeCharacteristicRing_i7

attribute [instance_reducible, instance]
  PrimeCharacteristicRing.trait_constr_PrimeCharacteristicRing_i8

attribute [instance_reducible, instance]
  PrimeCharacteristicRing.trait_constr_PrimeCharacteristicRing_i9

attribute [instance_reducible, instance]
  PrimeCharacteristicRing.trait_constr_PrimeCharacteristicRing_i10

end mersenne31.field


namespace mersenne31.monty_31

--  MontyParameters contains the prime P along with constants needed to convert elements into and out of MONTY form.
--  The MONTY constant is assumed to be a power of 2.
class MontyParameters.AssociatedTypes (Self : Type) where
  [trait_constr_MontyParameters_i0 :
  core_models.marker.Copy.AssociatedTypes
  Self]
  [trait_constr_MontyParameters_i1 :
  core_models.default.Default.AssociatedTypes
  Self]

attribute [instance_reducible, instance]
  MontyParameters.AssociatedTypes.trait_constr_MontyParameters_i0

attribute [instance_reducible, instance]
  MontyParameters.AssociatedTypes.trait_constr_MontyParameters_i1

class MontyParameters (Self : Type)
  [associatedTypes : outParam (MontyParameters.AssociatedTypes (Self : Type))]
  where
  [trait_constr_MontyParameters_i0 : core_models.marker.Copy Self]
  [trait_constr_MontyParameters_i1 : core_models.default.Default Self]
  PRIME (Self) : u32
  MONTY_BITS (Self) : u32
  MONTY_MU (Self) : u32
  MONTY_MASK (Self) :u32 :=
    RustM.of_isOk
      (do
      (rust_primitives.hax.cast_op
        (← ((← ((1 : u64) <<<? MONTY_BITS))
          -? (1 : u64))) :
        RustM u32))
      (by rfl)

attribute [instance_reducible, instance]
  MontyParameters.trait_constr_MontyParameters_i0

attribute [instance_reducible, instance]
  MontyParameters.trait_constr_MontyParameters_i1

--  Add two integers modulo `P = MP::PRIME`.
-- 
--  Assumes that `P` is less than `2^31` and `a + b <= 2P` for all array pairs `a, b`.
--  If the inputs are not in this range, the result may be incorrect.
--  The result will be in the range `[0, P]` and equal to `(a + b) mod P`.
--  It will be equal to `P` if and only if `a + b = 2P` so provided `a + b < 2P`
--  the result is guaranteed to be less than `P`.
@[spec]
def add
    (MP : Type)
    [trait_constr_add_associated_type_i0 : MontyParameters.AssociatedTypes MP]
    [trait_constr_add_i0 : MontyParameters MP ]
    (lhs : u32)
    (rhs : u32) :
    RustM u32 := do
  let sum : u32 ← (lhs +? rhs);
  let ⟨corr_sum, over⟩ ←
    (core_models.num.Impl_8.overflowing_sub sum (MontyParameters.PRIME MP));
  let sum : u32 ←
    if (← (!? over)) then do
      let sum : u32 := corr_sum;
      (pure sum)
    else do
      (pure sum);
  (pure sum)

--  Subtract two integers modulo `P = MP::PRIME`.
-- 
--  Assumes that `P` is less than `2^31` and `|a - b| <= P` for all array pairs `a, b`.
--  If the inputs are not in this range, the result may be incorrect.
--  The result will be in the range `[0, P]` and equal to `(a - b) mod P`.
--  It will be equal to `P` if and only if `a - b = P` so provided `a - b < P`
--  the result is guaranteed to be less than `P`.
@[spec]
def sub
    (MP : Type)
    [trait_constr_sub_associated_type_i0 : MontyParameters.AssociatedTypes MP]
    [trait_constr_sub_i0 : MontyParameters MP ]
    (lhs : u32)
    (rhs : u32) :
    RustM u32 := do
  let ⟨diff, over⟩ ← (core_models.num.Impl_8.overflowing_sub lhs rhs);
  let corr : u32 ←
    if over then do (pure (MontyParameters.PRIME MP)) else do (pure (0 : u32));
  let diff : u32 ← (core_models.num.Impl_8.wrapping_add diff corr);
  (pure diff)

--  Convert a u32 into MONTY form.
--  There are no constraints on the input.
--  The output will be a u32 in range `[0, P)`.
@[spec]
def to_monty
    (MP : Type)
    [trait_constr_to_monty_associated_type_i0 : MontyParameters.AssociatedTypes
      MP]
    [trait_constr_to_monty_i0 : MontyParameters MP ]
    (x : u32) :
    RustM u32 := do
  (rust_primitives.hax.cast_op
    (← ((← ((← (rust_primitives.hax.cast_op x : RustM u64))
        <<<? (MontyParameters.MONTY_BITS MP)))
      %? (← (rust_primitives.hax.cast_op
        (MontyParameters.PRIME MP) :
        RustM u64)))) :
    RustM u32)

--  Montgomery reduction of a value in `0..P << MONTY_BITS`.
-- 
--  The input must be in `[0, MONTY * P)`.
--  The output will be in `[0, P)`.
@[spec]
def monty_reduce
    (MP : Type)
    [trait_constr_monty_reduce_associated_type_i0 :
      MontyParameters.AssociatedTypes
      MP]
    [trait_constr_monty_reduce_i0 : MontyParameters MP ]
    (x : u64) :
    RustM u32 := do
  let t : u64 ←
    ((← (core_models.num.Impl_9.wrapping_mul
        x
        (← (rust_primitives.hax.cast_op
          (MontyParameters.MONTY_MU MP) :
          RustM u64))))
      &&&? (← (rust_primitives.hax.cast_op
        (MontyParameters.MONTY_MASK MP) :
        RustM u64)));
  let u : u64 ←
    (t
      *? (← (rust_primitives.hax.cast_op
        (MontyParameters.PRIME MP) :
        RustM u64)));
  let ⟨x_sub_u, over⟩ ← (core_models.num.Impl_9.overflowing_sub x u);
  let x_sub_u_hi : u32 ←
    (rust_primitives.hax.cast_op
      (← (x_sub_u >>>? (MontyParameters.MONTY_BITS MP))) :
      RustM u32);
  let corr : u32 ←
    if over then do (pure (MontyParameters.PRIME MP)) else do (pure (0 : u32));
  (core_models.num.Impl_8.wrapping_add x_sub_u_hi corr)

--  Convert a u32 out of MONTY form.
--  There are no constraints on the input.
--  The output will be a u32 in range `[0, P)`.
@[spec]
def from_monty
    (MP : Type)
    [trait_constr_from_monty_associated_type_i0 :
      MontyParameters.AssociatedTypes
      MP]
    [trait_constr_from_monty_i0 : MontyParameters MP ]
    (x : u32) :
    RustM u32 := do
  (monty_reduce MP (← (rust_primitives.hax.cast_op x : RustM u64)))

--  PackedMontyParameters contains constants needed for MONTY operations for packings of Monty31 fields.
class PackedMontyParameters.AssociatedTypes (Self : Type) where
  [trait_constr_PackedMontyParameters_i0 : MontyParameters.AssociatedTypes Self]

attribute [instance_reducible, instance]
  PackedMontyParameters.AssociatedTypes.trait_constr_PackedMontyParameters_i0

class PackedMontyParameters (Self : Type)
  [associatedTypes : outParam (PackedMontyParameters.AssociatedTypes (Self :
      Type))]
  where
  [trait_constr_PackedMontyParameters_i0 : MontyParameters Self]

attribute [instance_reducible, instance]
  PackedMontyParameters.trait_constr_PackedMontyParameters_i0

structure MontyField31
  (MP : Type)
  [trait_constr_MontyField31_associated_type_i0 :
    MontyParameters.AssociatedTypes
    MP]
  [trait_constr_MontyField31_i0 : MontyParameters MP ]
  where
  value : u32
  _phantom : (core_models.marker.PhantomData MP)

@[instance] opaque Impl_11.AssociatedTypes
  (MP : Type)
  [trait_constr_Impl_11_associated_type_i0 :
    core_models.clone.Clone.AssociatedTypes
    MP]
  [trait_constr_Impl_11_i0 : core_models.clone.Clone MP ]
  [trait_constr_Impl_11_associated_type_i1 : MontyParameters.AssociatedTypes MP]
  [trait_constr_Impl_11_i1 : MontyParameters MP ] :
  core_models.clone.Clone.AssociatedTypes (MontyField31 MP) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_11
  (MP : Type)
  [trait_constr_Impl_11_associated_type_i0 :
    core_models.clone.Clone.AssociatedTypes
    MP]
  [trait_constr_Impl_11_i0 : core_models.clone.Clone MP ]
  [trait_constr_Impl_11_associated_type_i1 : MontyParameters.AssociatedTypes MP]
  [trait_constr_Impl_11_i1 : MontyParameters MP ] :
  core_models.clone.Clone (MontyField31 MP) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_12.AssociatedTypes
  (MP : Type)
  [trait_constr_Impl_12_associated_type_i0 :
    core_models.marker.Copy.AssociatedTypes
    MP]
  [trait_constr_Impl_12_i0 : core_models.marker.Copy MP ]
  [trait_constr_Impl_12_associated_type_i1 : MontyParameters.AssociatedTypes MP]
  [trait_constr_Impl_12_i1 : MontyParameters MP ] :
  core_models.marker.Copy.AssociatedTypes (MontyField31 MP) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_12
  (MP : Type)
  [trait_constr_Impl_12_associated_type_i0 :
    core_models.marker.Copy.AssociatedTypes
    MP]
  [trait_constr_Impl_12_i0 : core_models.marker.Copy MP ]
  [trait_constr_Impl_12_associated_type_i1 : MontyParameters.AssociatedTypes MP]
  [trait_constr_Impl_12_i1 : MontyParameters MP ] :
  core_models.marker.Copy (MontyField31 MP) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_13.AssociatedTypes
  (MP : Type)
  [trait_constr_Impl_13_associated_type_i0 :
    core_models.default.Default.AssociatedTypes
    MP]
  [trait_constr_Impl_13_i0 : core_models.default.Default MP ]
  [trait_constr_Impl_13_associated_type_i1 : MontyParameters.AssociatedTypes MP]
  [trait_constr_Impl_13_i1 : MontyParameters MP ] :
  core_models.default.Default.AssociatedTypes (MontyField31 MP) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_13
  (MP : Type)
  [trait_constr_Impl_13_associated_type_i0 :
    core_models.default.Default.AssociatedTypes
    MP]
  [trait_constr_Impl_13_i0 : core_models.default.Default MP ]
  [trait_constr_Impl_13_associated_type_i1 : MontyParameters.AssociatedTypes MP]
  [trait_constr_Impl_13_i1 : MontyParameters MP ] :
  core_models.default.Default (MontyField31 MP) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_15.AssociatedTypes
  (MP : Type)
  [trait_constr_Impl_15_associated_type_i0 :
    core_models.hash.Hash.AssociatedTypes
    MP]
  [trait_constr_Impl_15_i0 : core_models.hash.Hash MP ]
  [trait_constr_Impl_15_associated_type_i1 : MontyParameters.AssociatedTypes MP]
  [trait_constr_Impl_15_i1 : MontyParameters MP ] :
  core_models.hash.Hash.AssociatedTypes (MontyField31 MP) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_15
  (MP : Type)
  [trait_constr_Impl_15_associated_type_i0 :
    core_models.hash.Hash.AssociatedTypes
    MP]
  [trait_constr_Impl_15_i0 : core_models.hash.Hash MP ]
  [trait_constr_Impl_15_associated_type_i1 : MontyParameters.AssociatedTypes MP]
  [trait_constr_Impl_15_i1 : MontyParameters MP ] :
  core_models.hash.Hash (MontyField31 MP) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_16.AssociatedTypes
  (MP : Type)
  [trait_constr_Impl_16_associated_type_i0 : MontyParameters.AssociatedTypes MP]
  [trait_constr_Impl_16_i0 : MontyParameters MP ] :
  core_models.marker.StructuralPartialEq.AssociatedTypes (MontyField31 MP) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_16
  (MP : Type)
  [trait_constr_Impl_16_associated_type_i0 : MontyParameters.AssociatedTypes MP]
  [trait_constr_Impl_16_i0 : MontyParameters MP ] :
  core_models.marker.StructuralPartialEq (MontyField31 MP) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_17.AssociatedTypes
  (MP : Type)
  [trait_constr_Impl_17_associated_type_i0 :
    core_models.cmp.PartialEq.AssociatedTypes
    MP
    MP]
  [trait_constr_Impl_17_i0 : core_models.cmp.PartialEq MP MP ]
  [trait_constr_Impl_17_associated_type_i1 : MontyParameters.AssociatedTypes MP]
  [trait_constr_Impl_17_i1 : MontyParameters MP ] :
  core_models.cmp.PartialEq.AssociatedTypes (MontyField31 MP) (MontyField31 MP)
  :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_17
  (MP : Type)
  [trait_constr_Impl_17_associated_type_i0 :
    core_models.cmp.PartialEq.AssociatedTypes
    MP
    MP]
  [trait_constr_Impl_17_i0 : core_models.cmp.PartialEq MP MP ]
  [trait_constr_Impl_17_associated_type_i1 : MontyParameters.AssociatedTypes MP]
  [trait_constr_Impl_17_i1 : MontyParameters MP ] :
  core_models.cmp.PartialEq (MontyField31 MP) (MontyField31 MP) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_14.AssociatedTypes
  (MP : Type)
  [trait_constr_Impl_14_associated_type_i0 : core_models.cmp.Eq.AssociatedTypes
    MP]
  [trait_constr_Impl_14_i0 : core_models.cmp.Eq MP ]
  [trait_constr_Impl_14_associated_type_i1 : MontyParameters.AssociatedTypes MP]
  [trait_constr_Impl_14_i1 : MontyParameters MP ] :
  core_models.cmp.Eq.AssociatedTypes (MontyField31 MP) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_14
  (MP : Type)
  [trait_constr_Impl_14_associated_type_i0 : core_models.cmp.Eq.AssociatedTypes
    MP]
  [trait_constr_Impl_14_i0 : core_models.cmp.Eq MP ]
  [trait_constr_Impl_14_associated_type_i1 : MontyParameters.AssociatedTypes MP]
  [trait_constr_Impl_14_i1 : MontyParameters MP ] :
  core_models.cmp.Eq (MontyField31 MP) :=
  by constructor <;> exact Inhabited.default

--  Create a new field element from any `u32`.
-- 
--  Any `u32` value is accepted and automatically converted to Montgomery form.
@[spec]
def Impl.new
    (MP : Type)
    [trait_constr_new_associated_type_i0 : MontyParameters.AssociatedTypes MP]
    [trait_constr_new_i0 : MontyParameters MP ]
    (value : u32) :
    RustM (MontyField31 MP) := do
  (pure (MontyField31.mk
    (value := (← (to_monty MP value)))
    (_phantom := core_models.marker.PhantomData.mk)))

--  FieldParameters contains constants and methods needed to imply PrimeCharacteristicRing, Field and PrimeField32 for MontyField31.
class FieldParameters.AssociatedTypes (Self : Type) where
  [trait_constr_FieldParameters_i0 : PackedMontyParameters.AssociatedTypes Self]

attribute [instance_reducible, instance]
  FieldParameters.AssociatedTypes.trait_constr_FieldParameters_i0

class FieldParameters (Self : Type)
  [associatedTypes : outParam (FieldParameters.AssociatedTypes (Self : Type))]
  where
  [trait_constr_FieldParameters_i0 : PackedMontyParameters Self]
  MONTY_ZERO (Self) :(MontyField31 Self) :=
    RustM.of_isOk (do (Impl.new Self (0 : u32))) (by rfl)
  MONTY_ONE (Self) :(MontyField31 Self) :=
    RustM.of_isOk (do (Impl.new Self (1 : u32))) (by rfl)
  MONTY_TWO (Self) :(MontyField31 Self) :=
    RustM.of_isOk (do (Impl.new Self (2 : u32))) (by rfl)
  MONTY_NEG_ONE (Self) :(MontyField31 Self) :=
    RustM.of_isOk
      (do (Impl.new Self (← ((MontyParameters.PRIME Self) -? (1 : u32)))))
      (by rfl)
  MONTY_GEN (Self) : (MontyField31 Self)
  HALF_P_PLUS_1 (Self) :u32 :=
    RustM.of_isOk
      (do ((← ((MontyParameters.PRIME Self) +? (1 : u32))) >>>? (1 : i32)))
      (by rfl)

attribute [instance_reducible, instance]
  FieldParameters.trait_constr_FieldParameters_i0

--  Given an element `x` from a 31 bit field `F` compute `x/2`.
--  The input must be in `[0, P)`.
--  The output will also be in `[0, P)`.
@[spec]
def halve_u32
    (FP : Type)
    [trait_constr_halve_u32_associated_type_i0 : FieldParameters.AssociatedTypes
      FP]
    [trait_constr_halve_u32_i0 : FieldParameters FP ]
    (input : u32) :
    RustM u32 := do
  let shr : u32 ← (input >>>? (1 : i32));
  let lo_bit : u32 ← (input &&&? (1 : u32));
  let shr_corr : u32 ← (shr +? (FieldParameters.HALF_P_PLUS_1 FP));
  if (← (lo_bit ==? (0 : u32))) then do (pure shr) else do (pure shr_corr)

--  Create a new field element from something already in MONTY form.
--  This is `pub(crate)` for tests and delayed reduction strategies. If you're using it outside of those, you're
--  likely doing something fishy.
@[spec]
def Impl.new_monty
    (MP : Type)
    [trait_constr_new_monty_associated_type_i0 : MontyParameters.AssociatedTypes
      MP]
    [trait_constr_new_monty_i0 : MontyParameters MP ]
    (value : u32) :
    RustM (MontyField31 MP) := do
  (pure (MontyField31.mk
    (value := value)
    (_phantom := core_models.marker.PhantomData.mk)))

--  Produce a u32 in range [0, P) from a field element corresponding to the true value.
@[spec]
def Impl.to_u32
    (MP : Type)
    [trait_constr_to_u32_associated_type_i0 : MontyParameters.AssociatedTypes
      MP]
    [trait_constr_to_u32_i0 : MontyParameters MP ]
    (elem : (MontyField31 MP)) :
    RustM u32 := do
  (from_monty MP (MontyField31.value elem))

--  Convert a `[u32; N]` array to an array of field elements.
-- 
--  Const version of `input.map(MontyField31::new)`.
@[spec]
def Impl.new_array
    (MP : Type)
    (N : usize)
    [trait_constr_new_array_associated_type_i0 : MontyParameters.AssociatedTypes
      MP]
    [trait_constr_new_array_i0 : MontyParameters MP ]
    (input : (RustArray u32 N)) :
    RustM (RustArray (MontyField31 MP) N) := do
  let output : (RustArray (MontyField31 MP) N) ←
    (rust_primitives.hax.repeat (← (Impl.new_monty MP (0 : u32))) N);
  let i : usize := (0 : usize);
  let ⟨i, output⟩ ←
    (rust_primitives.hax.while_loop
      (fun ⟨i, output⟩ => (do (pure true) : RustM Bool))
      (fun ⟨i, output⟩ => (do (i <? N) : RustM Bool))
      (fun ⟨i, output⟩ =>
        (do
        (rust_primitives.hax.int.from_machine (0 : u32)) :
        RustM hax_lib.int.Int))
      (rust_primitives.hax.Tuple2.mk i output)
      (fun ⟨i, output⟩ =>
        (do
        let output : (RustArray (MontyField31 MP) N) ←
          (rust_primitives.hax.monomorphized_update_at.update_at_usize
            output
            i
            (← (Impl.new MP (← input[i]_?))));
        let i : usize ← (i +? (1 : usize));
        (pure (rust_primitives.hax.Tuple2.mk i output)) :
        RustM
        (rust_primitives.hax.Tuple2 usize (RustArray (MontyField31 MP) N)))));
  (pure output)

--  Convert a constant 2d u32 array into a constant 2d array of field elements.
--  Constant version of array.map(MontyField31::new_array).
@[spec]
def Impl.new_2d_array
    (MP : Type)
    (N : usize)
    (M : usize)
    [trait_constr_new_2d_array_associated_type_i0 :
      MontyParameters.AssociatedTypes
      MP]
    [trait_constr_new_2d_array_i0 : MontyParameters MP ]
    (input : (RustArray (RustArray u32 N) M)) :
    RustM (RustArray (RustArray (MontyField31 MP) N) M) := do
  let output : (RustArray (RustArray (MontyField31 MP) N) M) ←
    (rust_primitives.hax.repeat
      (← (rust_primitives.hax.repeat (← (Impl.new_monty MP (0 : u32))) N))
      M);
  let i : usize := (0 : usize);
  let ⟨i, output⟩ ←
    (rust_primitives.hax.while_loop
      (fun ⟨i, output⟩ => (do (pure true) : RustM Bool))
      (fun ⟨i, output⟩ => (do (i <? M) : RustM Bool))
      (fun ⟨i, output⟩ =>
        (do
        (rust_primitives.hax.int.from_machine (0 : u32)) :
        RustM hax_lib.int.Int))
      (rust_primitives.hax.Tuple2.mk i output)
      (fun ⟨i, output⟩ =>
        (do
        let output : (RustArray (RustArray (MontyField31 MP) N) M) ←
          (rust_primitives.hax.monomorphized_update_at.update_at_usize
            output
            i
            (← (Impl.new_array MP (N) (← input[i]_?))));
        let i : usize ← (i +? (1 : usize));
        (pure (rust_primitives.hax.Tuple2.mk i output)) :
        RustM
        (rust_primitives.hax.Tuple2
          usize
          (RustArray (RustArray (MontyField31 MP) N) M)))));
  (pure output)

@[reducible] instance Impl_2.AssociatedTypes
  (FP : Type)
  [trait_constr_Impl_2_associated_type_i0 : MontyParameters.AssociatedTypes FP]
  [trait_constr_Impl_2_i0 : MontyParameters FP ] :
  core_models.ops.arith.Add.AssociatedTypes (MontyField31 FP) (MontyField31 FP)
  where
  Output := (MontyField31 FP)

instance Impl_2
  (FP : Type)
  [trait_constr_Impl_2_associated_type_i0 : MontyParameters.AssociatedTypes FP]
  [trait_constr_Impl_2_i0 : MontyParameters FP ] :
  core_models.ops.arith.Add (MontyField31 FP) (MontyField31 FP)
  where
  add := fun (self : (MontyField31 FP)) (rhs : (MontyField31 FP)) => do
    (Impl.new_monty FP
      (← (add FP (MontyField31.value self) (MontyField31.value rhs))))

@[reducible] instance Impl_3.AssociatedTypes
  (FP : Type)
  [trait_constr_Impl_3_associated_type_i0 : MontyParameters.AssociatedTypes FP]
  [trait_constr_Impl_3_i0 : MontyParameters FP ] :
  core_models.ops.arith.Sub.AssociatedTypes (MontyField31 FP) (MontyField31 FP)
  where
  Output := (MontyField31 FP)

instance Impl_3
  (FP : Type)
  [trait_constr_Impl_3_associated_type_i0 : MontyParameters.AssociatedTypes FP]
  [trait_constr_Impl_3_i0 : MontyParameters FP ] :
  core_models.ops.arith.Sub (MontyField31 FP) (MontyField31 FP)
  where
  sub := fun (self : (MontyField31 FP)) (rhs : (MontyField31 FP)) => do
    (Impl.new_monty FP
      (← (sub FP (MontyField31.value self) (MontyField31.value rhs))))

@[reducible] instance Impl_5.AssociatedTypes
  (FP : Type)
  [trait_constr_Impl_5_associated_type_i0 : MontyParameters.AssociatedTypes FP]
  [trait_constr_Impl_5_i0 : MontyParameters FP ] :
  core_models.ops.arith.Mul.AssociatedTypes (MontyField31 FP) (MontyField31 FP)
  where
  Output := (MontyField31 FP)

instance Impl_5
  (FP : Type)
  [trait_constr_Impl_5_associated_type_i0 : MontyParameters.AssociatedTypes FP]
  [trait_constr_Impl_5_i0 : MontyParameters FP ] :
  core_models.ops.arith.Mul (MontyField31 FP) (MontyField31 FP)
  where
  mul := fun (self : (MontyField31 FP)) (rhs : (MontyField31 FP)) => do
    let long_prod : u64 ←
      ((← (rust_primitives.hax.cast_op (MontyField31.value self) : RustM u64))
        *? (← (rust_primitives.hax.cast_op
          (MontyField31.value rhs) :
          RustM u64)));
    (Impl.new_monty FP (← (monty_reduce FP long_prod)))

@[reducible] instance Impl_6.AssociatedTypes
  (FP : Type)
  [trait_constr_Impl_6_associated_type_i0 : FieldParameters.AssociatedTypes FP]
  [trait_constr_Impl_6_i0 : FieldParameters FP ] :
  core_models.ops.arith.AddAssign.AssociatedTypes
  (MontyField31 FP)
  (MontyField31 FP)
  where

instance Impl_6
  (FP : Type)
  [trait_constr_Impl_6_associated_type_i0 : FieldParameters.AssociatedTypes FP]
  [trait_constr_Impl_6_i0 : FieldParameters FP ] :
  core_models.ops.arith.AddAssign (MontyField31 FP) (MontyField31 FP)
  where
  add_assign := fun (self : (MontyField31 FP)) (rhs : (MontyField31 FP)) => do
    let self : (MontyField31 FP) ←
      (core_models.ops.arith.Add.add
        (MontyField31 FP)
        (MontyField31 FP) self rhs);
    (pure self)

@[reducible] instance Impl_7.AssociatedTypes
  (FP : Type)
  [trait_constr_Impl_7_associated_type_i0 : FieldParameters.AssociatedTypes FP]
  [trait_constr_Impl_7_i0 : FieldParameters FP ] :
  core_models.ops.arith.SubAssign.AssociatedTypes
  (MontyField31 FP)
  (MontyField31 FP)
  where

instance Impl_7
  (FP : Type)
  [trait_constr_Impl_7_associated_type_i0 : FieldParameters.AssociatedTypes FP]
  [trait_constr_Impl_7_i0 : FieldParameters FP ] :
  core_models.ops.arith.SubAssign (MontyField31 FP) (MontyField31 FP)
  where
  sub_assign := fun (self : (MontyField31 FP)) (rhs : (MontyField31 FP)) => do
    let self : (MontyField31 FP) ←
      (core_models.ops.arith.Sub.sub
        (MontyField31 FP)
        (MontyField31 FP) self rhs);
    (pure self)

@[reducible] instance Impl_8.AssociatedTypes
  (FP : Type)
  [trait_constr_Impl_8_associated_type_i0 : FieldParameters.AssociatedTypes FP]
  [trait_constr_Impl_8_i0 : FieldParameters FP ] :
  core_models.ops.arith.MulAssign.AssociatedTypes
  (MontyField31 FP)
  (MontyField31 FP)
  where

instance Impl_8
  (FP : Type)
  [trait_constr_Impl_8_associated_type_i0 : FieldParameters.AssociatedTypes FP]
  [trait_constr_Impl_8_i0 : FieldParameters FP ] :
  core_models.ops.arith.MulAssign (MontyField31 FP) (MontyField31 FP)
  where
  mul_assign := fun (self : (MontyField31 FP)) (rhs : (MontyField31 FP)) => do
    let self : (MontyField31 FP) ←
      (core_models.ops.arith.Mul.mul
        (MontyField31 FP)
        (MontyField31 FP) self rhs);
    (pure self)

--  NOTE: Placeholder dummy impl
@[reducible] instance Impl_9.AssociatedTypes
  (FP : Type)
  [trait_constr_Impl_9_associated_type_i0 : FieldParameters.AssociatedTypes FP]
  [trait_constr_Impl_9_i0 : FieldParameters FP ] :
  mersenne31.unimplemented.Product.AssociatedTypes
  (MontyField31 FP)
  (MontyField31 FP)
  where

instance Impl_9
  (FP : Type)
  [trait_constr_Impl_9_associated_type_i0 : FieldParameters.AssociatedTypes FP]
  [trait_constr_Impl_9_i0 : FieldParameters FP ] :
  mersenne31.unimplemented.Product (MontyField31 FP) (MontyField31 FP)
  where
  product :=
    fun
      (I : Type)
      [trait_constr_product_associated_type_i1 :
        mersenne31.unimplemented.Iterator.AssociatedTypes
        I]
      [trait_constr_product_i1 : mersenne31.unimplemented.Iterator
        I
        (associatedTypes := {
          show mersenne31.unimplemented.Iterator.AssociatedTypes I
          by infer_instance
          with Item := (MontyField31 FP)})] (iter : I) => do
    (Impl.new FP (0 : u32))

@[reducible] instance Impl_10.AssociatedTypes
  (FP : Type)
  [trait_constr_Impl_10_associated_type_i0 : FieldParameters.AssociatedTypes FP]
  [trait_constr_Impl_10_i0 : FieldParameters FP ] :
  mersenne31.unimplemented.Sum.AssociatedTypes
  (MontyField31 FP)
  (MontyField31 FP)
  where

instance Impl_10
  (FP : Type)
  [trait_constr_Impl_10_associated_type_i0 : FieldParameters.AssociatedTypes FP]
  [trait_constr_Impl_10_i0 : FieldParameters FP ] :
  mersenne31.unimplemented.Sum (MontyField31 FP) (MontyField31 FP)
  where
  sum :=
    fun
      (I : Type)
      [trait_constr_sum_associated_type_i1 :
        mersenne31.unimplemented.Iterator.AssociatedTypes
        I]
      [trait_constr_sum_i1 : mersenne31.unimplemented.Iterator
        I
        (associatedTypes := {
          show mersenne31.unimplemented.Iterator.AssociatedTypes I
          by infer_instance
          with Item := (MontyField31 FP)})] (iter : I) => do
    (Impl.new FP (0 : u32))

end mersenne31.monty_31


namespace mersenne31.koalabear

--  The prime field `2^31 - 2^24 + 1`, a.k.a. the Koala Bear field.
abbrev KoalaBear :
  Type :=
  (mersenne31.monty_31.MontyField31 KoalaBearParameters)

@[reducible] instance Impl.AssociatedTypes :
  mersenne31.monty_31.MontyParameters.AssociatedTypes KoalaBearParameters
  where

instance Impl : mersenne31.monty_31.MontyParameters KoalaBearParameters where
  PRIME := (2130706433 : u32)
  MONTY_BITS := (32 : u32)
  MONTY_MU := (2164260865 : u32)

end mersenne31.koalabear


namespace mersenne31.mersenne31

--  NOTE: Dummy implementation of a dummy trait
@[reducible] instance Impl_3.AssociatedTypes :
  mersenne31.field.PrimeField32.AssociatedTypes Mersenne31
  where

instance Impl_3 : mersenne31.field.PrimeField32 Mersenne31 where
  ORDER_U32 := P
  as_canonical_u32 := fun (self : Mersenne31) => do
    if
    (← ((Mersenne31.value self)
      ==? (mersenne31.field.PrimeField32.ORDER_U32 Mersenne31))) then do
      (pure (0 : u32))
    else do
      (pure (Mersenne31.value self))

end mersenne31.mersenne31


namespace mersenne31.monty_31

@[reducible] instance Impl_4.AssociatedTypes
  (FP : Type)
  [trait_constr_Impl_4_associated_type_i0 : FieldParameters.AssociatedTypes FP]
  [trait_constr_Impl_4_i0 : FieldParameters FP ] :
  core_models.ops.arith.Neg.AssociatedTypes (MontyField31 FP)
  where
  Output := (MontyField31 FP)

instance Impl_4
  (FP : Type)
  [trait_constr_Impl_4_associated_type_i0 : FieldParameters.AssociatedTypes FP]
  [trait_constr_Impl_4_i0 : FieldParameters FP ] :
  core_models.ops.arith.Neg (MontyField31 FP)
  where
  neg := fun (self : (MontyField31 FP)) => do
    (core_models.ops.arith.Sub.sub
      (MontyField31 FP)
      (MontyField31 FP)
      (mersenne31.field.PrimeCharacteristicRing.ZERO (MontyField31 FP))
      self)

@[reducible] instance Impl_1.AssociatedTypes
  (FP : Type)
  [trait_constr_Impl_1_associated_type_i0 : FieldParameters.AssociatedTypes FP]
  [trait_constr_Impl_1_i0 : FieldParameters FP ] :
  mersenne31.field.PrimeCharacteristicRing.AssociatedTypes (MontyField31 FP)
  where
  PrimeSubfield := (MontyField31 FP)

instance Impl_1
  (FP : Type)
  [trait_constr_Impl_1_associated_type_i0 : FieldParameters.AssociatedTypes FP]
  [trait_constr_Impl_1_i0 : FieldParameters FP ] :
  mersenne31.field.PrimeCharacteristicRing (MontyField31 FP)
  where
  ZERO := RustM.of_isOk (do (FieldParameters.MONTY_ZERO FP)) (by rfl)
  ONE := RustM.of_isOk (do (FieldParameters.MONTY_ONE FP)) (by rfl)
  TWO := RustM.of_isOk (do (FieldParameters.MONTY_TWO FP)) (by rfl)
  NEG_ONE := RustM.of_isOk (do (FieldParameters.MONTY_NEG_ONE FP)) (by rfl)
  from_prime_subfield := fun (f : (MontyField31 FP)) => do (pure f)
  halve := fun (self : (MontyField31 FP)) => do
    (Impl.new_monty FP (← (halve_u32 FP (MontyField31.value self))))

end mersenne31.monty_31


namespace mersenne31.mersenne31

--  NOTE: Dummy implementation of a dummy trait
@[reducible] instance Impl_2.AssociatedTypes :
  mersenne31.field.PrimeField64.AssociatedTypes Mersenne31
  where

instance Impl_2 : mersenne31.field.PrimeField64 Mersenne31 where
  ORDER_U64 := P64
  as_canonical_u64 := fun (self : Mersenne31) => do
    (core_models.convert.Into.into
      u32
      u64 (← (mersenne31.field.PrimeField32.as_canonical_u32 Mersenne31 self)))

@[reducible] instance Impl_4.AssociatedTypes :
  core_models.ops.arith.Add.AssociatedTypes Mersenne31 Mersenne31
  where
  Output := Mersenne31

instance Impl_4 : core_models.ops.arith.Add Mersenne31 Mersenne31 where
  add := fun (self : Mersenne31) (rhs : Mersenne31) => do
    let ⟨sum_i32, over⟩ ←
      (core_models.num.Impl_2.overflowing_add
        (← (rust_primitives.hax.cast_op (Mersenne31.value self) : RustM i32))
        (← (rust_primitives.hax.cast_op (Mersenne31.value rhs) : RustM i32)));
    let sum_u32 : u32 ← (rust_primitives.hax.cast_op sum_i32 : RustM u32);
    let sum_corr : u32 ←
      (core_models.num.Impl_8.wrapping_sub
        sum_u32
        (mersenne31.field.PrimeField32.ORDER_U32 Mersenne31));
    (Impl.new_reduced
      (← if over then do (pure sum_corr) else do (pure sum_u32)))

@[reducible] instance Impl_5.AssociatedTypes :
  core_models.ops.arith.Sub.AssociatedTypes Mersenne31 Mersenne31
  where
  Output := Mersenne31

instance Impl_5 : core_models.ops.arith.Sub Mersenne31 Mersenne31 where
  sub := fun (self : Mersenne31) (rhs : Mersenne31) => do
    let ⟨sub, over⟩ ←
      (core_models.num.Impl_8.overflowing_sub
        (Mersenne31.value self)
        (Mersenne31.value rhs));
    let sub : u32 ← (sub -? (← (rust_primitives.hax.cast_op over : RustM u32)));
    (Impl.new_reduced
      (← (sub &&&? (mersenne31.field.PrimeField32.ORDER_U32 Mersenne31))))

@[reducible] instance Impl_6.AssociatedTypes :
  core_models.ops.arith.Neg.AssociatedTypes Mersenne31
  where
  Output := Mersenne31

instance Impl_6 : core_models.ops.arith.Neg Mersenne31 where
  neg := fun (self : Mersenne31) => do
    (Impl.new_reduced
      (← ((mersenne31.field.PrimeField32.ORDER_U32 Mersenne31)
        -? (Mersenne31.value self))))

@[reducible] instance Impl_8.AssociatedTypes :
  core_models.ops.arith.AddAssign.AssociatedTypes Mersenne31 Mersenne31
  where

instance Impl_8 : core_models.ops.arith.AddAssign Mersenne31 Mersenne31 where
  add_assign := fun (self : Mersenne31) (rhs : Mersenne31) => do
    let self : Mersenne31 ←
      (core_models.ops.arith.Add.add Mersenne31 Mersenne31 self rhs);
    (pure self)

@[reducible] instance Impl_9.AssociatedTypes :
  core_models.ops.arith.SubAssign.AssociatedTypes Mersenne31 Mersenne31
  where

instance Impl_9 : core_models.ops.arith.SubAssign Mersenne31 Mersenne31 where
  sub_assign := fun (self : Mersenne31) (rhs : Mersenne31) => do
    let self : Mersenne31 ←
      (core_models.ops.arith.Sub.sub Mersenne31 Mersenne31 self rhs);
    (pure self)

@[spec]
def from_u62 (input : u64) : RustM Mersenne31 := do
  let _ ← (hax_lib.assert (← (input <? (← ((1 : u64) <<<? (62 : i32))))));
  let input_lo : u32 ←
    (rust_primitives.hax.cast_op
      (← (input &&&? (← ((← ((1 : u64) <<<? (31 : i32))) -? (1 : u64))))) :
      RustM u32);
  let input_high : u32 ←
    (rust_primitives.hax.cast_op (← (input >>>? (31 : i32))) : RustM u32);
  (core_models.ops.arith.Add.add
    Mersenne31
    Mersenne31
    (← (Impl.new_reduced input_lo))
    (← (Impl.new_reduced input_high)))

@[reducible] instance Impl_7.AssociatedTypes :
  core_models.ops.arith.Mul.AssociatedTypes Mersenne31 Mersenne31
  where
  Output := Mersenne31

instance Impl_7 : core_models.ops.arith.Mul Mersenne31 Mersenne31 where
  mul := fun (self : Mersenne31) (rhs : Mersenne31) => do
    let prod : u64 ←
      ((← (core_models.convert.From._from u64 u32 (Mersenne31.value self)))
        *? (← (core_models.convert.From._from u64 u32 (Mersenne31.value rhs))));
    (from_u62 prod)

@[reducible] instance Impl_10.AssociatedTypes :
  core_models.ops.arith.MulAssign.AssociatedTypes Mersenne31 Mersenne31
  where

instance Impl_10 : core_models.ops.arith.MulAssign Mersenne31 Mersenne31 where
  mul_assign := fun (self : Mersenne31) (rhs : Mersenne31) => do
    let self : Mersenne31 ←
      (core_models.ops.arith.Mul.mul Mersenne31 Mersenne31 self rhs);
    (pure self)

@[reducible] instance Impl_1.AssociatedTypes :
  mersenne31.field.PrimeCharacteristicRing.AssociatedTypes Mersenne31
  where
  PrimeSubfield := Mersenne31

instance Impl_1 : mersenne31.field.PrimeCharacteristicRing Mersenne31 where
  ZERO := RustM.of_isOk (do (Mersenne31.mk (value := (0 : u32)))) (by rfl)
  ONE := RustM.of_isOk (do (Mersenne31.mk (value := (1 : u32)))) (by rfl)
  TWO := RustM.of_isOk (do (Mersenne31.mk (value := (2 : u32)))) (by rfl)
  NEG_ONE := RustM.of_isOk
    (do
    (Mersenne31.mk
      (value := (← ((mersenne31.field.PrimeField32.ORDER_U32 Mersenne31)
        -? (1 : u32))))))
    (by rfl)
  from_prime_subfield := fun (f : Mersenne31) => do (pure f)
  from_bool := fun (b : Bool) => do
    (Impl.new_reduced (← (rust_primitives.hax.cast_op b : RustM u32)))

--  Convert a `[u32; N]` array to an array of field elements.
-- 
--  Const version of `input.map(Mersenne31::new)`.
@[spec]
def Impl.new_array (N : usize) (input : (RustArray u32 N)) :
    RustM (RustArray Mersenne31 N) := do
  let output : (RustArray Mersenne31 N) ←
    (rust_primitives.hax.repeat
      (mersenne31.field.PrimeCharacteristicRing.ZERO Mersenne31)
      N);
  let i : usize := (0 : usize);
  let ⟨i, output⟩ ←
    (rust_primitives.hax.while_loop
      (fun ⟨i, output⟩ => (do (pure true) : RustM Bool))
      (fun ⟨i, output⟩ => (do (i <? N) : RustM Bool))
      (fun ⟨i, output⟩ =>
        (do
        (rust_primitives.hax.int.from_machine (0 : u32)) :
        RustM hax_lib.int.Int))
      (rust_primitives.hax.Tuple2.mk i output)
      (fun ⟨i, output⟩ =>
        (do
        let output : (RustArray Mersenne31 N) ←
          (rust_primitives.hax.monomorphized_update_at.update_at_usize
            output
            i
            {(← output[i]_?) with value := (← ((← input[i]_?) %? P))});
        let i : usize ← (i +? (1 : usize));
        (pure (rust_primitives.hax.Tuple2.mk i output)) :
        RustM (rust_primitives.hax.Tuple2 usize (RustArray Mersenne31 N)))));
  (pure output)

end mersenne31.mersenne31

