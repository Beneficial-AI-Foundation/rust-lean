#!/bin/bash

set -euo pipefail

######################
# GENERATE LEAN CODE #
######################

# Set up Opam for Hax to work
eval $(opam env)

Extraction_Dir='lean/Mersenne31'

# Extract with Hax
cargo hax into --output-dir $Extraction_Dir lean

###########################
# FIXES TO GENERATED CODE #
###########################

Extracted_File_Name='Mersenne31.lean'
Extracted_File="$Extraction_Dir/$Extracted_File_Name"

# FIX 0
# Generated file now starts lowercase and this project (and Hax, previously) expects it uppercase
Extracted_File_Name_Lowercase='mersenne31.lean'
Extracted_File_Lowercase="$Extraction_Dir/$Extracted_File_Name_Lowercase"
mv $Extracted_File_Lowercase $Extracted_File


# FIX 1
# Import HaxPatch file and open HaxPatch namespace
Insert_After='import Std.Tactic.Do.Syntax'
HaxPatch_Import='import Mersenne31.HaxPatch\nopen HaxPatch'
Subst_String="${Insert_After}\n${HaxPatch_Import}"
sed -i -z -e "s/$Insert_After/$Subst_String/" $Extracted_File

# FIX 2
# Remove fully quantified name for trait's constants used in trait function definitions
# Tracking issue: https://github.com/cryspen/hax/issues/1889
ZERO='(PrimeCharacteristicRing.ZERO Self)'
ONE='(PrimeCharacteristicRing.ONE Self)'
sed -i -z -e "s/$ZERO/ ZERO/" $Extracted_File
sed -i -z -e "s/$ONE/ ONE/" $Extracted_File
sed -i -z -e 's/ONE\n    else ZERO/ONE else ZERO/' $Extracted_File # For sane identation

AS_CANONICAL_U64_BAD='(PrimeField64.as_canonical_u64 Self self)'
AS_CANONICAL_U64_GUD='(as_canonical_u64 self)'
AS_CANONICAL_U32_BAD='(PrimeField32.as_canonical_u32 Self self)'
AS_CANONICAL_U32_GUD='(as_canonical_u32 self)'
sed -i -e "s/$AS_CANONICAL_U64_BAD/$AS_CANONICAL_U64_GUD/" $Extracted_File
sed -i -e "s/$AS_CANONICAL_U32_BAD/$AS_CANONICAL_U32_GUD/" $Extracted_File

ORDER32_Full='(Mersenne31.value self)\n      (← (Mersenne31.Field.PrimeField32.ORDER_U32 Mersenne31))))'
ORDER32_Def='(Mersenne31.value self) P))' # In this case we directly substitute for the definition
sed -i -z -e "s/${ORDER32_Full}/${ORDER32_Def}/" $Extracted_File

# FIX 3
# Some casts need to be made explicit
Bool_u32_Cast="let sub : u32 ← (sub -? (← (Rust_primitives.Hax.cast_op over)));"
Explicit_Bool_u32_Cast="let sub : u32 ← (sub -? (← (@Rust_primitives.Hax.cast_op Bool u32 _ over)));"
sed -i -e "s/${Bool_u32_Cast}/${Explicit_Bool_u32_Cast}/" $Extracted_File

# FIX 4
# Spurious bind annotations
# Tracking issue: https://github.com/cryspen/hax/issues/1928
ORDER32_bind='(← ((← (Mersenne31.Field.PrimeField32.ORDER_U32 Mersenne31))'
ORDER32_nobind='(← ((Mersenne31.Field.PrimeField32.ORDER_U32 Mersenne31)'
sed -i -e "s/${ORDER32_bind}/${ORDER32_nobind}/" $Extracted_File

ORDER32_bind1='(value := (← ((← (Mersenne31.Field.PrimeField32.ORDER_U32 Mersenne31))'
ORDER32_nobind1='(value := (← ((Mersenne31.Field.PrimeField32.ORDER_U32 Mersenne31)'
sed -i -e "s/${ORDER32_bind1}/${ORDER32_nobind1}/" $Extracted_File

###########
# MONTY31 #
###########

# MONTY_BITS_BAD='(← ((← ((1 : u64) <<<? (← (MontyParameters.MONTY_BITS Self))))'
# MONTY_BITS_GOOD='(← ((← ((1 : u64) <<<? MONTY_BITS))'
# sed -i -e "s/${MONTY_BITS_BAD}/${MONTY_BITS_GOOD}/" $Extracted_File

MONTY_BITS_BAD='(← ((← ((1 : u64) <<<? (MontyParameters.MONTY_BITS Self)))'
MONTY_BITS_GOOD='(← ((← ((1 : u64) <<<? MONTY_BITS))'
sed -i -e "s/${MONTY_BITS_BAD}/${MONTY_BITS_GOOD}/" $Extracted_File

# MONTY_B='%? (← (Rust_primitives.Hax.cast_op (← (MontyParameters.PRIME MP)))))))'
# MONTY_G='%? (← (@Rust_primitives.Hax.cast_op u32 u64 _ (← (MontyParameters.PRIME MP)))))))'
# sed -i -e "s/${MONTY_B}/${MONTY_G}/" $Extracted_File

# MONTY_B='(← ((← ((← (Rust_primitives.Hax.cast_op x))\n        <<<? (← (MontyParameters.MONTY_BITS MP))))'
# MONTY_G='(← ((← ((← (@Rust_primitives.Hax.cast_op u32 u64 _ x))\n        <<<? (MontyParameters.MONTY_BITS MP)))'
# sed -i -z -e "s/${MONTY_B}/${MONTY_G}/" $Extracted_File

# MONTY_B='← (MontyParameters.MONTY_BITS MP)'
# MONTY_G='MontyParameters.MONTY_BITS MP'
# sed -i -e "s/${MONTY_B}/${MONTY_G}/g" $Extracted_File

# MONTY_B='← (MontyParameters.MONTY_MU MP)'
# MONTY_G='MontyParameters.MONTY_MU MP'
# sed -i -e "s/${MONTY_B}/${MONTY_G}/g" $Extracted_File

# MONTY_B='← (MontyParameters.PRIME Self)'
# MONTY_G='MontyParameters.PRIME Self'
# sed -i -e "s/${MONTY_B}/${MONTY_G}/g" $Extracted_File

# MONTY_B='← (MontyParameters.PRIME MP)'
# MONTY_G='MontyParameters.PRIME MP'
# sed -i -e "s/${MONTY_B}/${MONTY_G}/g" $Extracted_File

# MONTY_B='(t \*? (← (Rust_primitives.Hax.cast_op'
# MONTY_G='(t \*? (← (@Rust_primitives.Hax.cast_op u32 u64 _'
# sed -i -e "s/${MONTY_B}/${MONTY_G}/g" $Extracted_File
