#!/bin/bash

set -euo pipefail

#######################
# GENERATE LEAN FILES #
#######################

# NOTE: $AENEAS_DIR should point to your local Aeneas directory
AENEAS="${AENEAS_DIR}/bin/aeneas"
CHARON_VERSION=$(sed -n 2p "${AENEAS_DIR}/charon-pin")

# Generate Charon .llbc file
nix run "github:AeneasVerif/charon/${CHARON_VERSION}" cargo -- --preset=aeneas

# Run Aeneas
$AENEAS -backend lean aeneas_field_arithmetic.llbc -split-files
# nix variant
# nix run github:aeneasverif/aeneas -L -- -backend lean aeneas_field_arithmetic.llbc -split-files

############################
# FIXES TO GENERATED FILES #
############################

# FIX 1
# Mishandling of circularities due to derived implementations
# Tracking issue: https://github.com/AeneasVerif/aeneas/issues/824
bad="mersenne31.Mersenne31.Insts.Aeneas_field_arithmeticFieldPrimeCharacteristicRingMersenne31.corecloneCloneInst.clone"
gud="mersenne31.Mersenne31.Insts.CoreCloneClone.clone"
sed -i -z -e "s/${bad}/${gud}/" Funs.lean
sed -i -z -e "s/${bad}/${gud}/" Funs.lean
bad="mersenne31.Mersenne31.Insts.Aeneas_field_arithmeticFieldPrimeCharacteristicRingMersenne31.coreopsarithAddInst.add"
gud="mersenne31.Mersenne31.Insts.CoreOpsArithAddMersenne31Mersenne31.add"
sed -i -z -e "s/${bad}/${gud}/" Funs.lean

bad="mersenne31.Mersenne31.Insts.Aeneas_field_arithmeticFieldFieldMersenne31Mersenne31.AlgebraInst"
gud="mersenne31.Mersenne31.Insts.Aeneas_field_arithmeticFieldAlgebraMersenne31Mersenne31"
sed -i -z -e "s/${bad}/${gud}/" Funs.lean
bad="mersenne31.Mersenne31.Insts.Aeneas_field_arithmeticFieldFieldMersenne31Mersenne31.corecmpEqInst"
gud="mersenne31.Mersenne31.Insts.CoreCmpEq"
sed -i -z -e "s/${bad}/${gud}/" Funs.lean

bad="let m ←\n    mersenne31.Mersenne31.Insts.Aeneas_field_arithmeticFieldAlgebraMersenne31Mersenne31.PrimeCharacteristicRingInst.ONE"
gud="let m :=\n    mersenne31.Mersenne31.Insts.Aeneas_field_arithmeticFieldPrimeCharacteristicRingMersenne31.ONE"
sed -i -z -e "s/${bad}/${gud}/" Funs.lean

########
# MISC #
########

# Rename template files
mv TypesExternal_Template.lean TypesExternal.lean
mv FunsExternal_Template.lean FunsExternal.lean

# Correct imports for the generated files in our repository structure
bad="import AeneasFieldArithmetic.TypesExternal"
gud="import AeneasFieldArithmetic.Generated.TypesExternal"
sed -i -z -e "s/${bad}/${gud}/" Types.lean
bad="import AeneasFieldArithmetic.Types"
gud="import AeneasFieldArithmetic.Generated.Types"
sed -i -z -e "s/${bad}/${gud}/" FunsExternal.lean
sed -i -z -e "s/${bad}/${gud}/" Funs.lean
bad="import AeneasFieldArithmetic.FunsExternal"
gud="import AeneasFieldArithmetic.Generated.FunsExternal"
sed -i -z -e "s/${bad}/${gud}/" Funs.lean

# Move generated files into the `lean` folder
mv *.lean lean/AeneasFieldArithmetic/Generated

