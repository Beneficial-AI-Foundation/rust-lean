-- This module serves as the root of the `FoldArityVerif` library.
-- Import modules here that should be built as part of the library.
--
-- NOTE: FoldingCorrectness imports ArkLib (which pulls in Batteries/mathlib),
-- while BasicProofs imports Aeneas. These two have a name collision on
-- `BitVec.toNat_pow`, so they cannot be imported in the same environment.
-- FoldingCorrectness is built as a separate lean_lib target in lakefile.lean.
import FoldArityVerif.Basic
import FoldArityVerif.BasicProofs
