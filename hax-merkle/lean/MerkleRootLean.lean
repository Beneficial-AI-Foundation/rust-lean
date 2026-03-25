-- This module serves as the root of the `MerkleRootLean` library.
-- Import modules here that should be built as part of the library.
import MerkleRootLean.Basic

import MerkleRootLean.Spec
import MerkleRootLean.Proof

-- @ TODO we should work with ArkLib and MathLib here.
-- 1. download ArkLib from Git
-- 2. lake build
-- 3. add dependenies in lakefile.toml file (require... dependencies) and link to locally built ArkLib (should be in root folder of zkvm-merkle-lean-verified)
-- import ArkLib.Hash
