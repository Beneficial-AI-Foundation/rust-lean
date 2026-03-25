import MerkleRootLean.Extracted.Merkle_root_rs

-- The theorems below are not crypto-security statements; they are
-- machine-checked properties of the Rust-extracted code (in the current model).

/--
`verify` is definitionally "compute root and compare with expected_root".
-/
theorem merkle_verify_is_pure_eq
  (leaf : Merkle_root_rs.Digest)
  (index : u32)
  (digests : RustSlice Merkle_root_rs.Digest)
  (expected_root : Merkle_root_rs.Digest)
  (hash_pair :
    Merkle_root_rs.Digest → Merkle_root_rs.Digest → RustM Merkle_root_rs.Digest) :
  Merkle_root_rs.merkle_verify_from_path leaf index digests expected_root hash_pair
    =
  (do
    let r ← Merkle_root_rs.merkle_root_from_path leaf index digests hash_pair
    Core.Cmp.PartialEq.eq Merkle_root_rs.Digest Merkle_root_rs.Digest r expected_root) := by
  -- just unfolding the definition is enough
  simp [Merkle_root_rs.merkle_verify_from_path]

/--
Conditional "acceptance" lemma:
if `merkle_root_from_path ...` evaluates to `ok r`, then verifying with `expected_root = r`
evaluates to `ok true`.

This avoids having to prove determinism of re-running `merkle_root_from_path`.
-/
theorem merkle_verify_of_root_ok_is_true
  (leaf : Merkle_root_rs.Digest)
  (index : u32)
  (digests : RustSlice Merkle_root_rs.Digest)
  (hash_pair :
    Merkle_root_rs.Digest → Merkle_root_rs.Digest → RustM Merkle_root_rs.Digest)
  (r : Merkle_root_rs.Digest)
  (hroot :
    Merkle_root_rs.merkle_root_from_path leaf index digests hash_pair = RustM.ok r) :
  Merkle_root_rs.merkle_verify_from_path leaf index digests r hash_pair = RustM.ok true := by
  simp [Merkle_root_rs.merkle_verify_from_path, hroot]
