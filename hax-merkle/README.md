# Current status

Build a first end-to-end prototype pipeline:

Rust → hax extraction → Lean 4 → (specification / proof)

Target: “representative zkVM-related code” with a clear, simple spec and a tractable first proof milestone.

## Choosing an initial verification target

Source: [Risk0 merkle.rs](https://github.com/risc0/risc0/blob/2e73cb82cadfbad9190b2b34f124481c9b57d371/risc0/zkvm/src/receipt/merkle.rs)

We selected Merkle root recomputation / inclusion verification (the root() and verify() logic) as the first candidate.

```rust
impl MerkleProof {
    /// Verify the Merkle inclusion proof against the given leaf and root.
    pub fn verify(
        &self,
        leaf: &Digest,
        root: &Digest,
        hashfn: &dyn HashFn<BabyBear>,
    ) -> Result<()> {
        ensure!(
            self.root(leaf, hashfn) == *root,
            "merkle proof verify failed"
        );
        Ok(())
    }

    /// Calculate the root of this branch by iteratively hashing, starting from the leaf.
    pub fn root(&self, leaf: &Digest, hashfn: &dyn HashFn<BabyBear>) -> Digest {
        let mut cur = *leaf;
        let mut cur_index = self.index;
        for sibling in &self.digests {
            cur = if cur_index & 1 == 0 {
                *hashfn.hash_pair(&cur, sibling)
            } else {
                *hashfn.hash_pair(sibling, &cur)
            };
            cur_index >>= 1;
        }
        cur
    }
}

```

### Why this is a strong first candidate

- Actually used in both RISC0 and Jolt (commitments to memory/trace pages)
- Elementary specification: "root = fold over path"
- Possible to prove the logic's correctness without cryptographic assumptions about the hash
- Convenient to link with the "Oracle" concept from ArkLib: hash compression can be an oracle

## Adapt the Rust code for extraction

Instead of extracting the entire RISC0 codebase, we created a small Rust crate that preserves the algorithm but uses an extraction-friendly interface.

Simplifications performed:

- Removed Trait Dependencies
- Eliminated Result Type and Error Handling
- Flattened Struct into Function Parameters
- Removed Generic Type Parameters
- Added Toy Hash for Testing

This is acceptable for formal verification prototyping: we preserved the algorithmic core and created a minimal extraction target.

Example Rust code (core function):

```rust

// This is a "representative zkVM code": the algorithm is identical, 
// the interface has been adapted for verification/extraction. 

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Digest(pub [u32; 8]);

pub fn merkle_root_from_path(
    leaf: Digest,
    index: u32,
    digests: &[Digest],
    hash_pair: fn(&Digest, &Digest) -> Digest,
) -> Digest {
    let mut cur = leaf;
    let mut cur_index = index;
    for sibling in digests {
        cur = if cur_index & 1 == 0 {
            hash_pair(&cur, sibling)
        } else {
            hash_pair(sibling, &cur)
        };
        cur_index >>= 1;
    }
    cur
}

pub fn merkle_verify_from_path(
    leaf: Digest,
    index: u32,
    digests: &[Digest],
    expected_root: Digest,
    hash_pair: fn(&Digest, &Digest) -> Digest,
) -> bool {
    merkle_root_from_path(leaf, index, digests, hash_pair) == expected_root
}

// For `сargo test` to pass and provide a basic sanity check, we implement a 'toy hash' function:

#[cfg(test)]
mod tests {
    use super::*;

    fn toy_hash_pair(a: &Digest, b: &Digest) -> Digest {
        let mut out = [0u32; 8];
        for i in 0..8 {
            out[i] = a.0[i].wrapping_add(b.0[i]) ^ 0x9e3779b9;
        }
        Digest(out)
    }

    #[test]
    fn root_and_verify_agree() {
        let leaf = Digest([1,2,3,4,5,6,7,8]);
        let sib1 = Digest([9,10,11,12,13,14,15,16]);
        let sib2 = Digest([17,18,19,20,21,22,23,24]);
        let path = vec![sib1, sib2];

        let root = merkle_root_from_path(leaf, 3, &path, toy_hash_pair);
        assert!(merkle_verify_from_path(leaf, 3, &path, root, toy_hash_pair));
    }
}

```

We extracted the essence of the Merkle proof algorithm while removing RISC0-specific implementation details.

## Extraction to Lean and resolving Lean backend gaps

We successfully run extraction with: `cargo hax into lean`

**Core issue encountered**

The extracted Lean code referenced parts of the modeled Rust core library that were missing or incomplete in the Lean prelude, specifically:

- Core.Cmp (equality traits / operations)
- Core.Iter.Traits.* (iterator-based loops: into_iter + fold)
- generated trait boilerplate with AssociatedTypes

**Resolution**

We asked the hax maintainers Source: [Zulip](https://hacspec.zulipchat.com/#narrow/channel/269544-general/topic/hax.20.2B.20lean.20example/with/561950534)

Following guidance from hax maintainers (Zulip), we implemented a local compatibility layer by extending the vendored Hax Lean core model (Hax.Core) with minimal stubs matching the shapes expected by the extracted output. This enabled the extracted file to typecheck.

Key result: the extracted module now builds in our project: `lake build MerkleRootLean.Extracted.Merkle_root_rs`

## First proven theorems in Lean (Proof.lean)

**Theorem 1: `merkle_verify_is_pure_eq`**

Statement (informal): the extracted verification function is definitionally just:

- compute the Merkle root from the path, then
- compare it to the expected root.

This is important because it confirms the verification function contains no hidden behavior besides recomputation + comparison.

**Theorem 2: `merkle_verify_of_root_ok_is_true` (conditional acceptance lemma)**

Proves basic soundness of the algorithm:
- If we compute a root `r` via `merkle_root_from_path`
- And then verify the same root `r` via `merkle_verify_from_path`
- The result will always be `true`

Because the extracted code lives in the RustM monad (with ok/fail/div), the appropriate “acceptance” statement is conditional:

If merkle_root_from_path ... = RustM.ok r, then verifying with expected_root = r yields RustM.ok true.

Lean proof file compiles successfully

`lake build MerkleRootLean.Proof`

(Proof uses simp plus a simp-lemma for reflexivity of the modeled equality.)

```lean
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

```

## Notes from hax maintainers (Zulip)

Source (Zulip thread):
https://hacspec.zulipchat.com/#narrow/channel/269544-general/topic/hax.20.2B.20lean.20example/with/561950534

Key points from maintainers:

- Missing pieces of Core.* in Lean are expected right now; work is ongoing.
- Preferred workaround currently: define missing Core.* locally or patch extracted output.
- AssociatedTypes generation is intended.
- They are moving toward a new methodology: core models written in Rust and extracted to Lean, meaning hand-written Lean core models will likely be replaced soon (Lean-only PRs for core stubs are not a priority upstream).

## Current work summary (Stage 1 / Recon)

What we have:

- A small reproducible repo demonstrating Rust → hax → Lean extraction for a zkVM-relevant component.
- A local Lean compatibility layer enabling extracted code to typecheck (addressing missing Core.Cmp and Core.Iter shapes).
- Two basic machine-checked theorems about the extracted verification logic.

## Next steps (Stage 2 preparation)

- Replace hand-written Lean core stubs with the recommended approach:
        write minimal Rust “core models” (traits/APIs needed: equality + iteration) and extract them via hax.
- Strengthen the Merkle specification:
        model the Merkle root computation as a list fold spec and prove equivalence to the extracted implementation (once iterator semantics is modeled, not stubbed).
- Re-introduce ArkLib / CompPoly integration:
        treat hash_pair as an oracle (ArkLib-style) and connect extracted code to higher-level specs when feasible.


