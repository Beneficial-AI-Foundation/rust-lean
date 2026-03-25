// ported from https://github.com/risc0/risc0/blob/2e73cb82cadfbad9190b2b34f124481c9b57d371/risc0/zkvm/src/receipt/merkle.rs

// we create minimal types + function MerkleProof::root.

// for good extraction with Hax we also should
//     1. Create type Digest locally (for example, struct Digest([u32; 8]) just like in RISC0 tests);
//     2. Pass the hash as a function parameter: `hash_pair: fn(&Digest, &Digest) -> Digest` (or as a generic `H: HashPair`).

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
