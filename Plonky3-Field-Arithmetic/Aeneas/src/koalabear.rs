use crate::monty_31::{MontyParameters, MontyField31};

/// The prime field `2^31 - 2^24 + 1`, a.k.a. the Koala Bear field.
pub type KoalaBear = MontyField31<KoalaBearParameters>;

#[derive(Copy, Clone, Default, Debug, Eq, Hash, PartialEq)]
pub struct KoalaBearParameters;

impl MontyParameters for KoalaBearParameters {
    /// The KoalaBear prime: 2^31 - 2^24 + 1
    /// This is a 31-bit prime with the highest possible two adicity if we additionally demand that
    /// the cube map (x -> x^3) is an automorphism of the multiplicative group.
    /// It's not unique, as there is one other option with equal 2 adicity: 2^30 + 2^27 + 2^24 + 1.
    /// There is also one 29-bit prime with higher two adicity which might be appropriate for some applications: 2^29 - 2^26 + 1.
    const PRIME: u32 = 0x7f000001;

    const MONTY_BITS: u32 = 32;
    const MONTY_MU: u32 = 0x81000001;
}
