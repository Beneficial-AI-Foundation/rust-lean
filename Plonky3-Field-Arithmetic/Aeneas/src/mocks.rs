
// We're currently using this mock because the provided
// Aeneas model for `Hasher` doesn't contain `write_u32`
// Mocking core::hash::Hasher
pub trait Hasher {
    fn finish(&self) -> u64;

    fn write(&mut self, bytes: &[u8]);

    /// Writes a single `u32` into this hasher.
    #[inline]
    fn write_u32(&mut self, i: u32) {
        self.write(&i.to_ne_bytes())
    }
}

// Mocking core::hash::Hash
pub trait Hash: // marker::PointeeSized
{
    fn hash<H: Hasher>(&self, state: &mut H);
}
