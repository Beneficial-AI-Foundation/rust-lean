-- As of hax PR #1880 (Lean 4.26.0), both Core_models.Option.Option and
-- Rust_primitives.Hax.Machine_int are already correctly capitalised in the
-- Hax library, so no aliases are needed.  This file is kept as an import
-- shim so that p3_fri_kernel.lean does not need to be regenerated.
import Hax
