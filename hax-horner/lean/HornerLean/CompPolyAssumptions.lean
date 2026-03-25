import HornerLean.Spec
import CompPoly.Multivariate.CMvPolynomialEvalLemmas

namespace HornerLean

/-
These are temporary assumptions to unblock the PoC.

They represent missing simp/grind/bridge lemmas that are needed for a clean proof
of Horner correctness against `CMvPolynomial.eval`.

Once these lemmas exist upstream in CompPoly (or are proved locally), the PoC can be made fully
proof-complete (no sorry/axiom).
-/

axiom eval_C_simp {n : ℕ} {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R]
  (vals : Fin n → R) (c : R) :
  (CPoly.CMvPolynomial.C (n := n) (R := R) c).eval vals = c

axiom eval_X_simp {n : ℕ} {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R]
  (vals : Fin n → R) (i : Fin n) :
  (CPoly.CMvPolynomial.X (n := n) (R := R) i).eval vals = vals i

-- Specialize the axioms to our HornerLean setting (n=1, R=ℤ)
@[simp] theorem evalAt_C (x c : ℤ) : evalAt x (C c) = c := by
  -- unfold evalAt/C and use eval_C_simp
  simp [HornerLean.evalAt, HornerLean.C, eval_C_simp]

@[simp] theorem evalAt_X0 (x : ℤ) : evalAt x X0 = x := by
  simp [HornerLean.evalAt, HornerLean.X0, eval_X_simp]

end HornerLean
