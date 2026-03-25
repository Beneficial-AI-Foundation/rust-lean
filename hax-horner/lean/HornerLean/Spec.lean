import CompPoly.Multivariate.CMvPolynomial

namespace HornerLean

/-- One-variable polynomial ring over ℤ. -/
abbrev P := CPoly.CMvPolynomial 1 ℤ

/-- The single variable X₀ in a 1-variable ring. -/
def X0 : P :=
  CPoly.CMvPolynomial.X (n := 1) (R := ℤ) ⟨0, by decide⟩

/-- Constant polynomial constructor. -/
def C (c : ℤ) : P :=
  CPoly.CMvPolynomial.C (n := 1) (R := ℤ) c

/-- Evaluate a polynomial at a point `x` (we use the constant assignment `Fin 1 → ℤ`). -/
def evalAt (x : ℤ) (p : P) : ℤ :=
  CPoly.CMvPolynomial.eval (R := ℤ) (n := 1) (fun (_ : Fin 1) => x) p

/--
Build a polynomial from coefficients in Horner form:
`polyOfCoeffs [c0, c1, c2, ...] = c0 + X0 * (c1 + X0 * (c2 + ...))`.
-/
def polyOfCoeffs : List ℤ → P
| []      => C 0
| c :: cs => C c + X0 * polyOfCoeffs cs

end HornerLean
