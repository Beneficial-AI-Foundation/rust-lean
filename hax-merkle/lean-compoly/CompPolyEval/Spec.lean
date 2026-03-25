import CompPoly.Multivariate.CMvPolynomial
import CompPoly.Multivariate.Lawful

namespace CompPolyEval

abbrev P := CPoly.CMvPolynomial 1 ℤ

def x0 : Fin 1 := ⟨0, by decide⟩
def X0 : P := CPoly.Lawful.X 0

def evalAt (x : ℤ) (p : P) : ℤ :=
  CPoly.CMvPolynomial.eval (R := ℤ) (n := 1) (fun (_ : Fin 1) => x) p

def polyOfCoeffs : List ℤ → P
| []      => (CPoly.Lawful.C (n := 1) (R := ℤ) 0)
| c :: cs => (CPoly.Lawful.C (n := 1) (R := ℤ) c) + X0 * polyOfCoeffs cs

end CompPolyEval
