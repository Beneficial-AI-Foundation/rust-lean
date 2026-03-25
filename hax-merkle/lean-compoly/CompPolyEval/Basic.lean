import CompPoly.Multivariate.CMvPolynomial
import CompPoly.Multivariate.MvPolyEquiv
import CompPoly.Multivariate.Lawful

namespace CompPolyEval

abbrev P := CPoly.CMvPolynomial 1 ℤ

-- constant polynomial 3 in 1 variable ring
def pConst : P := (CPoly.Lawful.C (n := 1) (R := ℤ) 3)

-- X_0 lives in 1-variable ring, and Lawful.X 0 has type Lawful 1 ℤ
def X0 : P := (CPoly.Lawful.X 0)

def p : P := pConst + (CPoly.Lawful.C (n := 1) (R := ℤ) 2) * X0

#check p

end CompPolyEval
