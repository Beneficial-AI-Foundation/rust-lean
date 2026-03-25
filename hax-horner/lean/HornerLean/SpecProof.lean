import HornerLean.Spec
import HornerLean.CompPolyAssumptions
import CompPoly.Multivariate.CMvPolynomialEvalLemmas

-- Horner spec over ℤ agrees with CompPoly eval ("math correctness on spec layer")

namespace HornerLean

-- Horner spec over ℤ
def hornerZ : List ℤ → ℤ → ℤ
| [],      _ => 0
| c :: cs, x => c + x * hornerZ cs x


-- I am having instances conflict HAdd
-- #check (inferInstance : HAdd P P P)
-- #check (inferInstance : HAdd P P (CPoly.Lawful (max 1 1) ℤ))

-- #check CPoly.Lawful.instHMulMaxNat
-- отключаем инстанс, который подменяет + на liftPoly
section
  attribute [-instance] CPoly.Lawful.instHAddMaxNat
  @[simp] theorem evalAt_add (x : ℤ) (p q : P) :
    evalAt x (p + q) = evalAt x p + evalAt x q := by
    simpa [evalAt] using (CPoly.eval_add (vals := fun _ => x) p q)
end

section
  @[simp] theorem evalAt_mul (x : ℤ) (p q : P) :
    evalAt x (p * q) = evalAt x p * evalAt x q := by
    sorry
end


theorem eval_polyOfCoeffs_eq_hornerZ (cs : List ℤ) (x : ℤ) :
    evalAt x (polyOfCoeffs cs) = hornerZ cs x := by
  induction cs with
  | nil =>
      -- evalAt x (C 0) = 0
      simp [polyOfCoeffs, hornerZ]
  | cons c cs ih =>
      simp [polyOfCoeffs, hornerZ]
      rw [evalAt_mul]
      simp
      rw [ih]
      simp

end HornerLean
