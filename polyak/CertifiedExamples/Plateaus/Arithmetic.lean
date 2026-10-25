import chebyshev2.Numerics.IntervalExpr
import polyak.CertifiedExamples.Plateaus.Polynomial

/-! Executable arithmetic expressions with independently proved source
semantics.  No expression graph is accepted from the archive. -/
namespace polyak.CertifiedExamples.Plateaus
open scoped Polynomial
open chebyshev2.Numerics

abbrev E (d : ℕ) := IntervalExpr d

def cst {d : ℕ} (r : ℚ) : E d := .literal r
def plus {d : ℕ} (a b : E d) : E d := .add a b
def minus {d : ℕ} (a b : E d) : E d := .add a (.neg b)
def times {d : ℕ} (a b : E d) : E d := .mul a b
def divideE {d : ℕ} (a b : E d) : E d := .mul a (.inverse b)
def square {d : ℕ} (a : E d) : E d := .power a 2

noncomputable def rawXi (y β κ c : ℝ) : ℝ :=
  let x := y/κ
  let A := 1+β-(x+y)/2
  let B := (y-x)/2
  (B^2-(1-β)^2-A^2+2*A*(1+β)*c-4*β*c^2)/(2*B*(1-β))

def tExpr {d : ℕ} (c : E d) : ℕ → E d
  | 0 => cst 1
  | 1 => c
  | n+2 => minus (times (times (cst 2) c) (tExpr c (n+1))) (tExpr c n)

def uExpr {d : ℕ} (c : E d) : ℕ → E d
  | 0 => cst 1
  | 1 => times (cst 2) c
  | n+2 => minus (times (times (cst 2) c) (uExpr c (n+1))) (uExpr c n)

noncomputable section
open General Levels

theorem rawXi_actual (q : Tuning) (c : ℝ) :
    rawXi q.y q.beta q.kappa c=q.Xi c := rfl

theorem tExpr_value {d : ℕ} (c : E d) (v : Fin d → ℝ) (n : ℕ) :
    (tExpr c n).value v=Spectral.chebT n (c.value v) := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [tExpr,cst,IntervalExpr.value,Spectral.chebT]
  | one => norm_num [tExpr,IntervalExpr.value,Spectral.chebT]
  | more n ih₀ ih₁ =>
    have h := congrArg (fun p : ℝ[X] => p.eval (c.value v))
      (Polynomial.Chebyshev.T_add_two ℝ (n : ℤ))
    simpa only [tExpr,minus,times,cst,IntervalExpr.value,ih₀,ih₁,
      Spectral.chebT,Polynomial.eval_sub,Polynomial.eval_mul,
      Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_add,Polynomial.eval_neg,Rat.cast_ofNat,
      Int.cast_natCast,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,sub_eq_add_neg] using h.symm

theorem uExpr_value {d : ℕ} (c : E d) (v : Fin d → ℝ) (n : ℕ) :
    (uExpr c n).value v=Spectral.chebU n (c.value v) := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [uExpr,cst,IntervalExpr.value,Spectral.chebU]
  | one => norm_num [uExpr,times,cst,IntervalExpr.value,Spectral.chebU]
  | more n ih₀ ih₁ =>
    have h := congrArg (fun p : ℝ[X] => p.eval (c.value v))
      (Polynomial.Chebyshev.U_add_two ℝ (n : ℤ))
    simpa only [uExpr,minus,times,cst,IntervalExpr.value,ih₀,ih₁,
      Spectral.chebU,Polynomial.eval_sub,Polynomial.eval_mul,
      Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_add,Polynomial.eval_neg,Rat.cast_ofNat,
      Int.cast_natCast,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,sub_eq_add_neg] using h.symm

def xiNumerator (y β κ c : ℝ) : ℝ :=
  κ*((y-1-β)*(1+β)-(1-β)^2)-y*(y-1-β)+
    ((κ*(2+2*β-y)-y)*(1+β))*c-4*β*κ*c^2

def xiDenominator (y β κ : ℝ) : ℝ := y*(κ-1)*(1-β)

theorem xiNumerator_actual (q : Tuning) (c : ℝ) :
    xiNumerator q.y q.beta q.kappa c =
      xiDenominator q.y q.beta q.kappa * q.Xi c := by
  have hκ := q.kappa_pos.ne'
  have hβ : 1-q.beta ≠ 0 := sub_ne_zero.mpr q.beta_lt_one.ne'
  unfold Tuning.Xi
  rw [← mul_div_assoc]
  apply (eq_div_iff (mul_ne_zero (mul_ne_zero (by norm_num) q.B_ne_zero) hβ)).mpr
  unfold xiNumerator xiDenominator Tuning.B Tuning.A Tuning.x
  field_simp [hκ]
  ring

def numeratorLag (y β κ : ℝ) (n : ℤ) (c : ℝ) : ℝ :=
  xiNumerator y β κ c*(1-Spectral.chebT n.natAbs c)-
    xiDenominator y β κ*(n.sign : ℝ)*(1-c^2)*Spectral.chebU (n.natAbs-1) c

theorem numeratorLag_actual (q : Tuning) (n : ℤ) (c : ℝ) :
    numeratorLag q.y q.beta q.kappa n c =
      xiDenominator q.y q.beta q.kappa * Farey.Certificates.signedLagPolynomial q n c := by
  unfold numeratorLag Farey.Certificates.signedLagPolynomial
  rw [xiNumerator_actual]
  ring

def xiNumeratorExpr {d : ℕ} (y β : ℚ) (κ c : E d) : E d :=
  minus
    (plus (minus (times κ (cst ((y-1-β)*(1+β)-(1-β)^2)))
      (cst (y*(y-1-β))))
      (times (times (minus (times κ (cst (2+2*β-y))) (cst y)) (cst (1+β))) c))
    (times (times (cst (4*β)) κ) (square c))

def xiDenominatorExpr {d : ℕ} (y β : ℚ) (κ : E d) : E d :=
  times (times (cst y) (minus κ (cst 1))) (cst (1-β))

def numeratorLagExpr {d : ℕ} (y β : ℚ) (κ c : E d) (n : ℤ) : E d :=
  minus (times (xiNumeratorExpr y β κ c) (minus (cst 1) (tExpr c n.natAbs)))
    (times (times (times (xiDenominatorExpr y β κ) (cst n.sign))
      (minus (cst 1) (square c))) (uExpr c (n.natAbs-1)))

theorem xiNumeratorExpr_value {d : ℕ} (y β : ℚ) (κ c : E d) (v : Fin d → ℝ) :
    (xiNumeratorExpr y β κ c).value v =
      xiNumerator y β (κ.value v) (c.value v) := by
  norm_num [xiNumeratorExpr,xiNumerator,cst,plus,minus,times,square,IntervalExpr.value]
  ring

theorem xiDenominatorExpr_value {d : ℕ} (y β : ℚ) (κ : E d) (v : Fin d → ℝ) :
    (xiDenominatorExpr y β κ).value v = xiDenominator y β (κ.value v) := by
  simp [xiDenominatorExpr,xiDenominator,cst,minus,times,IntervalExpr.value,sub_eq_add_neg]

theorem numeratorLagExpr_value {d : ℕ} (y β : ℚ) (κ c : E d) (n : ℤ)
    (v : Fin d → ℝ) :
    (numeratorLagExpr y β κ c n).value v =
      numeratorLag y β (κ.value v) n (c.value v) := by
  simp only [numeratorLagExpr,numeratorLag,minus,times,cst,square,IntervalExpr.value,
    xiNumeratorExpr_value,xiDenominatorExpr_value,tExpr_value,uExpr_value,
    Rat.cast_intCast,Rat.cast_one,sub_eq_add_neg]

end
end polyak.CertifiedExamples.Plateaus
