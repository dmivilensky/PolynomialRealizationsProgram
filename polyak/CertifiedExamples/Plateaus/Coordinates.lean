import polyak.CertifiedExamples.Plateaus.Kernels

/-! Polynomial coordinates for all finite checks. Xi coefficients and cosine
coordinates are independent interval variables; their membership is proved
separately from the scalar kappa bracket and the actual rational angles. -/
noncomputable section
namespace polyak.CertifiedExamples.Plateaus
open General Levels Matrix chebyshev2.Numerics
open scoped BigOperators

def coefficientValue (X : Fin 3 → ℝ) (c : ℝ) : ℝ := X 0+X 1*c+X 2*c^2

def sourceCoefficients (y β κ : ℝ) : Fin 3 → ℝ :=
  ![xiNumerator y β κ 0/xiDenominator y β κ,
    ((κ*(2+2*β-y)-y)*(1+β))/xiDenominator y β κ,
    (-4*β*κ)/xiDenominator y β κ]

theorem sourceCoefficients_actual (q : Tuning) (c : ℝ) :
    coefficientValue (sourceCoefficients q.y q.beta q.kappa) c=q.Xi c := by
  have hd : xiDenominator q.y q.beta q.kappa ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero q.y_pos.ne' (sub_ne_zero.mpr q.kappa_gt_one.ne'))
      (sub_ne_zero.mpr q.beta_lt_one.ne')
  apply (mul_left_cancel₀ hd)
  rw [← xiNumerator_actual]
  dsimp [coefficientValue,sourceCoefficients]
  field_simp [hd]
  unfold xiNumerator
  ring

def coordinateLag (X : Fin 3 → ℝ) (n : ℤ) (c : ℝ) : ℝ :=
  coefficientValue X c*(1-Spectral.chebT n.natAbs c)-
    (n.sign:ℝ)*(1-c^2)*Spectral.chebU (n.natAbs-1) c

def coordinateMatrix {d : ℕ} (X : Fin 3 → ℝ) (reps : Fin d → ℤ) (c : Fin d → ℝ) :
    Matrix (Fin d) (Fin d) ℝ := Matrix.of (fun r i => coordinateLag X (reps r) (c i))

theorem coordinateLag_actual (q : Tuning) (n : ℤ) (c : ℝ) :
    coordinateLag (sourceCoefficients q.y q.beta q.kappa) n c =
      Farey.Certificates.signedLagPolynomial q n c := by
  unfold coordinateLag Farey.Certificates.signedLagPolynomial
  rw [sourceCoefficients_actual]

def coefficientValueExpr {d : ℕ} (X : Fin 3 → E d) (c : E d) : E d :=
  plus (plus (X 0) (times (X 1) c)) (times (X 2) (square c))

def coordinateLagExpr {d : ℕ} (X : Fin 3 → E d) (n : ℤ) (c : E d) : E d :=
  minus (times (coefficientValueExpr X c) (minus (cst 1) (tExpr c n.natAbs)))
    (times (times (cst n.sign) (minus (cst 1) (square c))) (uExpr c (n.natAbs-1)))

theorem coefficientValueExpr_value {d : ℕ} (X : Fin 3 → E d) (c : E d)
    (v : Fin d → ℝ) :
    (coefficientValueExpr X c).value v=coefficientValue (fun i=>(X i).value v) (c.value v) := by
  rfl

theorem coordinateLagExpr_value {d : ℕ} (X : Fin 3 → E d) (n : ℤ) (c : E d)
    (v : Fin d → ℝ) :
    (coordinateLagExpr X n c).value v=coordinateLag (fun i=>(X i).value v) n (c.value v) := by
  simp only [coordinateLagExpr,coordinateLag,minus,times,cst,square,IntervalExpr.value,
    coefficientValueExpr_value,tExpr_value,uExpr_value,Rat.cast_intCast,Rat.cast_one,
    sub_eq_add_neg]

end polyak.CertifiedExamples.Plateaus
