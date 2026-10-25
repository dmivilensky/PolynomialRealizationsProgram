import polyak.CertifiedExamples.Plateaus.Arithmetic
import polyak.Numerics.Root

/-! The selected boundary equation is a polynomial determinant in kappa.
Its entries are the numerators of the actual original lag functions. -/
noncomputable section
namespace polyak.CertifiedExamples.Plateaus
open General Levels Matrix chebyshev2.Numerics

def sourceMatrix {d : ℕ} (y β κ : ℝ) (n : Fin d → ℤ) (c : Fin d → ℝ) :
    Matrix (Fin d) (Fin d) ℝ := fun r i => numeratorLag y β κ (n r) (c i)

def determinant18 (κ : ℝ) : ℝ :=
  (sourceMatrix (2201327/1000000) (1567/2500) κ ![1,-4]
    ![Real.cos (2*Real.pi*3/18),Real.cos (2*Real.pi*4/18)]).det

def determinant21 (κ : ℝ) : ℝ :=
  (sourceMatrix (89631/40000) (769/1250) κ ![1,-12,-4]
    ![Real.cos (2*Real.pi*3/21),Real.cos (2*Real.pi*4/21),
      Real.cos (2*Real.pi*5/21)]).det

theorem continuous_sourceDeterminant {d : ℕ} (y β : ℝ)
    (n : Fin d → ℤ) (c : Fin d → ℝ) :
    Continuous (fun κ => (sourceMatrix y β κ n c).det) := by
  apply Continuous.matrix_det
  apply continuous_pi
  intro r
  apply continuous_pi
  intro i
  unfold sourceMatrix numeratorLag xiNumerator xiDenominator
  fun_prop

theorem continuous_determinant18 : Continuous determinant18 :=
  continuous_sourceDeterminant _ _ _ _

theorem continuous_determinant21 : Continuous determinant21 :=
  continuous_sourceDeterminant _ _ _ _

theorem sourceMatrix_actual {d : ℕ} (q : Tuning) (n : Fin d → ℤ)
    (c : Fin d → ℝ) :
    sourceMatrix q.y q.beta q.kappa n c =
      xiDenominator q.y q.beta q.kappa •
        (fun r i => Farey.Certificates.signedLagPolynomial q (n r) (c i)) := by
  ext r i
  exact numeratorLag_actual q (n r) (c i)

def det2Expr {d : ℕ} (m : Fin 2 → Fin 2 → E d) : E d :=
  minus (times (m 0 0) (m 1 1)) (times (m 0 1) (m 1 0))

def det3Expr {d : ℕ} (m : Fin 3 → Fin 3 → E d) : E d :=
  plus (plus
    (times (m 0 0) (minus (times (m 1 1) (m 2 2)) (times (m 1 2) (m 2 1))))
    (times (m 0 1) (minus (times (m 1 2) (m 2 0)) (times (m 1 0) (m 2 2)))))
    (times (m 0 2) (minus (times (m 1 0) (m 2 1)) (times (m 1 1) (m 2 0))))

theorem det2Expr_value {d : ℕ} (m : Fin 2 → Fin 2 → E d) (v : Fin d → ℝ) :
    (det2Expr m).value v=Matrix.det (Matrix.of (fun i j => (m i j).value v)) := by
  rw [Matrix.det_fin_two]
  simp only [det2Expr,minus,times,IntervalExpr.value,Matrix.of_apply,sub_eq_add_neg]

theorem det3Expr_value {d : ℕ} (m : Fin 3 → Fin 3 → E d) (v : Fin d → ℝ) :
    (det3Expr m).value v=Matrix.det (Matrix.of (fun i j => (m i j).value v)) := by
  rw [Matrix.det_fin_three]
  simp only [det3Expr,plus,minus,times,IntervalExpr.value,Matrix.of_apply]
  ring

def determinant18Expr (κ : ℚ) : E 2 :=
  det2Expr (fun r i => numeratorLagExpr (2201327/1000000) (1567/2500)
    (cst κ) (.variable i) ((![1,-4] : Fin 2 → ℤ) r))

def determinant21Expr (κ : ℚ) : E 3 :=
  det3Expr (fun r i => numeratorLagExpr (89631/40000) (769/1250)
    (cst κ) (.variable i) ((![1,-12,-4] : Fin 3 → ℤ) r))

theorem determinant18Expr_value (κ : ℚ) :
    (determinant18Expr κ).value
      ![Real.cos (2*Real.pi*3/18),Real.cos (2*Real.pi*4/18)] = determinant18 κ := by
  rw [determinant18Expr,det2Expr_value]
  unfold determinant18 sourceMatrix
  congr 1
  funext r i
  simp only [Matrix.of_apply]
  rw [numeratorLagExpr_value]
  norm_num [cst,IntervalExpr.value]

theorem determinant21Expr_value (κ : ℚ) :
    (determinant21Expr κ).value
      ![Real.cos (2*Real.pi*3/21),Real.cos (2*Real.pi*4/21),Real.cos (2*Real.pi*5/21)] =
      determinant21 κ := by
  rw [determinant21Expr,det3Expr_value]
  unfold determinant21 sourceMatrix
  congr 1
  funext r i
  simp only [Matrix.of_apply]
  rw [numeratorLagExpr_value]
  norm_num [cst,IntervalExpr.value]

theorem polynomial_root_from_opposite_signs {f : ℝ → ℝ} (hf : Continuous f)
    {a b : ℝ} (hab : a ≤ b) (h : f a < 0 ∧ 0 < f b ∨ f b < 0 ∧ 0 < f a) :
    ∃ κ ∈ Set.Icc a b, f κ=0 := by
  rcases h with h | h
  · exact intermediate_value_Icc hab hf.continuousOn ⟨h.1.le,h.2.le⟩
  · exact intermediate_value_Icc' hab hf.continuousOn ⟨h.1.le,h.2.le⟩

end polyak.CertifiedExamples.Plateaus
