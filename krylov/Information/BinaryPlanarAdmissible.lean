import krylov.Information.BinaryPlanarModel
import krylov.Tensor.BinaryPlanarSlices

/-!
Article: main_krylov, thm:H, the full compatible planar source class.
Use: retain every actual binary tensor in the genuine ball and every unknown
rank-one base beta in the original interval. Derive all source budgets in
that actual base, including the exact 1/(1-b) normalization factor.
Source: the proved binary Banach slice bound and genuine Loewner budget transfer.
-/

namespace krylov.Information
noncomputable section
open Real Matrix Finset krylov.Tensor krylov.Tensor.BinaryCubic krylov.Secant
  krylov.Reference krylov.LinearAlgebra krylov.Correction krylov.Methods
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator MatrixOrder
variable {n : ℕ}

/-- The full compatible binary planar source, with an independent unknown base coefficient.
Article: main_krylov, thm:H, the original planar model with |beta|<=e_c.
The two midpoint increments and final slice come from the same actual tensor. -/
def binaryPlanarScenario (e h : EuclideanSpace ℝ (Fin n)) (κ r β : ℝ)
    (N : ℕ) (t : BinaryCubic) : Scenario n where
  base := 1 + planarMatrix e h 0 0 β
  increment j :=
    (if j=0 then κ • planarMatrix e h t.t0 t.t1 t.t2 else 0) +
      (if j=N-1 then (κ*r) • planarMatrix e h t.t1 t.t2 t.t3 else 0)
  terminal := (κ*r) • planarMatrix e h t.t1 t.t2 t.t3
  correction := 0

/-- Every actual binary-ball tensor and every allowed hidden base produce a genuinely admissible source scenario.
Article: main_krylov, thm:H, full planar uncertainty before optimizing RFC.
All relative budgets are computed in the same true unknown base. -/
theorem binaryPlanarScenario_admissible (e h : EuclideanSpace ℝ (Fin n))
    (he : ‖e‖=1) (hh : ‖h‖=1) (heh : inner ℝ e h=0)
    (κ r β b : ℝ) (hκ : 0 ≤ κ) (hr : 0 ≤ r) (hb : 0 ≤ b) (hb₁ : b < 1)
    (hβ : |β| ≤ b) (N : ℕ) (t : BinaryCubic) (ht : t.InBall) :
    (binaryPlanarScenario e h κ r β N t).Admissible N 1 b
      (fun j => binaryFirstLast N κ (κ*r) j / (1-b)) (κ*r/(1-b)) 0 := by
  let S := binaryPlanarScenario e h κ r β N t
  have hc : 0 < 1-b := by linarith
  have hbase : ‖S.base-1‖ ≤ b := by
    have heq : S.base-1=planarMatrix h e β 0 0 := by
      simp only [S, binaryPlanarScenario, planarMatrix, zero_smul, zero_add, add_zero]
      abel
    rw [heq, planar_diagonal_norm h e hh]
    exact hβ
  have hbaseSym : S.base.IsSymm := Matrix.isSymm_one.add (planarMatrix_isSymm _ _ _ _ _)
  have hdom := relative_displacement_base (1 : Matrix (Fin n) (Fin n) ℝ) S.base Matrix.PosDef.one
    hbaseSym hb hb₁ (by rw [relativeBudget_one]; exact hbase)
  have hchange (E : Matrix (Fin n) (Fin n) ℝ) (hE : E.IsSymm) (w : ℝ) (hw : 0 ≤ w)
      (hEn : ‖E‖ ≤ w) : relativeBudget S.base E ≤ w/(1-b) := by
    apply relative_budget_change 1 S.base E Matrix.PosDef.one hdom.2.2 hE hc.le
      (div_nonneg hw hc.le) hdom.1
    rw [relativeBudget_one]
    have heq : (1-b)*(w/(1-b)) = w := by field_simp
    rw [heq]
    exact hEn
  have hslices := endpoint_slice_norms ht e h he hh heh
  have hinc (j : ℕ) : (S.increment j).IsSymm ∧ ‖S.increment j‖ ≤ binaryFirstLast N κ (κ*r) j := by
    have h0 : ‖κ • planarMatrix e h t.t0 t.t1 t.t2‖ ≤ κ := by
      rw [norm_smul, Real.norm_of_nonneg hκ]
      exact (mul_le_mul_of_nonneg_left hslices.1 hκ).trans_eq (mul_one _)
    have h1 : ‖(κ*r) • planarMatrix e h t.t1 t.t2 t.t3‖ ≤ κ*r := by
      rw [norm_smul, Real.norm_of_nonneg (mul_nonneg hκ hr)]
      exact (mul_le_mul_of_nonneg_left hslices.2 (mul_nonneg hκ hr)).trans_eq (mul_one _)
    constructor
    · dsimp only [S, binaryPlanarScenario]
      apply Matrix.IsSymm.add
      · by_cases hj : j=0
        · simpa only [ite_eq_left hj] using (planarMatrix_isSymm e h t.t0 t.t1 t.t2).smul κ
        · simpa only [ite_eq_right hj] using (Matrix.isSymm_zero : (0 : Matrix (Fin n) (Fin n) ℝ).IsSymm)
      · by_cases hj : j=N-1
        · simpa only [ite_eq_left hj] using (planarMatrix_isSymm e h t.t1 t.t2 t.t3).smul (κ*r)
        · simpa only [ite_eq_right hj] using (Matrix.isSymm_zero : (0 : Matrix (Fin n) (Fin n) ℝ).IsSymm)
    · change ‖(if j=0 then κ • planarMatrix e h t.t0 t.t1 t.t2 else 0) +
        (if j=N-1 then (κ*r) • planarMatrix e h t.t1 t.t2 t.t3 else 0)‖ ≤ _
      apply (norm_add_le _ _).trans
      dsimp only [binaryFirstLast]
      apply add_le_add
      · split_ifs <;> first | exact h0 | simp only [norm_zero, le_refl]
      · split_ifs <;> first | exact h1 | simp only [norm_zero, le_refl]
  refine ⟨hdom.2.2, ?_, ?_, (planarMatrix_isSymm _ _ _ _ _).smul (κ*r), ?_, ?_⟩
  · rw [relativeBudget_one]
    exact hbase
  · intro j _
    refine ⟨(hinc j).1, hchange _ (hinc j).1 _ ?_ (hinc j).2⟩
    exact (norm_nonneg _).trans (hinc j).2
  · apply hchange _ ((planarMatrix_isSymm _ _ _ _ _).smul (κ*r)) _ (mul_nonneg hκ hr)
    change ‖(κ*r) • planarMatrix e h t.t1 t.t2 t.t3‖ ≤ κ*r
    rw [norm_smul, Real.norm_of_nonneg (mul_nonneg hκ hr)]
    exact (mul_le_mul_of_nonneg_left hslices.2 (mul_nonneg hκ hr)).trans_eq (mul_one _)
  · intro j _
    refine ⟨Matrix.isSymm_zero, ?_⟩
    change relativeBudget S.base (0 : Matrix (Fin n) (Fin n) ℝ) ≤ 0
    simp [relativeBudget, relativeOperator, chebyshev1.opNorm]

/-- The full compatible binary planar source has the same genuine individual budgets in the original physical coordinates.
Article: main_krylov, thm:H, the actual unknown-base physical model. -/
theorem physical_binaryPlanarScenario_admissible (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (e h : EuclideanSpace ℝ (Fin n)) (he : ‖e‖=1) (hh : ‖h‖=1) (heh : inner ℝ e h=0)
    (κ r β b : ℝ) (hκ : 0 ≤ κ) (hr : 0 ≤ r) (hb : 0 ≤ b) (hb₁ : b < 1)
    (hβ : |β| ≤ b) (N : ℕ) (t : BinaryCubic) (ht : t.InBall) :
    ((binaryPlanarScenario e h κ r β N t).inPhysical (metricRoot A)⁻¹).Admissible N A b
      (fun j => binaryFirstLast N κ (κ*r) j / (1-b)) (κ*r/(1-b)) 0 := by
  have hS := binaryPlanarScenario_admissible e h he hh heh κ r β b hκ hr hb hb₁ hβ N t ht
  have hb' := Scenario.inPhysical_admissible _ N 1 (metricRoot A)⁻¹ Matrix.PosDef.one
    (Matrix.isUnit_nonsing_inv_det _ (metricRoot_det_unit A hA)) b _ _ 0 hS
  simpa only [inverseRootForm_one A hA] using hb'

end
end krylov.Information
