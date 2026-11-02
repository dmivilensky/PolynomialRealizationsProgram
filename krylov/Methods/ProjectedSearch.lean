import krylov.Methods.ProjectedModel

/-!
Article: main_krylov, lem:projected-residual, the normalized post-search residual.
Use: derive its √p bound from genuine old-image conjugacy and exact line search;
the constants use relative pair errors and never a minimum physical step size.
Source: finite Euclidean norm identities, Cauchy--Schwarz and the actual exact-search formula.
-/

namespace krylov.Methods
noncomputable section
open Matrix krylov.Reference
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {p : ℕ}

/-- A uniformly bounded finite coordinate vector has its dimension-square-root Euclidean bound.
Use: preserve the printed √p factor for projected line-search perturbations.
Article: main_krylov, lem:projected-residual.
Proof: sum the actual squared coordinate bounds and compare nonnegative squared norms. -/
theorem coordinate_norm_le_sqrt_card (v : Fin p → ℝ) {C : ℝ} (hC : 0≤C)
    (hv : ∀ i, |v i|≤C) : ‖WithLp.toLp 2 v‖≤Real.sqrt p*C := by
  -- Squaring keeps exactly p summands, without an entrywise-to-supremum-norm detour.
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hC)).mp
  rw [EuclideanSpace.real_norm_sq_eq, mul_pow, Real.sq_sqrt (Nat.cast_nonneg p)]
  calc
    _ ≤ ∑ _i : Fin p, C^2 := Finset.sum_le_sum fun i _ => by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hC).mpr (hv i)
    _ = _ := by simp

/-- Adding a zero coordinate preserves the genuine Euclidean norm.
Use: the reference old-window residual is embedded beside the exact zero line coordinate.
Article: main_krylov, lem:projected-residual.
Proof: the extra coordinate contributes zero to the finite sum of squares. -/
theorem coordinate_norm_zero_cons (v : Fin p → ℝ) :
    ‖WithLp.toLp 2 (Fin.cons (0 : ℝ) v : Fin (p+1) → ℝ)‖=‖WithLp.toLp 2 v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
    zero_pow (by decide : 2≠0), zero_add]

/-- Old-image conjugacy and a relative observed-pair error control the true new line pairing.
Use: no symmetry assumption is needed after the actual pair error has been bounded.
Article: main_krylov, lem:projected-residual, conjugacy identity in its proof.
Proof: subtract the identity operator and the observed image; the remaining
image pairing vanishes by actual conjugacy, and Cauchy--Schwarz bounds both errors. -/
theorem approximate_conjugacy_bound (s y v : E) (A : E →L[ℝ] E) (hs : ‖s‖=1)
    {ε η : ℝ} (hA : ‖A-ContinuousLinearMap.id ℝ E‖≤ε) (hy : ‖y-s‖≤η)
    (ho : inner ℝ y v=0) : |inner ℝ s (A v)|≤(ε+η)*‖v‖ := by
  -- The true pairing is split into operator drift and the actually observed secant discrepancy.
  have he : inner ℝ s (A v)=inner ℝ s ((A-ContinuousLinearMap.id ℝ E) v)+inner ℝ (s-y) v := by
    change inner ℝ s (A v)=inner ℝ s (A v-v)+inner ℝ (s-y) v
    rw [inner_sub_right, inner_sub_left, ho]
    ring
  have ha := norm_inner_le_norm (𝕜 := ℝ) s ((A-ContinuousLinearMap.id ℝ E) v)
  rw [Real.norm_eq_abs, hs, one_mul] at ha
  have hb := norm_inner_le_norm (𝕜 := ℝ) (s-y) v
  rw [Real.norm_eq_abs, norm_sub_rev s y] at hb
  rw [he]
  exact ((abs_add_le _ _).trans (add_le_add
    (ha.trans (((A-ContinuousLinearMap.id ℝ E).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right hA (norm_nonneg _)) ))
    (hb.trans (mul_le_mul_of_nonneg_right hy (norm_nonneg _))))).trans_eq (by ring)

/-- The exact implemented line search makes its actual post-search gradient orthogonal to its direction.
Use: discharges the zero current coordinate of the normalized augmented residual.
Article: main_krylov, lem:projected-residual, dᵀg′=0.
Proof: substitute the actual line-length quotient and cancel its nonzero curvature. -/
theorem searchedGradient_inner_zero (g d z : E) (hc : inner ℝ d z≠0) :
    inner ℝ d (searchedGradient g d z)=0 := by
  rw [searchedGradient, inner_add_right, real_inner_smul_right, lineLength, div_mul_cancel₀ _ hc]
  exact add_neg_cancel _

/-- Actual length normalization commutes with adjoining the new physical direction.
Use: identify the current and old coordinates of the genuine normalized augmented RFC window.
Article: main_krylov, lem:projected-residual, T=[V,d/‖d‖].
Proof: each index selects its own actual column and its own actual norm. -/
theorem unitWindow_cons (d : E) (s : Fin p → E) :
    unitWindow (Fin.cons d s)=Fin.cons (‖d‖⁻¹ • d) (unitWindow s) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [unitWindow, rescaleWindow, Fin.cons_zero]
  · simp only [unitWindow, rescaleWindow, Fin.cons_succ]

/-- The actual normalized post-search RFC residual has its printed old-residual plus √p perturbation bound.
Use: all hypotheses concern genuine observed old pairs and the actual current line operator.
Article: main_krylov, lem:projected-residual, ‖ρ‖≤R+C√pεt.
Proof: split off the old projected gradient with a zero current coordinate;
actual conjugacy bounds each old perturbation and exact search kills the current one. -/
theorem normalizedSearch_residual_bound (s y : Fin p → E) (hs : ∀ i, s i≠0)
    (A : E →L[ℝ] E) (g d : E) {ε η : ℝ} (hε : 0≤ε) (hη : 0≤η)
    (hA : ‖A-ContinuousLinearMap.id ℝ E‖≤ε) (hy : ∀ i, ‖y i-s i‖≤η*‖s i‖)
    (ho : ∀ i, inner ℝ (y i) d=0) (hc : inner ℝ d (A d)≠0) :
    ‖projectedResidual (unitWindow (Fin.cons d s)) (searchedGradient g d (A d))‖≤
      ‖projectedResidual (unitWindow s) g‖+
        Real.sqrt (p+1)*((ε+η)*‖lineLength g d (A d) • d‖) := by
  -- The perturbation vector uses the real searched gradient, including its exact current-coordinate zero.
  let r : Fin (p+1) → ℝ := Fin.cons 0 (coordinates (unitWindow s) g)
  let v : Fin (p+1) → ℝ := coordinates (unitWindow (Fin.cons d s)) (searchedGradient g d (A d))-r
  have hC : 0≤(ε+η)*‖lineLength g d (A d) • d‖ := mul_nonneg (add_nonneg hε hη) (norm_nonneg _)
  have hv (i : Fin (p+1)) : |v i|≤(ε+η)*‖lineLength g d (A d) • d‖ := by
    refine Fin.cases ?_ (fun j => ?_) i
    · change |coordinates (unitWindow (Fin.cons d s)) (searchedGradient g d (A d)) 0-0|≤_
      rw [unitWindow_cons]
      simp only [coordinates, Fin.cons_zero, real_inner_smul_left,
        searchedGradient_inner_zero g d (A d) hc, mul_zero, sub_self, abs_zero]
      exact hC
    · have hp := approximate_conjugacy_bound (unitWindow s j)
        (rescaleWindow y (fun k => ‖s k‖⁻¹) j) (lineLength g d (A d) • d) A
        (unitWindow_norm s hs j) hA (unitWindow_pair_error s y hs hy j) (by
          simp only [rescaleWindow, real_inner_smul_left, real_inner_smul_right, ho, mul_zero])
      change |coordinates (unitWindow (Fin.cons d s)) (searchedGradient g d (A d)) j.succ-
        coordinates (unitWindow s) g j|≤_
      rw [unitWindow_cons]
      simpa only [coordinates, Fin.cons_succ, searchedGradient, inner_add_right,
        real_inner_smul_right, map_smul, add_sub_cancel_left] using hp
  have hn := coordinate_norm_le_sqrt_card v hC hv
  have he : projectedResidual (unitWindow (Fin.cons d s)) (searchedGradient g d (A d))=
      WithLp.toLp 2 v+WithLp.toLp 2 r := by
    ext i
    change coordinates (unitWindow (Fin.cons d s)) (searchedGradient g d (A d)) i=
      (coordinates (unitWindow (Fin.cons d s)) (searchedGradient g d (A d)) i-r i)+r i
    ring
  rw [he]
  have hr : ‖WithLp.toLp 2 r‖=‖projectedResidual (unitWindow s) g‖ := coordinate_norm_zero_cons _
  exact ((norm_add_le _ _).trans (add_le_add hn hr.le)).trans_eq (by rw [Nat.cast_add, Nat.cast_one]; ring)

end
end krylov.Methods
