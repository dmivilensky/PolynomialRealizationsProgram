import krylov.Information.KnownBaseRadius
import krylov.Correction.InformedScalar

/-!
Article: main_krylov, thm:C2(c), actual spectral known-base lower witnesses.
Use: the sharp informed coefficient is forced by genuine admissible
one-increment fixed-base physical source scenarios and true method outputs.
Source: exact symmetric planar contraction, actual complete data fibre and
the proved attained scalar maximum t(1−t²)=2/(3√3).
-/

namespace krylov.Information
noncomputable section
open Matrix Filter Asymptotics Topology Finset krylov.Reference krylov.Secant
  krylov.Correction krylov.Methods krylov.LinearAlgebra krylov.Stability
open scoped BigOperators MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- A genuine planar completion at either scalar consistency-interval endpoint is a spectral contraction, including the degenerate boundary.
Use: prove the exact unit budgets of the informed-base signed lower matrices rather than infer them from a Frobenius bound.
Article: main_krylov, thm:C2(c), (±(1−a²),a;a,0) has spectral norm at most one.
Proof: the missing squared output energy is exactly (1−a²)(ap−σq)²
in the true orthonormal plane. It is nonnegative, and the actual two-unit
Bessel inequality bounds the input's two-coordinate energy by its full norm.
-/
theorem planar_endpoint_norm_le (e f : EuclideanSpace ℝ (Fin n))
    (he : ‖e‖=1) (hf : ‖f‖=1) (hef : inner ℝ e f=0)
    (a σ : ℝ) (ha : a^2≤1) (hσ : σ^2=1) :
    ‖planarMatrix e f (σ*(1-a^2)) a 0‖≤1 := by
  -- Verify the genuine physical action on every input, including directions outside the attaining plane.
  rw [Matrix.cstar_norm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num : (0 : ℝ)≤1)
  intro v
  rw [one_mul]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [planarMatrix_action,planar_coordinates_norm_sq e f he hf hef]
  let p := inner ℝ e v
  let q := inner ℝ f v
  have hgap : p^2+q^2-((σ*(1-a^2)*p+a*q)^2+(a*p+0*q)^2)=
      (1-a^2)*(a*p-σ*q)^2 := by
    linear_combination -((1-a^2)^2*p^2+(1-a^2)*q^2)*hσ
  have hnonneg : 0≤(1-a^2)*(a*p-σ*q)^2 := mul_nonneg (by linarith) (sq_nonneg _)
  have hb := two_unit_bessel e f v he hf hef
  change _≤‖v‖^2
  dsimp only [p,q] at hgap hnonneg
  nlinarith

/-- Every original spectral profile has actual admissible fixed-base signed planar physical scenarios whenever their genuine unit planar form obeys the source norm budget.
Use: reuse one concrete physical admissibility bridge for the sharp informed lower pair and all zero-budget cases.
Article: main_krylov, thm:C2(c), primitive fixed-base spectral admissibility.
Proof: each true canonical increment is its nonnegative primitive budget
times the same genuine unit spectral form. The terminal rank-one budget is
exact and intermediate defects vanish. Actual inverse-root congruence
preserves all source budgets and maps the base identity exactly to A.
-/
theorem knownBasePlanarScenario_spectral_admissible
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (e f : EuclideanSpace ℝ (Fin n)) (he : ‖e‖=1)
    (ω : ℕ → ℝ) (w τ r : ℝ) (N : ℕ) (hω : ∀ i<N, 0≤ω i)
    (hw : 0≤w) (hτ : 0≤τ) (hr : 0≤r)
    (a γ σ : ℝ) (hσ : σ^2=1) (hP : ‖planarMatrix e f (σ*γ) a 0‖≤1) :
    ((knownBasePlanarScenario e f (fun i => a*ω i) (fun i => γ*ω i) w σ).inPhysical (metricRoot A)⁻¹).Admissible N A r ω w τ := by
  -- Prove every original primitive budget before the genuine physical transport.
  let S := knownBasePlanarScenario e f (fun i => a*ω i) (fun i => γ*ω i) w σ
  have hσabs : |σ|=1 := by nlinarith [sq_abs σ,abs_nonneg σ]
  have hS : S.Admissible N 1 r ω w τ := by
    refine ⟨Matrix.PosDef.one,?_,?_,planarMatrix_isSymm _ _ _ _ _,?_,?_⟩
    · simpa only [S,knownBasePlanarScenario,sub_self,relativeBudget_one,norm_zero] using hr
    · intro i hi
      refine ⟨planarMatrix_isSymm _ _ _ _ _,?_⟩
      change relativeBudget 1 (planarMatrix e f (σ*(γ*ω i)) (a*ω i) 0)≤ω i
      rw [relativeBudget_one]
      have hscale : planarMatrix e f (σ*(γ*ω i)) (a*ω i) 0=
          ω i • planarMatrix e f (σ*γ) a 0 := by
        rw [← planarMatrix_scale]
        congr 1 <;> ring
      rw [hscale,norm_smul,Real.norm_of_nonneg (hω i hi)]
      exact (mul_le_mul_of_nonneg_left hP (hω i hi)).trans_eq (mul_one _)
    · change relativeBudget 1 (planarMatrix e f (σ*w) 0 0)≤w
      rw [relativeBudget_one]
      rw [planar_diagonal_norm e f he,abs_mul,hσabs,abs_of_nonneg hw,one_mul]
    · intro i _
      refine ⟨Matrix.isSymm_zero,?_⟩
      simpa only [S,knownBasePlanarScenario,relativeBudget_one,norm_zero] using hτ
  have ht := Scenario.inPhysical_admissible S N 1 (metricRoot A)⁻¹ Matrix.PosDef.one
    (Matrix.isUnit_nonsing_inv_det _ (metricRoot_det_unit A hA)) r ω w τ hS
  simpa only [inverseRootForm_one A hA] using ht

end
end krylov.Information
