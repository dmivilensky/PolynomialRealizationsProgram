import krylov.Correction.GatedSmallLine
import krylov.Correction.GatedWindowPhase

/-!
Article: main_krylov, thm:UCg, genuine terminal and scale-uniform restart bounds.
Use: Finish both real uniform gated-RFC terminal cases using actual observed
data and original spectral conditioning, with no smallest-step assumption.
Source: proved true observed energy and model residual identities, actual
spectral-gate domains and full genuine Euclidean Gram reconstruction.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Stability
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Actual positive-base coercivity and a condition-number bound control the true gradient by its genuine line and old projected residual uniformly over every spectral scale.
Use: Assemble the full original spectral-class gated-RFC cycle bounds.
Article: main_krylov, thm:UCg, actual terminal and scale-uniform restart.
Proof: Reuse the proved actual observed energy estimate. The original lower quadratic form and upper operator norm differ only by the true condition-number ratio; multiply by positive real quantities and cancel the actual nonzero gradient norm after separating zero.
-/
theorem observed_small_line_condition_bound {p : ℕ} (s y : Fin p → E)
    (H A : E →L[ℝ] E) (g d : E) {μ κ : ℝ} (hμ : 0<μ) (hκ : 0≤κ)
    (hs : ∀ i, ‖s i‖=1) (hG : ‖crossGram s s-1‖≤(1/2 : ℝ))
    (hspan : d+H g∈Submodule.span ℝ (Set.range s))
    (hcoerc : ∀ v : E, μ*‖v‖^2≤ inner ℝ v (H v)) (hnorm : ‖H‖≤κ*μ)
    {η : ℝ} (hη : 0≤η) (hsmall : 4*Real.sqrt p*η≤1/2)
    (hy : ∀ i, ‖y i-s i‖≤η) (ho : ∀ i, inner ℝ (y i) d=0)
    (hA : ‖A‖≤2) (hc : inner ℝ d (A d)≠0) :
    ‖g‖≤8*κ*‖lineLength g d (A d) • d‖+20*κ*‖projectedResidual s g‖ := by
  have he := (hcoerc g).trans (observed_direction_energy_bound s y H A g d hs hG hspan hη hsmall hy ho hA hc)
  have hn : 8*‖H‖*‖lineLength g d (A d) • d‖+20*‖H‖*‖projectedResidual s g‖≤
      μ*(8*κ*‖lineLength g d (A d) • d‖+20*κ*‖projectedResidual s g‖) := by
    nlinarith [mul_le_mul_of_nonneg_right hnorm (norm_nonneg (lineLength g d (A d) • d)),
      mul_le_mul_of_nonneg_right hnorm (norm_nonneg (projectedResidual s g))]
  have hfinal := he.trans (mul_le_mul_of_nonneg_right hn (norm_nonneg g))
  by_cases hg : g=0
  · rw [hg,norm_zero]
    positivity
  · have hpos := mul_pos hμ (norm_pos_iff.mpr hg)
    nlinarith

/-- The common horizon-only angle and pair-error allowances give every real old Gram and projected-conjugacy smallness margin needed at a small line.
Use: Assemble the full original spectral-class gated-RFC cycle bounds.
Article: main_krylov, thm:UCg, actual terminal and scale-uniform restart.
Proof: Compare the actual prefix dimension and its square root with the original horizon, then use the same genuine nonnegative scalar allowances.
-/
theorem uniform_restart_margins {N m : ℕ} {γ a η : ℝ} (hN : 1≤N) (hm : m≤N)
    (hγ : 0≤γ) (ha : 0≤a) (hη : 0≤η) (hηa : η≤a/2)
    (hbudget : (N : ℝ)*a≤(1-γ)/8) :
    (m : ℝ)*a≤1/2 ∧ 4*Real.sqrt m*η≤1/2 := by
  have hN' : (1 : ℝ)≤N := by exact_mod_cast hN
  have hm' : (m : ℝ)≤N := by exact_mod_cast hm
  have hN0 : (0 : ℝ)≤N := Nat.cast_nonneg N
  have hsqrt : Real.sqrt m≤(N : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨hN0,by nlinarith⟩
  have hma := mul_le_mul_of_nonneg_right hm' ha
  have hNη := mul_le_mul_of_nonneg_left hηa hN0
  have hrootη := mul_le_mul_of_nonneg_right hsqrt hη
  constructor <;> nlinarith

/-- The original observed-list direction has the true small-line gradient bound with constants depending only on spectral conditioning, uniformly over arbitrary positive spectral scales.
Use: Assemble the full original spectral-class gated-RFC cycle bounds.
Article: main_krylov, thm:UCg, actual terminal and scale-uniform restart.
Proof: The actual old inverse gives nonzero genuine canonical columns and true image conjugacy. Original spectral lower forms supply the real coercivity constant; the true base norm supplies its condition-number ratio. Apply the common observed energy bound and preserve the exact actual physical line through genuine root coordinates.
-/
theorem windowDirection_small_line_condition_bound {n : ℕ}
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) {μ κ : ℝ} (hμ : 0<μ) (hκ : 0≤κ)
    (hspec : ∀ i, μ≤hb.1.eigenvalues i) (hnorm : ‖cgOperator base‖≤κ*μ)
    (W : List (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
    (g : EuclideanSpace ℝ (Fin n))
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hC : IsUnit (crossGram (windowImages W) (windowSteps W)).det)
    (hG : ‖crossGram (unitWindow (primalWindow base (windowSteps W)))
      (unitWindow (primalWindow base (windowSteps W)))-1‖≤(1/2 : ℝ))
    {η : ℝ} (hη : 0≤η) (hsmall : 4*Real.sqrt W.length*η≤1/2) (hhalf : η≤1/2)
    (hy : ∀ i, ‖dualWindow base (windowImages W) i-primalWindow base (windowSteps W) i‖≤
      η*‖primalWindow base (windowSteps W) i‖)
    (hA : ‖canonicalOperator base A-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤η)
    (hc : inner ℝ (windowDirection W g) (A (windowDirection W g))≠0) :
    let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (krylov.Secant.metricRoot base)
    let J := Matrix.toEuclideanCLM (𝕜 := ℝ) (krylov.Secant.metricRoot base)⁻¹
    ‖J g‖≤8*κ*‖R (lineLength g (windowDirection W g) (A (windowDirection W g)) • windowDirection W g)‖+
      20*κ*‖projectedResidual (unitWindow (primalWindow base (windowSteps W))) (J g)‖ := by
  let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (krylov.Secant.metricRoot base)
  let J := Matrix.toEuclideanCLM (𝕜 := ℝ) (krylov.Secant.metricRoot base)⁻¹
  have hs := canonical_window_steps_ne_zero base hb W hC
  have hcoerc (v : EuclideanSpace ℝ (Fin n)) : μ*‖v‖^2≤ inner ℝ v (cgOperator base v) := by
    simpa only [cgOperator] using krylov.LinearAlgebra.spectral_lower_form base hb.1 hspec v
  have hcurv : inner ℝ (R (windowDirection W g)) (canonicalOperator base A (R (windowDirection W g)))≠0 := by
    rw [canonicalOperator_primal base hb,← canonical_search_pairing base hb]
    exact hc
  have hout := observed_small_line_condition_bound
    (unitWindow (primalWindow base (windowSteps W)))
    (rescaleWindow (dualWindow base (windowImages W)) (fun i => ‖primalWindow base (windowSteps W) i‖⁻¹))
    (cgOperator base) (canonicalOperator base A) (J g) (R (windowDirection W g)) hμ hκ
    (unitWindow_norm _ hs) hG (windowDirection_canonical_span base hb W g) hcoerc hnorm hη hsmall
    (unitWindow_pair_error _ _ hs hy) (windowDirection_canonical_conjugacy base hb W g hC)
    (near_identity_operator_norm _ hA hhalf) hcurv
  rw [canonicalOperator_primal base hb,canonical_lineLength base hb] at hout
  simpa only [map_smul] using hout

end
end krylov.Correction
