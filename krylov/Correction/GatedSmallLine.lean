import krylov.Correction.GatedPhaseGrowth
import krylov.Stability.CanonicalDirectionGeometry
import krylov.Methods.DirectionStaircase
import krylov.Correction.GatedWindowPhase

/-!
Article: main_krylov, thm:UCg and apG:restart, genuine small-line control.
Use: Bound the actual current gradient by its real searched displacement and
old observed projection, so small intermediate lines imply small gradients.
Source: true positive spectral quadratic forms, actual observed orthogonal
projections, real conjugacy solves and the exact implemented search quotient.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Stability
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The true exact-search displacement controls its actual gradient/direction pairing.
Use: Complete the small-intermediate-line case of the uniform gated-RFC cycle argument.
Article: main_krylov, thm:UCg and apG:restart, actual small-line control.
Proof: The actual search makes the post-search pairing zero; its genuine quotient and the real operator norm give the stated bound.
-/
theorem actual_line_pairing_bound (A : E →L[ℝ] E) (g d : E)
    (hA : ‖A‖≤2) (hc : inner ℝ d (A d)≠0) :
    |inner ℝ g d|≤2*‖lineLength g d (A d) • d‖*‖d‖ := by
  let α := lineLength g d (A d)
  have he : inner ℝ d g= -(α*inner ℝ d (A d)) := by
    have ht := searchedGradient_inner_zero g d (A d) hc
    rw [searchedGradient,inner_add_right,real_inner_smul_right] at ht
    exact eq_neg_of_add_eq_zero_left ht
  have ha := (A.le_opNorm d).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg d))
  have hi : |inner ℝ d (A d)|≤2*‖d‖^2 := by
    have ht := norm_inner_le_norm (𝕜 := ℝ) d (A d)
    rw [Real.norm_eq_abs] at ht
    exact ht.trans (by nlinarith [norm_nonneg d])
  calc
    _ = |α| * |inner ℝ d (A d)| := by rw [real_inner_comm,he,abs_neg,abs_mul]
    _ ≤ |α| * (2*‖d‖^2) := mul_le_mul_of_nonneg_left hi (abs_nonneg α)
    _ = _ := by rw [norm_smul,Real.norm_eq_abs]; dsimp only [α]; ring

variable [FiniteDimensional ℝ E]

/-- Genuine observed conjugacy and the actual search line control the original positive-base energy by the real line and old projected residual.
Use: Reuse the same true energy estimate for unit-normalized and arbitrary positive spectral intervals.
Article: main_krylov, thm:UCg and apG:restart, actual small-line energy.
Proof: The actual observed-span equation identifies the real base energy with a projected-gradient pairing minus the genuine search pairing. The proved true projection, conjugacy and line estimates bound these two terms independently of reference scaling.
-/
theorem observed_direction_energy_bound {p : ℕ} (s y : Fin p → E)
    (H A : E →L[ℝ] E) (g d : E)
    (hs : ∀ i, ‖s i‖=1) (hG : ‖crossGram s s-1‖≤(1/2 : ℝ))
    (hspan : d+H g∈Submodule.span ℝ (Set.range s))
    {η : ℝ} (hη : 0≤η) (hsmall : 4*Real.sqrt p*η≤1/2)
    (hy : ∀ i, ‖y i-s i‖≤η) (ho : ∀ i, inner ℝ (y i) d=0)
    (hA : ‖A‖≤2) (hc : inner ℝ d (A d)≠0) :
    inner ℝ g (H g)≤(8*‖H‖*‖lineLength g d (A d) • d‖+
      20*‖H‖*‖projectedResidual s g‖)*‖g‖ := by
  have hproj := observedProjection_conjugacy_bound s y hs hG d hη hy ho
  have hdir := (projected_direction_bound s H g d hspan
    (show 0≤4*Real.sqrt p*η by positivity) hsmall (hproj.trans_eq (by ring))).1
  have hpg := observedProjection_residual_bound s hG g
  have hp := (Submodule.span ℝ (Set.range s)).starProjection_inner_eq_zero g (d+H g) hspan
  change inner ℝ (g-observedProjection s g) (d+H g)=0 at hp
  rw [inner_sub_left,inner_add_right] at hp
  have henergy : inner ℝ g (H g)=inner ℝ (observedProjection s g) (d+H g)-inner ℝ g d := by linarith
  have hcross : inner ℝ (observedProjection s g) (d+H g)≤
      (4*‖projectedResidual s g‖)*(4*‖H‖*‖g‖+‖H‖*‖g‖) := by
    have hv := (norm_add_le d (H g)).trans (add_le_add hdir (H.le_opNorm g))
    exact (real_inner_le_norm _ _).trans (mul_le_mul hpg hv (norm_nonneg _) (by positivity))
  have hline := (actual_line_pairing_bound A g d hA hc).trans
    (mul_le_mul_of_nonneg_left hdir (by positivity : 0≤2*‖lineLength g d (A d) • d‖))
  rw [henergy]
  have habs := (abs_le.mp hline).1
  nlinarith

/-- A true observed-span conjugate direction for a coercive reference bounds the actual gradient by its real line step and old projected residual.
Use: Complete the small-intermediate-line case of the uniform gated-RFC cycle argument.
Article: main_krylov, thm:UCg and apG:restart, actual small-line control.
Proof: The genuine span equation makes the positive base energy equal an actual projected-gradient pairing minus the search pairing. Proved observed conjugacy absorbs the direction component, the real projection bounds the old residual and the exact search bounds the line pairing; cancel the genuine nonzero gradient norm after separating its zero case.
-/
theorem observed_small_line_restart_bound {p : ℕ} (s y : Fin p → E)
    (H A : E →L[ℝ] E) (g d : E)
    (hs : ∀ i, ‖s i‖=1) (hG : ‖crossGram s s-1‖≤(1/2 : ℝ))
    (hspan : d+H g∈Submodule.span ℝ (Set.range s))
    (hcoerc : ∀ v : E, ‖v‖^2≤ inner ℝ v (H v))
    {η : ℝ} (hη : 0≤η) (hsmall : 4*Real.sqrt p*η≤1/2)
    (hy : ∀ i, ‖y i-s i‖≤η) (ho : ∀ i, inner ℝ (y i) d=0)
    (hA : ‖A‖≤2) (hc : inner ℝ d (A d)≠0) :
    ‖g‖≤8*‖H‖*‖lineLength g d (A d) • d‖+
      20*‖H‖*‖projectedResidual s g‖ := by
  have he := (hcoerc g).trans (observed_direction_energy_bound s y H A g d hs hG hspan hη hsmall hy ho hA hc)
  by_cases hg : g=0
  · rw [hg,norm_zero]
    positivity
  · have hpos := norm_pos_iff.mpr hg
    nlinarith

/-- The actual observed-list direction has its genuine canonical base-gradient span equation.
Use: Complete the small-intermediate-line case of the uniform gated-RFC cycle argument.
Article: main_krylov, thm:UCg and apG:restart, actual small-line control.
Proof: The real direction is minus the observed gradient plus its computed old-step synthesis. The positive-root map transports that actual synthesis, and true normalization preserves the real old span.
-/
theorem windowDirection_canonical_span {n : ℕ}
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (W : List (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
    (g : EuclideanSpace ℝ (Fin n)) :
    let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (krylov.Secant.metricRoot base)
    let J := Matrix.toEuclideanCLM (𝕜 := ℝ) (krylov.Secant.metricRoot base)⁻¹
    R (windowDirection W g)+cgOperator base (J g)∈
      Submodule.span ℝ (Set.range (unitWindow (primalWindow base (windowSteps W)))) := by
  let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (krylov.Secant.metricRoot base)
  have he : unitWindow (primalWindow base (windowSteps W))=
      fun i => NormedSpace.normalize (R (windowSteps W i)) := rfl
  dsimp only
  rw [he,span_normalize_eq_span,canonical_base_dual base hb]
  have hc := combine_mem_span (primalWindow base (windowSteps W))
    (conjugacyCoefficients (windowSteps W) (windowImages W) g)
  have hv : R (windowDirection W g)+R g=
      combine (primalWindow base (windowSteps W)) (conjugacyCoefficients (windowSteps W) (windowImages W) g) := by
    change R (-g+combine _ _)+R g=_
    rw [map_add,map_neg,combine_operator R]
    abel
  rw [hv]
  exact hc

/-- The genuine nonsingular observed-list solve annihilates every true normalized canonical old secant.
Use: Complete the small-intermediate-line case of the uniform gated-RFC cycle argument.
Article: main_krylov, thm:UCg and apG:restart, actual small-line control.
Proof: Apply the actual inverse solve conjugacy equation and the proved primal/dual metric pairing; true old-column normalization preserves zero.
-/
theorem windowDirection_canonical_conjugacy {n : ℕ}
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (W : List (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
    (g : EuclideanSpace ℝ (Fin n))
    (hC : IsUnit (crossGram (windowImages W) (windowSteps W)).det) (i : Fin W.length) :
    let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (krylov.Secant.metricRoot base)
    inner ℝ (rescaleWindow (dualWindow base (windowImages W))
      (fun j => ‖primalWindow base (windowSteps W) j‖⁻¹) i) (R (windowDirection W g))=0 := by
  have hc := congrFun (conjugacyDirection_conjugate (windowSteps W) (windowImages W) g hC) i
  dsimp only
  rw [rescaleWindow,real_inner_smul_left,real_inner_comm]
  dsimp only [dualWindow]
  rw [← canonical_search_pairing base hb]
  change _*inner ℝ (windowDirection W g) (windowImages W i)=0
  rw [real_inner_comm]
  change inner ℝ (windowImages W i) (windowDirection W g)=0 at hc
  rw [hc,mul_zero]

/-- The original physical observed-list method has the genuine small-line gradient bound in its true reference metric.
Use: Complete the small-intermediate-line case of the uniform gated-RFC cycle argument.
Article: main_krylov, thm:UCg and apG:restart, actual small-line control.
Proof: The real solve proves every old step nonzero before normalization, and derives both its true canonical span and conjugacy equations. The actual base spectrum supplies coercivity; genuine observed-pair and current-operator budgets give the proved geometric restart bound with the actual physical line step.
-/
theorem windowDirection_small_line_restart_bound {n : ℕ}
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (hspec : ∀ i, 1≤hb.1.eigenvalues i)
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
    ‖J g‖≤8*‖cgOperator base‖*‖R (lineLength g (windowDirection W g) (A (windowDirection W g)) • windowDirection W g)‖+
      20*‖cgOperator base‖*‖projectedResidual (unitWindow (primalWindow base (windowSteps W))) (J g)‖ := by
  let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (krylov.Secant.metricRoot base)
  let J := Matrix.toEuclideanCLM (𝕜 := ℝ) (krylov.Secant.metricRoot base)⁻¹
  have hs (i : Fin W.length) : primalWindow base (windowSteps W) i≠0 :=
    canonical_window_steps_ne_zero base hb W hC i
  have hcoerc (v : EuclideanSpace ℝ (Fin n)) : ‖v‖^2≤ inner ℝ v (cgOperator base v) := by
    simpa only [one_mul,cgOperator] using krylov.LinearAlgebra.spectral_lower_form base hb.1 hspec v
  have hcurv : inner ℝ (R (windowDirection W g)) (canonicalOperator base A (R (windowDirection W g)))≠0 := by
    rw [canonicalOperator_primal base hb,← canonical_search_pairing base hb]
    exact hc
  have hout := observed_small_line_restart_bound
    (unitWindow (primalWindow base (windowSteps W)))
    (rescaleWindow (dualWindow base (windowImages W)) (fun i => ‖primalWindow base (windowSteps W) i‖⁻¹))
    (cgOperator base) (canonicalOperator base A) (J g) (R (windowDirection W g))
    (unitWindow_norm _ hs) hG (windowDirection_canonical_span base hb W g) hcoerc hη hsmall
    (unitWindow_pair_error _ _ hs hy) (windowDirection_canonical_conjugacy base hb W g hC)
    (near_identity_operator_norm _ hA hhalf) hcurv
  rw [canonicalOperator_primal base hb,canonical_lineLength base hb] at hout
  simpa only [map_smul] using hout

end
end krylov.Correction
