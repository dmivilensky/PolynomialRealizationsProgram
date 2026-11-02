import krylov.Correction.GatedRestartEnergy

/-!
Article: main_krylov, apG:restart, sharp observed projection constants.
Use: retain the printed 2/sqrt(3) and sqrt(k/3) epsilon constants under
exactly the true normalized Gram lower bound. Source: genuine orthogonal
projection, the already proved spectral coefficient bound and measured
image conjugacy. No projected-direction bound is an execution premise.
-/
namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Stability
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {p : ℕ}

/-- A lower Gram endpoint gives the sharp inverse-square-root bound for
projection onto the actual old observed span. Article: apG:restart. -/
theorem observedProjection_spectral_bound (s : Fin p → E) {a : ℝ} (ha : 0<a)
    (hgram : ∀ i,a≤(crossGram_isHermitian s).eigenvalues i) (g : E) :
    ‖observedProjection s g‖≤(Real.sqrt a)⁻¹*‖projectedResidual s g‖ := by
  let v := observedProjection s g
  have hv := (Submodule.span ℝ (Set.range s)).starProjection_apply_mem g
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hv
  change combine s c=v at hc
  have hcoeff := combine_coefficients_bound s c ha hgram
  rw [hc] at hcoeff
  have ho := (Submodule.span ℝ (Set.range s)).starProjection_inner_eq_zero g v hv
  change inner ℝ (g-v) v=0 at ho
  rw [inner_sub_left,real_inner_self_eq_norm_sq,real_inner_comm] at ho
  have hi := real_inner_le_norm (WithLp.toLp 2 c) (projectedResidual s g)
  rw [←combine_inner_coordinates,hc] at hi
  have hh := mul_le_mul_of_nonneg_right hcoeff (norm_nonneg (projectedResidual s g))
  have hnorm : 0≤(Real.sqrt a)⁻¹*‖projectedResidual s g‖ := by positivity
  change ‖v‖≤_
  by_cases hz : v=0
  · simpa only [hz,norm_zero] using hnorm
  · have hp := norm_pos_iff.mpr hz
    nlinarith

/-- The exact printed projection constant at the true 3/4 Gram endpoint.
Article: main_krylov, apG:restart, first assertion. -/
theorem observedProjection_three_quarters (s : Fin p → E)
    (hgram : ∀ i,(3/4 : ℝ)≤(crossGram_isHermitian s).eigenvalues i) (g : E) :
    ‖observedProjection s g‖≤(2/Real.sqrt 3)*‖projectedResidual s g‖ := by
  have hs : (Real.sqrt (3/4 : ℝ))⁻¹=2/Real.sqrt 3 := by norm_num [Real.sqrt_div]
  simpa only [hs] using observedProjection_spectral_bound s (by norm_num : (0:ℝ)<3/4) hgram g

/-- Genuine measured image conjugacy gives the original sharper old-span
component, with no independence or projection estimate supplied separately.
Article: main_krylov, apG:restart, epsilon_2=sqrt(k/3) epsilon. -/
theorem observedProjection_sharp_conjugacy (s y : Fin p → E)
    (hgram : ∀ i,(3/4 : ℝ)≤(crossGram_isHermitian s).eigenvalues i)
    (d : E) {epsilon : ℝ} (he : 0≤epsilon)
    (hy : ∀ i,‖y i-s i‖≤epsilon/2) (ho : ∀ i,inner ℝ (y i) d=0) :
    ‖observedProjection s d‖≤(Real.sqrt p/Real.sqrt 3)*epsilon*‖d‖ := by
  have hb : ‖projectedResidual s d‖≤Real.sqrt p*(epsilon/2*‖d‖) := by
    apply coordinate_norm_le_sqrt_card _ (by positivity)
    intro i
    have ha := norm_inner_le_norm (𝕜 := ℝ) (s i-y i) d
    rw [Real.norm_eq_abs,inner_sub_left,ho i,sub_zero] at ha
    have hys : ‖s i-y i‖≤epsilon/2 := by simpa only [norm_sub_rev] using hy i
    exact ha.trans (mul_le_mul_of_nonneg_right hys (norm_nonneg d))
  exact (observedProjection_three_quarters s hgram d).trans
    ((mul_le_mul_of_nonneg_left hb (by positivity : 0≤2/Real.sqrt 3)).trans_eq (by ring))

/-- The true orthogonal complement is a contraction, with no factor two.
Article: main_krylov, apG:restart, direction decomposition. -/
theorem observedProjection_complement_sharp (s : Fin p → E) (v : E) :
    ‖v-observedProjection s v‖≤‖v‖ := by
  simpa only [Submodule.starProjection_orthogonal_val,observedProjection] using
    (Submodule.span ℝ (Set.range s))ᗮ.norm_starProjection_apply_le v

/-- A half-small genuine projected direction has the sharp factor two
bound used by the printed restart proof. Article: apG:restart. -/
theorem projected_direction_sharp (s : Fin p → E) (H : E →L[ℝ] E) (g d : E)
    (hspan : d+H g∈Submodule.span ℝ (Set.range s)) {nu : ℝ} (hsmall : nu≤1/2)
    (hproj : ‖observedProjection s d‖≤nu*‖d‖) : ‖d‖≤2*‖H‖*‖g‖ := by
  have hd := observedProjection_decomposition s H g d hspan
  have hn : ‖d‖≤‖H‖*‖g‖+nu*‖d‖ := by
    calc
      _ = ‖-(H g-observedProjection s (H g))+observedProjection s d‖ := congrArg norm hd
      _ ≤ ‖H g-observedProjection s (H g)‖+‖observedProjection s d‖ := by
        simpa only [norm_neg] using norm_add_le (-(H g-observedProjection s (H g))) (observedProjection s d)
      _ ≤ _ := add_le_add ((observedProjection_complement_sharp s (H g)).trans (H.le_opNorm g)) hproj
  nlinarith [mul_le_mul_of_nonneg_right hsmall (norm_nonneg d)]

end
end krylov.Correction
