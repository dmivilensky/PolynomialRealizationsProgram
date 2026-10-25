import polyak.Realization.ExplicitSpiral.Assembly

/-!
Article: (spirallower), one actual objective and one Y=2 from-rest start for all horizons.
Use: interpolate the entire unchanged-value table, execute the original Polyak
algorithm, and retain the exact initial norm sqrt(5) under transport to R³.
-/
namespace polyak.Realization.ExplicitSpiral
noncomputable section
open Interpolation Dynamics

/-- Article: the explicit stationary mode satisfies the normalized Polyak recurrence. -/
theorem mode_recurrence {z : ℂ} (hz : z≠0) {q : ℝ} (hq : q≠0) (k : ℕ) :
    modePosition z (some (k+2))=(0 : ℝ) • modePosition z (some (k+1))+
      (2*q) • modeGradient z (multiplier z q) (some (k+1))-
      q^2 • modePosition z (some k) := by
  have hqc : (q : ℂ)≠0 := by exact_mod_cast hq
  simp only [modePosition,modeGradient,zero_smul,zero_add,Complex.real_smul,
    Complex.ofReal_mul,Complex.ofReal_ofNat,Complex.ofReal_pow]
  unfold multiplier
  rw [pow_add,pow_add,pow_one]
  field_simp [hz,hqc]
  ring

/-- Article: one normalized potential interpolates every initialized Y=2 datum. -/
theorem exists_potential_of_table {z : ℂ} {q C : ℝ}
    (h : TableFeasible (position z q) (gradient z (multiplier z q) q) (value z (multiplier z q) C)) :
    ∃ ψ : WithLp 2 (ℂ × ℝ) → ℝ, NormalizedSmooth ψ ∧
      ∀ i, ψ (position z q i)=value z (multiplier z q) C i ∧
        _root_.gradient ψ (position z q i)=gradient z (multiplier z q) q i := by
  apply exists_normalized_interpolant h none
  · simp [position,startupPosition,productPosition,modePosition,scalarPosition]
  · simp [gradient,startupGradient,productGradient,correctGradient,modeGradient,modePosition,scalarPosition]
  · rfl

/-- Article: the whole initialized table is the actual Polyak trajectory from rest. -/
theorem exists_execution_of_table {μ L r : ℝ} (hμ : 0<μ) (hL : μ<L) (hr : 0<r)
    (h : TableFeasible (position (radialWave r) (polyakQ μ L))
      (gradient (radialWave r) (multiplier (radialWave r) (polyakQ μ L)) (polyakQ μ L))
      (value (radialWave r) (multiplier (radialWave r) (polyakQ μ L)) (physicalValueConstant r))) :
    ∃ ψ : WithLp 2 (ℂ × ℝ) → ℝ, NormalizedSmooth ψ ∧ ∀ N : ℕ,
      iterate (_root_.gradient (denormalizeFunction μ L ψ)) (polyakAlpha μ L) (polyakBeta μ L)
        (position (radialWave r) (polyakQ μ L) (some 0)) N=
          position (radialWave r) (polyakQ μ L) (some N) := by
  let q := polyakQ μ L
  have hq : 0<q := polyakQ_pos hμ hL
  have hz : radialWave r≠0 := by
    have he := (radial_wave_coordinates hr).1
    intro hz
    rw [hz,norm_zero] at he
    linarith
  obtain ⟨ψ,hψ,hdata⟩ := exists_potential_of_table h
  refine ⟨ψ,hψ,fun N => ?_⟩
  have hAn : normalizedA μ L (polyakAlpha μ L) (polyakQ μ L^2)=0 := by
    simpa only [polyakBeta] using polyak_normalizedA hμ hL
  have hBn := polyak_normalizedB hμ hL
  have hh := startup_iterate (μ:=μ) (L:=L) (α:=polyakAlpha μ L) (β:=polyakBeta μ L)
    (τ:=0) (Y:=2) (modePosition (radialWave r))
    (modeGradient (radialWave r) (multiplier (radialWave r) q)) hψ
    (by rw [hBn]; positivity)
    (by simpa only [hAn,hBn,polyakBeta,position,gradient] using fun i => (hdata i).2)
    (by simpa only [hAn,hBn,polyakBeta] using mode_recurrence hz hq.ne') N
  simpa only [hAn,hBn,polyakBeta,position] using hh

/-- Article: the exact initial norm gives the explicit lower constant 1/sqrt(5) in R³. -/
theorem exists_three_dimensional_of_table {μ L r : ℝ} (hμ : 0<μ) (hL : μ<L) (hr : 0<r)
    (h : TableFeasible (position (radialWave r) (polyakQ μ L))
      (gradient (radialWave r) (multiplier (radialWave r) (polyakQ μ L)) (polyakQ μ L))
      (value (radialWave r) (multiplier (radialWave r) (polyakQ μ L)) (physicalValueConstant r))) :
    ∃ f : EuclideanSpace ℝ (Fin 3) → ℝ, CenteredSmoothStronglyConvex μ L f ∧
      ∃ x₀, ‖x₀‖=Real.sqrt 5 ∧ x₀≠0 ∧ ∀ N : ℕ,
        (1/Real.sqrt 5)*r^N*‖x₀‖≤‖iterate (_root_.gradient f) (polyakAlpha μ L) (polyakBeta μ L) x₀ N‖ := by
  obtain ⟨ψ,hψ,hmodel⟩ := exists_execution_of_table hμ hL hr h
  let E := WithLp 2 (ℂ × ℝ)
  let F := denormalizeFunction μ L ψ
  have hF : CenteredSmoothStronglyConvex μ L F := hψ.denormalize hμ hL
  let Q := (stdOrthonormalBasis ℝ E).repr.toLinearIsometry
  let G := extendObjective μ L Q F
  have hG : CenteredSmoothStronglyConvex μ L G := hF.extendObjective Q
  let x₀ := Q (position (radialWave r) (polyakQ μ L) (some 0))
  have hxnorm : ‖x₀‖=Real.sqrt 5 := by
    rw [Q.norm_map]
    exact norm_position_zero _ _
  have hxne : x₀≠0 := by
    apply norm_pos_iff.mp
    rw [hxnorm]
    positivity
  have hnorm (N : ℕ) : r^N≤‖iterate (_root_.gradient G) (polyakAlpha μ L) (polyakBeta μ L) x₀ N‖ := by
    rw [iterate_embedding Q (_root_.gradient F) (_root_.gradient G)
      (gradient_extendObjective_embed hF.toSmoothStronglyConvex Q) _ _ _ N,Q.norm_map,hmodel N]
    have he := norm_mode_le_position (radialWave r) (polyakQ μ L) N
    rw [(radial_wave_coordinates hr).1] at he
    exact he
  have hdim : Module.finrank ℝ E=3 := by
    dsimp only [E]
    rw [(WithLp.linearEquiv 2 ℝ (ℂ × ℝ)).finrank_eq,Module.finrank_prod,
      Complex.finrank_real_complex,Module.finrank_self]
  have hresult : ∃ f : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ,
      CenteredSmoothStronglyConvex μ L f ∧ ∃ x₀,‖x₀‖=Real.sqrt 5 ∧ x₀≠0 ∧ ∀ N : ℕ,
        (1/Real.sqrt 5)*r^N*‖x₀‖≤‖iterate (_root_.gradient f) (polyakAlpha μ L) (polyakBeta μ L) x₀ N‖ := by
    refine ⟨G,hG,x₀,hxnorm,hxne,fun N => ?_⟩
    rw [hxnorm]
    have hs : Real.sqrt 5≠0 := by positivity
    have he : (1/Real.sqrt 5)*r^N*Real.sqrt 5=r^N := by field_simp
    rw [he]
    exact hnorm N
  rw [hdim] at hresult
  exact hresult

end
end polyak.Realization.ExplicitSpiral
