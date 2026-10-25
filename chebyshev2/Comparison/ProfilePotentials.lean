import chebyshev2.Comparison.ProfileJost
import chebyshev2.Comparison.ProfileBounds
import chebyshev2.Comparison.Coefficients
import chebyshev2.Comparison.LinearPair
import chebyshev2.Comparison.SymmetricObservation

/-!
Article: chebyshev2, Theorem 3.4.
Lemma 12: exact determinant and trace potentials for every comparison profile.
Use: `chebyshev2.Comparison.Profile.tracePotential_path_derivative` feeds
`chebyshev2.Comparison.Profile.traceAlong_derivative` (trace Along derivative).
Proof chain: `chebyshev2.Comparison.Profile.signed_trace_comparison` — chebyshev2, Theorem
3.4; Signed determinant and square-trace comparisons.
-/
namespace chebyshev2.Comparison.Profile
noncomputable section
open Set MeasureTheory Filter Real chebyshev2.PrescribedSpeed chebyshev2.GroundState chebyshev2.Filters chebyshev2.Continuum chebyshev2.Comparison
open scoped Topology
set_option backward.isDefEq.respectTransparency false
variable {κ : ℝ} (P : chebyshev2.Comparison.Profile κ) (hκ : 0 < κ)

/--
Defines `determinantL` of type `ℝ` by `log (jost s (reflected (P.density hκ)) (-((P.speedData
hκ).X q)))`.

Use: `chebyshev2.Comparison.Profile.determinantPotential` uses this definition in the
displayed construction of `determinantPotential`. Its inputs and component formulas are fixed
by that definition.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.
-/
def determinantL (s q : ℝ) : ℝ := log (jost s (reflected (P.density hκ))
  (-((P.speedData hκ).X q)))
/--
Defines `determinantPotential` of type `ℝ` by `P.determinantL hκ s q+log ((2+r+P.rightFilter hκ
s q)/2)`.

Use: `chebyshev2.Comparison.Profile.determinantPotential_two` uses this definition to
establish exact identity `P.determinantPotential hκ s 2 r=log (1+r/2)`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.
-/
def determinantPotential (s q r : ℝ) : ℝ :=
  P.determinantL hκ s q+log ((2+r+P.rightFilter hκ s q)/2)

/--
The actual derivative at the stated point: `HasDerivAt (P.determinantL hκ s) (-P.rightFilter hκ
s q/P.speed q) q`.

Use: `chebyshev2.Comparison.Profile.determinantPotential_q_derivative` uses this derivative
formula to establish the actual derivative at the stated point: `HasDerivAt (fun q =>
P.determinantPotential hκ s q r) (-(r*P.rightFilter hκ s q+s*(P.amplitude q)^2)/ (P.speed
q*(2+r+P.rightFilter hκ s q))) q`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.Filters.log_jost_hasDerivAt`,
`chebyshev2.Filters.reflected_integrable`,
`chebyshev2.PrescribedSpeed.SpeedData.density_integrable` with the arguments shown in the
proof.
-/
theorem determinantL_derivative {s q : ℝ} (hs : 0 ≤ s) (hq : q ∈ Ioo (0:ℝ) 2) :
    HasDerivAt (P.determinantL hκ s) (-P.rightFilter hκ s q/P.speed q) q := by
  -- Use the identities/estimates `chebyshev2.Filters.log_jost_hasDerivAt`,
  -- `chebyshev2.Filters.reflected_integrable`,
  -- `chebyshev2.PrescribedSpeed.SpeedData.density_integrable` with the arguments shown in
  -- the proof.
  have h := (log_jost_hasDerivAt
    (reflected_integrable ((P.speedData hκ).density_integrable hκ))
    (reflected_nonneg ((P.speedData hκ).density_nonneg hκ)) hs
    (-((P.speedData hκ).X q))).comp q (P.X_derivative hκ hq).neg
  convert h using 1
  · rfl
  · dsimp only [rightFilter,density]
    simp only [div_eq_mul_inv]
    ring

/--
The actual derivative at the stated point: `HasDerivAt (fun q => P.determinantPotential hκ s q
r) (-(r*P.rightFilter hκ s q+s*(P.amplitude q)^2)/ (P.speed q*(2+r+P.rightFilter hκ s q))) q`.

Use: a standalone supporting derivative formula for the article chain below; no retained
declaration currently has an explicit proof dependency on it.

Article: chebyshev2, Theorem 3.4.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem determinantPotential_q_derivative {s q r : ℝ} (hs : 0 ≤ s)
    (hq : q ∈ Ioo (0:ℝ) 2) (hr : 0 ≤ r) :
    HasDerivAt (fun q => P.determinantPotential hκ s q r)
      (-(r*P.rightFilter hκ s q+s*(P.amplitude q)^2)/
        (P.speed q*(2+r+P.rightFilter hκ s q))) q := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hR := P.rightFilter_bounds hκ hs ⟨hq.1.le,hq.2.le⟩
  have hn : 2+r+P.rightFilter hκ s q ≠ 0 := ne_of_gt (by linarith [hR.1])
  have h := (P.determinantL_derivative hκ hs hq).add
    (((P.rightFilter_derivative hκ hs hq).const_add (2+r)).div_const 2 |>.log
      (div_ne_zero hn (by norm_num)))
  convert h using 1
  · rfl
  · field_simp [(P.speed_pos hq).ne',hn]
    ring

/--
The actual derivative at the stated point: `HasDerivAt (P.determinantPotential hκ s q)
(1/(2+r+P.rightFilter hκ s q)) r`.

Use: a standalone supporting derivative formula for the article chain below; no retained
declaration currently has an explicit proof dependency on it.

Article: chebyshev2, Theorem 3.4.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem determinantPotential_r_derivative {s q r : ℝ} (hs : 0 ≤ s)
    (hq : q ∈ Icc (0:ℝ) 2) (hr : 0 ≤ r) :
    HasDerivAt (P.determinantPotential hκ s q) (1/(2+r+P.rightFilter hκ s q)) r := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hR := P.rightFilter_bounds hκ hs hq
  have hn : 2+r+P.rightFilter hκ s q ≠ 0 := ne_of_gt (by linarith [hR.1])
  have h := (hasDerivAt_const r (P.determinantL hκ s q)).add
    ((((hasDerivAt_id r).const_add 2).add_const (P.rightFilter hκ s q)).div_const 2 |>.log
      (div_ne_zero hn (by norm_num)))
  convert h using 1
  · rfl
  · simp only [id_eq]
    field_simp [hn]
    ring

/--
Exact identity `P.determinantPotential hκ s 2 r=log (1+r/2)`.

Use: `chebyshev2.Comparison.Profile.determinantAlong_derivative` rewrites with this
identity to prove the eventual or almost-everywhere assertion `∀ᵐ x,
HasDerivAt (determinantAlong G P (s := s)) (-nonlinear s m x+P.comparisonA G.coupling_positive
s (G.q x) (nonlinear s m x)* (m x-(P.amplitude (G.q x))^2)) x`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates
`chebyshev2.PrescribedSpeed.SpeedData.density_zero_outside`,
`chebyshev2.Comparison.Profile.rightFilter_two`,
`chebyshev2.Filters.jost_left_of_density_zero` with the arguments shown in the proof.
-/
theorem determinantPotential_two {s r : ℝ} (hs : 0 ≤ s) :
    P.determinantPotential hκ s 2 r=log (1+r/2) := by
  -- Use the identities/estimates
  -- `chebyshev2.PrescribedSpeed.SpeedData.density_zero_outside`,
  -- `chebyshev2.Comparison.Profile.rightFilter_two`,
  -- `chebyshev2.Filters.jost_left_of_density_zero` with the arguments shown in the proof.
  have hz : ∀ t ≤ -((P.speedData hκ).X 2),
      reflected ((P.speedData hκ).density κ) t=0 := by
    intro t ht
    change (P.speedData hκ).density κ (-t)=0
    exact (P.speedData hκ).density_zero_outside κ (fun h => by linarith [h.2])
  unfold determinantPotential determinantL
  change log (jost s (reflected ((P.speedData hκ).density κ)) (-((P.speedData hκ).X 2)))+
    log ((2+r+P.rightFilter hκ s 2)/2)=_
  rw [P.rightFilter_two hκ hs,jost_left_of_density_zero
    (reflected_integrable ((P.speedData hκ).density_integrable hκ))
    (reflected_nonneg ((P.speedData hκ).density_nonneg hκ)) hs _ hz,log_one,zero_add]
  congr 1
  ring

/--
The precise assertion is `P.determinantPotential hκ s 0 0= logDeterminant (kernelEigenvalue
((P.speedData hκ).density_integrable hκ) ((P.speedData hκ).density_nonneg hκ)) s`.

Use: `chebyshev2.Comparison.Profile.signed_determinant_comparison` rewrites with this
identity to establish the identity stated in that declaration.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates
`chebyshev2.PrescribedSpeed.SpeedData.density_integrable`,
`chebyshev2.PrescribedSpeed.SpeedData.density_nonneg`,
`chebyshev2.PrescribedSpeed.SpeedData.density_zero_outside` with the arguments shown in the
proof.
-/
theorem determinantPotential_zero {s : ℝ} (hs : 0 ≤ s) :
    P.determinantPotential hκ s 0 0=
      logDeterminant (kernelEigenvalue ((P.speedData hκ).density_integrable hκ)
        ((P.speedData hκ).density_nonneg hκ)) s := by
  -- Use the identities/estimates
  -- `chebyshev2.PrescribedSpeed.SpeedData.density_integrable`,
  -- `chebyshev2.PrescribedSpeed.SpeedData.density_nonneg`,
  -- `chebyshev2.PrescribedSpeed.SpeedData.density_zero_outside` with the arguments shown
  -- in the proof.
  let S := P.speedData hκ
  have hz : ∀ t ≤ S.X 0, S.density κ t=0 := by
    intro t ht
    exact S.density_zero_outside κ (fun h => (not_lt_of_ge ht) h.1)
  have he := jostWronskian_value (S.density_integrable hκ) (S.density_nonneg hκ)
    (P.density_continuous hκ) hs (S.X 0)
  simp only [jostWronskian,nonlinear_left_of_density_zero _ _ hz,
    jost_left_of_density_zero (S.density_integrable hκ) (S.density_nonneg hκ) hs _ hz,add_zero,mul_one] at he
  have hR := P.rightFilter_bounds hκ hs (q := 0) (by norm_num)
  have hv : 0 < jost s (reflected (S.density κ)) (-S.X 0) :=
    jost_positive (reflected_integrable (S.density_integrable hκ)) (reflected_nonneg (S.density_nonneg hκ)) hs _
  have hprod : jost s (reflected (S.density κ)) (-S.X 0)*((2+P.rightFilter hκ s 0)/2)=transmission s (S.density κ) := by
    change (2+nonlinear s (reflected (S.density κ)) (-S.X 0))*jost s (reflected (S.density κ)) (-S.X 0)=
      2*transmission s (S.density κ) at he
    change jost s (reflected (S.density κ)) (-S.X 0)*((2+nonlinear s (reflected (S.density κ)) (-S.X 0))/2)=_
    linarith
  unfold determinantPotential determinantL
  simp only [add_zero]
  change log (jost s (reflected (S.density κ)) (-S.X 0))+log ((2+P.rightFilter hκ s 0)/2)=_
  rw [← log_mul hv.ne' (div_ne_zero (ne_of_gt (by linarith [hR.1])) (by norm_num)),hprod,
    log_transmission_eq_logDeterminant (S.density_integrable hκ) (S.density_nonneg hκ) hs]

end
end chebyshev2.Comparison.Profile

namespace chebyshev2.Comparison.Profile
noncomputable section
open Set MeasureTheory Filter Real chebyshev2.Filters chebyshev2.Comparison chebyshev2.Calibration chebyshev2.Continuum
open scoped Topology
set_option backward.isDefEq.respectTransparency false
variable {κ : ℝ} (P : chebyshev2.Comparison.Profile κ) (hκ : 0 < κ)

/--
Defines `traceIntegrand` of type `ℝ` by `P.density hκ x*rightCausal (P.density hκ) x`.

Use: `chebyshev2.Comparison.Profile.traceG` uses this definition in the displayed
construction of `traceG`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.
-/
def traceIntegrand (x : ℝ) : ℝ :=
  P.density hκ x*rightCausal (P.density hκ) x
/--
Defines `traceG` of type `ℝ` by `κ^2/2*((∫ x in Ioi (0:ℝ), P.traceIntegrand hκ x)- primitive
(P.traceIntegrand hκ) ((P.speedData hκ).X q))`.

Use: `chebyshev2.Comparison.Profile.traceG_continuous` uses this definition to establish
continuity of the displayed function: `Continuous (P.traceG hκ)`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.
-/
def traceG (q : ℝ) : ℝ := κ^2/2*((∫ x in Ioi (0:ℝ), P.traceIntegrand hκ x)-
  primitive (P.traceIntegrand hκ) ((P.speedData hκ).X q))
/--
Defines `tracePotential` of type `ℝ` by `r^2/4+r*P.rightLinear hκ q/2+P.traceG hκ q`.

Use: `chebyshev2.Comparison.Profile.tracePotential_two` rewrites with this definition to
establish exact identity `P.tracePotential hκ 2 r=r^2/4`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.
-/
def tracePotential (q r : ℝ) : ℝ :=
  r^2/4+r*P.rightLinear hκ q/2+P.traceG hκ q

/--
Integrability of the displayed function: `Integrable (P.traceIntegrand hκ)`.

Use: `chebyshev2.Comparison.Profile.traceG_tail` uses this integrability result to
establish exact identity `P.traceG hκ q=κ^2/2*∫ x in Ioi ((P.speedData hκ).X q),
P.traceIntegrand hκ x`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates
`chebyshev2.Comparison.density_mul_rightCausal_integrable`,
`chebyshev2.PrescribedSpeed.SpeedData.density_integrable`,
`chebyshev2.PrescribedSpeed.SpeedData.density_nonneg` with the arguments shown in the
proof.
-/
theorem traceIntegrand_integrable : Integrable (P.traceIntegrand hκ) :=
  density_mul_rightCausal_integrable ((P.speedData hκ).density_integrable hκ)
    ((P.speedData hκ).density_nonneg hκ)

/--
Continuity of the displayed function: `Continuous (P.traceIntegrand hκ)`.

Use: `chebyshev2.Comparison.Profile.traceG_continuous` uses this continuity result to
establish continuity of the displayed function: `Continuous (P.traceG hκ)`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.Comparison.Profile.density_continuous`,
`chebyshev2.Comparison.rightCausal_c1`,
`chebyshev2.PrescribedSpeed.SpeedData.density_integrable` with the arguments shown in the
proof.
-/
theorem traceIntegrand_continuous : Continuous (P.traceIntegrand hκ) :=
  (P.density_continuous hκ).mul
    (rightCausal_c1 ((P.speedData hκ).density_integrable hκ)
      (P.density_continuous hκ)).continuous

/--
Exact identity `P.traceG hκ q=κ^2/2*∫ x in Ioi ((P.speedData hκ).X q), P.traceIntegrand hκ x`.

Use: `chebyshev2.Comparison.Profile.traceG_two` rewrites with this identity to establish
exact identity `P.traceG hκ 2=0`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates
`chebyshev2.Comparison.Profile.traceIntegrand_integrable` with the arguments shown in the
proof.
-/
theorem traceG_tail (q : ℝ) :
    P.traceG hκ q=κ^2/2*∫ x in Ioi ((P.speedData hκ).X q), P.traceIntegrand hκ x := by
  have he := intervalIntegral.integral_Ioi_sub_Ioi'
    (a := (0:ℝ)) (b := (P.speedData hκ).X q)
    (P.traceIntegrand_integrable hκ).integrableOn (P.traceIntegrand_integrable hκ).integrableOn
  unfold traceG primitive
  congr 1
  linarith

/--
Continuity of the displayed function: `Continuous (P.traceG hκ)`.

Use: `chebyshev2.Comparison.Profile.tracePotential_continuous` uses this continuity result
to establish continuity of the displayed function: `Continuous (fun p : ℝ × ℝ =>
P.tracePotential hκ p.1 p.2)`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.Calibration.primitive_c1`,
`chebyshev2.Comparison.Profile.traceIntegrand_continuous`,
`chebyshev2.PrescribedSpeed.SpeedData.X_continuous` with the arguments shown in the proof.
-/
theorem traceG_continuous : Continuous (P.traceG hκ) := by
  unfold traceG
  exact (continuous_const.sub
    ((primitive_c1 (P.traceIntegrand_continuous hκ)).continuous.comp
      (P.speedData hκ).X_continuous)).const_mul _

/--
The actual derivative at the stated point: `HasDerivAt (P.traceG hκ) (-κ*(P.amplitude
q)^2*P.rightLinear hκ q/(2*P.speed q)) q`.

Use: `chebyshev2.Comparison.Profile.tracePotential_path_derivative` uses this derivative
formula to establish the derivative formula stated in that declaration.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.Calibration.primitive_derivative`,
`chebyshev2.Comparison.Profile.traceIntegrand_continuous`,
`chebyshev2.Comparison.Profile.X_derivative` with the arguments shown in the proof.
-/
theorem traceG_derivative {q : ℝ} (hq : q ∈ Ioo (0:ℝ) 2) :
    HasDerivAt (P.traceG hκ) (-κ*(P.amplitude q)^2*P.rightLinear hκ q/(2*P.speed q)) q := by
  -- Use the identities/estimates `chebyshev2.Calibration.primitive_derivative`,
  -- `chebyshev2.Comparison.Profile.traceIntegrand_continuous`,
  -- `chebyshev2.Comparison.Profile.X_derivative` with the arguments shown in the proof.
  have h := (((primitive_derivative (P.traceIntegrand_continuous hκ)
    ((P.speedData hκ).X q)).comp q (P.X_derivative hκ hq)).const_sub
      (∫ x in Ioi (0:ℝ), P.traceIntegrand hκ x)).const_mul (κ^2/2)
  convert h using 1
  · rfl
  · dsimp only [traceIntegrand,rightCausal,rightLinear,density]
    have hm := P.density_formula hκ ((P.speedData hκ).X q)
    rw [(P.speedData hκ).q_X ⟨hq.1.le,hq.2.le⟩] at hm
    change (P.speedData hκ).density κ ((P.speedData hκ).X q)=(P.amplitude q)^2 at hm
    rw [hm]
    simp only [div_eq_mul_inv]
    ring

/--
Exact identity `P.traceG hκ 2=0`.

Use: `chebyshev2.Comparison.Profile.tracePotential_two` rewrites with this identity to
establish exact identity `P.tracePotential hκ 2 r=r^2/4`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem traceG_two : P.traceG hκ 2=0 := by
  rw [P.traceG_tail hκ]
  have he : (∫ x in Ioi ((P.speedData hκ).X 2), P.traceIntegrand hκ x)=0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    change (P.speedData hκ).density κ x*rightCausal (P.density hκ) x=0
    rw [(P.speedData hκ).density_zero_outside κ (fun hi => (not_lt_of_ge hx.le) hi.2),zero_mul]
  rw [he,mul_zero]

/--
Exact identity `P.traceG hκ 0=(∫ x, (linear ((P.speedData hκ).density_integrable hκ)
((P.speedData hκ).density_nonneg hκ) x)^2)`.

Use: `chebyshev2.Comparison.Profile.tracePotential_zero` rewrites with this identity to
establish the precise assertion is `P.tracePotential hκ 0 0= (∫ x, (linear ((P.speedData
hκ).density_integrable hκ) ((P.speedData hκ).density_nonneg hκ) x)^2)`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem traceG_zero :
    P.traceG hκ 0=(∫ x, (linear ((P.speedData hκ).density_integrable hκ)
      ((P.speedData hκ).density_nonneg hκ) x)^2) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  let S := P.speedData hκ
  have he : (∫ x in Iic (S.X 0), P.traceIntegrand hκ x)=0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
    change S.density κ x*rightCausal (S.density κ) x=0
    rw [S.density_zero_outside κ (fun hi => (not_lt_of_ge hx) hi.1),zero_mul]
  have ht : (∫ x in Ioi (S.X 0), P.traceIntegrand hκ x)=∫ x, P.traceIntegrand hκ x := by
    have h := intervalIntegral.integral_Iic_add_Ioi
      (P.traceIntegrand_integrable hκ).integrableOn (P.traceIntegrand_integrable hκ).integrableOn (b := S.X 0)
    rw [he,zero_add] at h
    exact h
  rw [P.traceG_tail hκ,ht]
  have h := causal_square_right_mass (S.density_integrable hκ) (S.density_nonneg hκ)
    (P.density_continuous hκ)
  simp only [linear,S.groundParameter_density hκ,mul_pow,integral_const_mul]
  change κ^2/2*(∫ x, S.density κ x*rightCausal (S.density κ) x)=κ^2*(∫ x, (causal 2 (S.density κ) x)^2)
  rw [h]
  ring

/--
Exact identity `P.tracePotential hκ 2 r=r^2/4`.

Use: `chebyshev2.Comparison.Profile.signed_trace_comparison` uses this identity to
establish the identity stated in that declaration.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.Comparison.Profile.rightLinear_two`,
`chebyshev2.Comparison.Profile.traceG_two` with the arguments shown in the proof.
-/
theorem tracePotential_two (r : ℝ) : P.tracePotential hκ 2 r=r^2/4 := by simp only [tracePotential,P.rightLinear_two hκ,P.traceG_two hκ,mul_zero,zero_div,add_zero]

/--
The precise assertion is `P.tracePotential hκ 0 0= (∫ x, (linear ((P.speedData
hκ).density_integrable hκ) ((P.speedData hκ).density_nonneg hκ) x)^2)`.

Use: `chebyshev2.Comparison.Profile.signed_trace_comparison` rewrites with this identity to
establish the identity stated in that declaration.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.Comparison.Profile.traceG_zero` with the
arguments shown in the proof.
-/
theorem tracePotential_zero : P.tracePotential hκ 0 0=
    (∫ x, (linear ((P.speedData hκ).density_integrable hκ)
      ((P.speedData hκ).density_nonneg hκ) x)^2) := by
  simp only [tracePotential,zero_pow (by decide : 2 ≠ 0),zero_div,zero_mul,zero_add,P.traceG_zero hκ]

/--
Continuity of the displayed function: `Continuous (fun p : ℝ × ℝ => P.tracePotential hκ p.1
p.2)`.

Use: `chebyshev2.Comparison.Profile.signed_trace_comparison` uses this continuity result to
establish the identity stated in that declaration.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.Filters.causal_continuous`,
`chebyshev2.Filters.reflected_integrable`,
`chebyshev2.PrescribedSpeed.SpeedData.density_integrable` with the arguments shown in the
proof.
-/
theorem tracePotential_continuous : Continuous (fun p : ℝ × ℝ => P.tracePotential hκ p.1 p.2) := by
  have hR : Continuous (P.rightLinear hκ) :=
    ((causal_continuous (by norm_num : (0:ℝ) ≤ 2)
      (reflected_integrable ((P.speedData hκ).density_integrable hκ))).comp
        (P.speedData hκ).X_continuous.neg).const_mul κ
  exact (((continuous_snd.pow 2).div_const 4).add
    ((continuous_snd.mul (hR.comp continuous_fst)).div_const 2)).add
      ((P.traceG_continuous hκ).comp continuous_fst)

/--
The actual derivative at the stated point: `HasDerivAt (fun t => P.tracePotential hκ (q t) (r
t)) ((2*r x*P.rightLinear hκ (q x)-κ*(P.amplitude (q x))^2*(r x+P.rightLinear hκ (q x)))/
(2*P.speed (q x))*u+(r x+P.rightLinear hκ (q x))/2*v) x`.

Use: `chebyshev2.Comparison.Profile.traceAlong_derivative` uses this derivative formula to
establish establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, HasDerivAt
(traceAlong G P) (-(linear hm hn x)^2+P.comparisonA0 G.coupling_positive (G.q x) (linear hm hn
x)* (m x-(P.amplitude (G.q x))^2)) x`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem tracePotential_path_derivative {x u v : ℝ} {q r : ℝ → ℝ}
    (hq : q x ∈ Ioo (0:ℝ) 2) (hdq : HasDerivAt q u x) (hdr : HasDerivAt r v x) :
    HasDerivAt (fun t => P.tracePotential hκ (q t) (r t))
      ((2*r x*P.rightLinear hκ (q x)-κ*(P.amplitude (q x))^2*(r x+P.rightLinear hκ (q x)))/
        (2*P.speed (q x))*u+(r x+P.rightLinear hκ (q x))/2*v) x := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have h := (((hdr.pow 2).div_const 4).add
    ((hdr.mul ((P.rightLinear_derivative hκ hq).comp x hdq)).div_const 2)).add
      ((P.traceG_derivative hκ hq).comp x hdq)
  convert h using 1
  · rfl
  · simp only [Function.comp_apply]
    field_simp [(P.speed_pos hq).ne']
    ring

end
end chebyshev2.Comparison.Profile
