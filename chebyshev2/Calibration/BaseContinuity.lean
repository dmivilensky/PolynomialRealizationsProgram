import chebyshev2.Calibration.BaseIdentity

/-!
Article: chebyshev2, Proposition 6.
The derivative estimate 0 ≤ ∂s H ≤ mass/2, in the Lipschitz form needed when the observation scale
moves with the ground parameter.
Use: `chebyshev2.Calibration.logDeterminant_scale_distance` feeds
`chebyshev2.Calibration.Data.packedObservation_tendsto` (packed Observation tendsto).
Proof chain: `chebyshev2.DualCertificate.Data.uniform_finite_lower_bound` — chebyshev2,
Theorem E.1; Stability of strict admissibility and uniform transfer of the certificate value.
-/
namespace chebyshev2.Calibration
noncomputable section
open Set MeasureTheory Filter Real
open scoped Topology
set_option backward.isDefEq.respectTransparency false

namespace Data
variable (C : Data)

/--
Continuity on the stated domain: `ContinuousOn (fun κ => ∫ q in (0:ℝ)..2, C.amplitude κ q) (Ioi
(0:ℝ))`.

Use: `chebyshev2.Calibration.Data.base_continuousOn` uses this continuity result to
establish continuity on the stated domain: `ContinuousOn (fun p : ℝ × ℝ => C.base p.1 p.2) {p |
0 < p.1}`.

Article: chebyshev2, Theorem E.1 via
`chebyshev2.DualCertificate.Data.packed_value_tendsto`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem amplitudeIntegral_continuousOn :
    ContinuousOn (fun κ => ∫ q in (0:ℝ)..2, C.amplitude κ q) (Ioi (0:ℝ)) := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  rw [continuousOn_iff_continuous_domRestrict]
  let : LocallyCompactSpace (Ioi (0:ℝ)) := isOpen_Ioi.locallyCompactSpace
  -- Establish continuity hc before using the function at limits or in calculus arguments.
  have hc : Continuous (fun p : Ioi (0:ℝ) × ℝ => C.extendedAmplitude p.1 p.2) := by
    exact C.amplitude_continuousOn.comp_continuous
      (continuous_subtype_val.comp continuous_fst |>.prodMk
        (continuous_const.max (continuous_const.min continuous_snd)))
      (fun p => ⟨p.1.property,clamp_mem p.2⟩)
  have hi := continuous_parametric_integral_of_continuous
    (μ := volume) (s := Icc (0:ℝ) 2)
    (f := fun κ : Ioi (0:ℝ) => C.extendedAmplitude κ) hc isCompact_Icc
  convert hi using 1
  funext κ
  change (∫ q in (0:ℝ)..2, C.amplitude κ q)=∫ q in Icc (0:ℝ) 2, C.extendedAmplitude κ q
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 2),← integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro q hq
  exact (C.extendedAmplitude_eq hq).symm

/--
Proposition 6's continuity input is proved for the actual cubic amplitude, uniformly on every
compact parameter neighborhood.

Continuity on the stated domain: `ContinuousOn (fun p : ℝ × ℝ => C.base p.1 p.2) {p | 0 <
p.1}`.

Use: `chebyshev2.Calibration.Data.base_tendsto` uses this continuity result to establish
convergence along the specified source filter to the specified limit: `Tendsto (fun a => C.base
(κ a) (H a)) l (𝓝 (C.base k h))`.

Article: chebyshev2, Theorem E.1 via
`chebyshev2.DualCertificate.Data.packed_value_tendsto`.

Proof: Use the identities/estimates
`chebyshev2.Calibration.Data.amplitudeIntegral_continuousOn` with the arguments shown in
the proof.
-/
theorem base_continuousOn : ContinuousOn (fun p : ℝ × ℝ => C.base p.1 p.2)
    {p | 0 < p.1} := by
  -- Use the identities/estimates
  -- `chebyshev2.Calibration.Data.amplitudeIntegral_continuousOn` with the arguments shown
  -- in the proof.
  have hi := C.amplitudeIntegral_continuousOn.comp continuous_fst.continuousOn
    (show MapsTo Prod.fst {p : ℝ × ℝ | 0 < p.1} (Ioi (0:ℝ)) from fun _ h => h)
  -- Establish continuity hk before using the function at limits or in calculus arguments.
  have hk : ContinuousOn (fun p : ℝ × ℝ => p.1) {p | 0 < p.1} := continuous_fst.continuousOn
  have hn : ∀ p ∈ {p : ℝ × ℝ | 0 < p.1}, p.1 ≠ 0 := fun _ hp => ne_of_gt hp
  -- Establish continuity htwo before using the function at limits or in calculus arguments.
  have htwo : ContinuousOn (fun p : ℝ × ℝ => 2*C.b/p.1) {p | 0 < p.1} :=
    continuous_const.continuousOn.div hk hn
  -- Establish continuity hthree before using the function at limits or in calculus arguments.
  have hthree : ContinuousOn (fun p : ℝ × ℝ => 3/(2*p.1)) {p | 0 < p.1} :=
    continuous_const.continuousOn.div (continuous_const.continuousOn.mul hk)
      (fun p hp => mul_ne_zero (by norm_num) (hn p hp))
  exact (((continuous_const.continuousOn.add htwo).add (hthree.mul hi)).sub
    continuous_const.continuousOn).sub (continuous_const.continuousOn.mul
      ((hk.div_const C.sigma).sub (continuous_const.continuousOn.mul continuous_snd.continuousOn)))

/--
Convergence along the specified source filter to the specified limit: `Tendsto (fun a => C.base
(κ a) (H a)) l (𝓝 (C.base k h))`.

Use: `chebyshev2.Calibration.Data.packedBase_tendsto` uses this limit to establish the
limit stated in that declaration.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates `chebyshev2.Calibration.Data.base_continuousOn` with
the arguments shown in the proof.
-/
theorem base_tendsto {α : Type*} {l : Filter α} {κ H : α → ℝ} {k h : ℝ}
    (hk : 0 < k) (hklim : Tendsto κ l (𝓝 k)) (hHlim : Tendsto H l (𝓝 h)) :
    Tendsto (fun a => C.base (κ a) (H a)) l (𝓝 (C.base k h)) := by
  -- Use the identities/estimates `chebyshev2.Calibration.Data.base_continuousOn` with the
  -- arguments shown in the proof.
  have hopen : IsOpen {p : ℝ × ℝ | 0 < p.1} := isOpen_lt continuous_const continuous_fst
  -- Establish continuity hc before using the function at limits or in calculus arguments.
  have hc : ContinuousAt (fun p : ℝ × ℝ => C.base p.1 p.2) (k,h) :=
    ContinuousOn.continuousAt (x := (k,h)) (C.base_continuousOn)
      (hopen.mem_nhds (x := (k,h)) hk)
  -- Record the convergence hp with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hp : Tendsto (fun a => (κ a,H a)) l (𝓝 (k,h)) := hklim.prodMk_nhds hHlim
  exact Tendsto.comp (g := fun p : ℝ × ℝ => C.base p.1 p.2)
    (f := fun a : α => (κ a,H a)) hc hp

end Data

/--
The derivative estimate 0 ≤ ∂s H ≤ mass/2, in the Lipschitz form needed when the observation
scale moves with the ground parameter.

The stated quantitative bound `|chebyshev2.Continuum.logDeterminant a
s-chebyshev2.Continuum.logDeterminant a t| ≤ |s-t|/2*(∑' j, a j)`.

Use: `chebyshev2.Calibration.Data.packedObservation_tendsto` uses this bound to establish
the limit stated in that declaration.

Article: chebyshev2, Theorem E.1 via
`chebyshev2.DualCertificate.Data.packed_value_tendsto`.

Proof: Use the identities/estimates `chebyshev2.Continuum.log_spectral_summable`,
`chebyshev2.Continuum.log_abs_sub_le` with the arguments shown in the proof.
-/
theorem logDeterminant_scale_distance {a : ℕ → ℝ} (ha : Summable a) (hn : ∀ j, 0 ≤ a j)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    |chebyshev2.Continuum.logDeterminant a s-chebyshev2.Continuum.logDeterminant a t| ≤
      |s-t|/2*(∑' j, a j) := by
  -- Use the identities/estimates `chebyshev2.Continuum.log_spectral_summable`,
  -- `chebyshev2.Continuum.log_abs_sub_le` with the arguments shown in the proof.
  open chebyshev2.Continuum in
  rw [logDeterminant,logDeterminant,← (log_spectral_summable ha hn hs).tsum_sub
    (log_spectral_summable ha hn ht)]
  have h := norm_tsum_le_tsum_norm ((chebyshev2.Continuum.log_spectral_summable ha hn hs).sub
    (chebyshev2.Continuum.log_spectral_summable ha hn ht)).norm
  rw [Real.norm_eq_abs] at h
  apply h.trans
  rw [← tsum_mul_left]
  apply Summable.tsum_le_tsum
  · intro j
    rw [Real.norm_eq_abs]
    have hb := chebyshev2.Continuum.log_abs_sub_le
      (show 1 ≤ 1+s/2*a j by nlinarith [mul_nonneg hs (hn j)])
      (show 1 ≤ 1+t/2*a j by nlinarith [mul_nonneg ht (hn j)])
    have he : (1+s/2*a j)-(1+t/2*a j)=(s-t)/2*a j := by ring
    rw [he,abs_mul,abs_div,abs_of_nonneg (hn j)] at hb
    norm_num at hb
    exact hb
  · exact ((chebyshev2.Continuum.log_spectral_summable ha hn hs).sub
      (chebyshev2.Continuum.log_spectral_summable ha hn ht)).norm
  · exact ha.mul_left _

end
end chebyshev2.Calibration
