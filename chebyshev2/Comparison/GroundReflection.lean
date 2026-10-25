import chebyshev2.Filters.ReflectionObservation

/-!
Article: chebyshev2, Lemma 11.
Reflection of the actual spectral ground parameter and coordinate for continuous L1 densities.
Use: `chebyshev2.Comparison.groundCoordinate_reflection` feeds
`chebyshev2.Comparison.Profile.rightLinear_bounds` (right Linear bounds).
Proof chain: `chebyshev2.Comparison.Profile.signed_determinant_comparison` — chebyshev2,
Theorem 3.4; Signed determinant and square-trace comparisons.
-/
namespace chebyshev2.Comparison
noncomputable section
open Set MeasureTheory Filter Real chebyshev2.Filters chebyshev2.GroundState chebyshev2.Sobolev
open scoped Topology
set_option backward.isDefEq.respectTransparency false
variable {m : ℝ → ℝ} {hm : Integrable m} {hn : ∀ x, 0 ≤ m x}
variable (G : GroundWitness hm hn) (hc : Continuous m)
include G hc

/--
The actual derivative at the stated point: `HasDerivAt G.R.a (1-groundParameter hm hn*m
x-(G.R.a x)^2) x`.

Use: `chebyshev2.Comparison.groundLog_c1` uses this derivative formula to establish
smoothness to the stated order: `ContDiff ℝ 1 G.R.a`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates
`chebyshev2.GroundState.locallyAC_hasDerivAt_of_continuous`,
`chebyshev2.GroundState.RiccatiData.continuous` with the arguments shown in the proof.
-/
theorem groundLog_hasDerivAt (x : ℝ) : HasDerivAt G.R.a
    (1-groundParameter hm hn*m x-(G.R.a x)^2) x :=
  locallyAC_hasDerivAt_of_continuous G.R.locally_ac G.R.derivative_ae
    ((continuous_const.sub (continuous_const.mul hc)).sub (G.R.continuous.pow 2)) x

/--
Smoothness to the stated order: `ContDiff ℝ 1 G.R.a`.

Use: `chebyshev2.Comparison.reflectedRiccati` uses this assertion in the displayed
construction of `reflectedRiccati`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem groundLog_c1 : ContDiff ℝ 1 G.R.a := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x => (groundLog_hasDerivAt G hc x).differentiableAt,?_⟩
  have he : deriv G.R.a=fun x => 1-groundParameter hm hn*m x-(G.R.a x)^2 :=
    funext (fun x => (groundLog_hasDerivAt G hc x).deriv)
  rw [he]
  exact (continuous_const.sub (continuous_const.mul hc)).sub (G.R.continuous.pow 2)

/--
Constructs `reflectedRiccati` of type `RiccatiData (reflected m) (groundParameter hm hn)` by
the displayed record fields. Data fields specify the construction; proof fields discharge its
required properties.

Use: `chebyshev2.Comparison.groundParameter_reflection` uses this definition to establish
exact identity `groundParameter (reflected_integrable hm) (reflected_nonneg hn)=groundParameter
hm hn`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.
-/
def reflectedRiccati : RiccatiData (reflected m) (groundParameter hm hn) where
  a := fun x => -G.R.a (-x)
  bound := fun x => by simpa only [abs_neg] using G.R.bound (-x)
  locally_ac a b := ((groundLog_c1 G hc).comp contDiff_neg).neg.contDiffOn.absolutelyContinuousOnInterval
  derivative_ae := Eventually.of_forall (fun x => by
    have h := ((groundLog_hasDerivAt G hc (-x)).comp x (hasDerivAt_neg x)).neg
    convert h using 1
    · rfl
    · dsimp only [reflected]
      ring)

/--
The actual derivative at the stated point: `HasDerivAt G.d ((1-groundParameter hm hn*m
x)*H1.rep G.u x) x`.

Use: `chebyshev2.Comparison.groundCoordinate_reflection` uses this derivative formula to
establish exact identity `Gr.q x=2-G.q (-x)`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates
`chebyshev2.GroundState.locallyAC_hasDerivAt_of_continuous`,
`chebyshev2.GroundState.GroundWitness.d_locallyAC`,
`chebyshev2.GroundState.GroundWitness.ode` with the arguments shown in the proof.
-/
theorem groundSlope_hasDerivAt (x : ℝ) : HasDerivAt G.d
    ((1-groundParameter hm hn*m x)*H1.rep G.u x) x :=
  locallyAC_hasDerivAt_of_continuous G.d_locallyAC G.ode
    ((continuous_const.sub (continuous_const.mul hc)).mul (H1.continuous_rep G.u)) x

/--
Smoothness to the stated order: `ContDiff ℝ 1 G.d`.

Use: `chebyshev2.Comparison.groundCoordinate_reflection` uses this assertion to establish
exact identity `Gr.q x=2-G.q (-x)`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem groundSlope_c1 : ContDiff ℝ 1 G.d := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x => (groundSlope_hasDerivAt G hc x).differentiableAt,?_⟩
  have he : deriv G.d=fun x => (1-groundParameter hm hn*m x)*H1.rep G.u x :=
    funext (fun x => (groundSlope_hasDerivAt G hc x).deriv)
  rw [he]
  exact (continuous_const.sub (continuous_const.mul hc)).mul (H1.continuous_rep G.u)

omit hc in
/--
The stated quantitative bound `SobolevRegular (fun x => H1.rep G.u (-x)) (fun x => -G.d (-x))
where value_memLp`.

Use: `chebyshev2.Comparison.reflectedGround_exists` uses this identity to establish
constructs witnesses with the exact properties `∃ v : H1, H1.rep v=fun x => H1.rep G.u (-x)`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.Sobolev.H1.regular`,
`chebyshev2.GroundState.GroundWitness.d_memLp`,
`chebyshev2.GroundState.GroundWitness.c1` with the arguments shown in the proof.
-/
theorem reflectedGround_regular :
    SobolevRegular (fun x => H1.rep G.u (-x)) (fun x => -G.d (-x)) where
  value_memLp := (H1.regular G.u).value_memLp.comp_measurePreserving (Measure.measurePreserving_neg volume)
  derivative_memLp := (G.d_memLp.comp_measurePreserving (Measure.measurePreserving_neg volume)).neg
  locally_ac a b := (G.c1.comp contDiff_neg).contDiffOn.absolutelyContinuousOnInterval
  derivative_ae := Eventually.of_forall (fun x => by
    convert (G.derivative (-x)).comp x (hasDerivAt_neg x) using 1
    · rfl
    · change -G.d (-x)=(G.R.a (-x)*H1.rep G.u (-x))*(-1)
      dsimp [GroundWitness.d]
      ring)

omit hc in
/--
Constructs witnesses with the exact properties `∃ v : H1, H1.rep v=fun x => H1.rep G.u (-x)`.

Use: `chebyshev2.Comparison.groundCoordinate_reflection` uses this identity to establish
exact identity `Gr.q x=2-G.q (-x)`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.Sobolev.H1.range_iff`,
`chebyshev2.Comparison.reflectedGround_regular` with the arguments shown in the proof.
-/
theorem reflectedGround_exists : ∃ v : H1, H1.rep v=fun x => H1.rep G.u (-x) :=
  (H1.range_iff _).mpr ⟨_,reflectedGround_regular G⟩

/--
Equality of the two actual variational/spectral parameters.

Exact identity `groundParameter (reflected_integrable hm) (reflected_nonneg hn)=groundParameter
hm hn`.

Use: `chebyshev2.Comparison.groundCoordinate_reflection` rewrites with this identity to
establish exact identity `Gr.q x=2-G.q (-x)`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.Filters.reflected_integrable`,
`chebyshev2.Filters.reflected_nonneg`,
`chebyshev2.GroundState.groundParameter_variational` with the arguments shown in the proof.
-/
theorem groundParameter_reflection :
    groundParameter (reflected_integrable hm) (reflected_nonneg hn)=groundParameter hm hn := by
  -- Use the identities/estimates `chebyshev2.Filters.reflected_integrable`,
  -- `chebyshev2.Filters.reflected_nonneg`,
  -- `chebyshev2.GroundState.groundParameter_variational` with the arguments shown in the
  -- proof.
  let hmr := reflected_integrable hm
  let hnr := reflected_nonneg hn
  have hM : 0 < ∫ x, reflected m x := by
    change 0 < ∫ x, m (-x)
    simpa only [integral_neg_eq_self] using G.mass_positive
  have hle : groundParameter hm hn ≤ groundParameter hmr hnr := by
    apply (groundParameter_variational hmr hnr hM _).mp
    intro f
    have he := (reflectedRiccati G hc).square_identity hmr f
    have hp : 0 ≤ ∫ x, (H1.slope f x-(reflectedRiccati G hc).a x*H1.rep f x)^2 :=
      integral_nonneg (fun x => sq_nonneg _)
    linarith
  obtain ⟨v,hv⟩ := reflectedGround_exists G
  have hd : ∀ x, HasDerivAt (H1.rep v) (-G.d (-x)) x := by
    rw [hv]
    intro x
    convert (G.derivative (-x)).comp x (hasDerivAt_neg x) using 1
    · rfl
    · change -G.d (-x)=(G.R.a (-x)*H1.rep G.u (-x))*(-1)
      dsimp [GroundWitness.d]
      ring
  have ho : ∀ᵐ x, HasDerivAt (fun x => -G.d (-x))
      ((1-groundParameter hm hn*reflected m x)*H1.rep v x) x := by
    apply Eventually.of_forall
    intro x
    have h := ((groundSlope_hasDerivAt G hc (-x)).comp x (hasDerivAt_neg x)).neg
    rw [hv]
    convert h using 1
    · rfl
    · dsimp only [reflected]
      ring
  have hac (a b : ℝ) : AbsolutelyContinuousOnInterval (fun x => -G.d (-x)) a b :=
    ((groundSlope_c1 G hc).comp contDiff_neg).neg.contDiffOn.absolutelyContinuousOnInterval
  have he := ode_energy hmr (groundParameter hm hn) v (Eventually.of_forall hd) hac ho
  have hvne : v ≠ 0 := by
    intro hz
    have hp := G.positive 0
    have hzv := congr_fun hv 0
    rw [hz,H1.rep_zero,neg_zero] at hzv
    simp only [Pi.zero_apply] at hzv
    linarith
  have hw : 0 < ∫ x, reflected m x*H1.rep v x^2 := by
    have hp : 0 < ‖v‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hvne)
    have hκ := G.coupling_positive
    nlinarith
  exact le_antisymm ((mul_le_mul_iff_left₀ hw).mp
    (by simpa only [he] using groundParameter_bound hmr hnr hM v)) hle

/--
The reflection formula includes every point of the line.

Exact identity `Gr.q x=2-G.q (-x)`.

Use: `chebyshev2.Calibration.Data.rightFilter_bounds` rewrites with this identity to
establish membership in the specified domain/enclosure: `C.rightFilter hκ s q ∈ Icc (0:ℝ)
(s/κ*(2-q))`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.Filters.reflected_integrable`,
`chebyshev2.Filters.reflected_nonneg`, `chebyshev2.Comparison.reflectedGround_exists`
with the arguments shown in the proof.
-/
theorem groundCoordinate_reflection (Gr : GroundWitness (reflected_integrable hm) (reflected_nonneg hn))
    (x : ℝ) : Gr.q x=2-G.q (-x) := by
  -- Use the identities/estimates `chebyshev2.Filters.reflected_integrable`,
  -- `chebyshev2.Filters.reflected_nonneg`,
  -- `chebyshev2.Comparison.reflectedGround_exists` with the arguments shown in the proof.
  obtain ⟨v,hv⟩ := reflectedGround_exists G
  have hd (x : ℝ) : HasDerivAt (H1.rep v) (-G.d (-x)) x := by
    rw [hv]
    convert (G.derivative (-x)).comp x (hasDerivAt_neg x) using 1
    · rfl
    · change -G.d (-x)=(G.R.a (-x)*H1.rep G.u (-x))*(-1)
      dsimp [GroundWitness.d]
      ring
  have ho : ∀ᵐ x, HasDerivAt (fun x => -G.d (-x))
      ((1-groundParameter (reflected_integrable hm) (reflected_nonneg hn)*reflected m x)*H1.rep v x) x := by
    rw [groundParameter_reflection G hc,hv]
    apply Eventually.of_forall
    intro x
    convert ((groundSlope_hasDerivAt G hc (-x)).comp x (hasDerivAt_neg x)).neg using 1
    · rfl
    · dsimp only [reflected]
      ring
  have he := Gr.coordinate_unique v (by rw [hv]; exact fun x => G.positive (-x)) hd
    (fun a b => ((groundSlope_c1 G hc).comp contDiff_neg).neg.contDiffOn.absolutelyContinuousOnInterval) ho x
  rw [hv,G.coordinate_eq (-x)] at *
  change Gr.q x=2-(1-G.d (-x)/H1.rep G.u (-x))
  change 1-(-G.d (-x))/H1.rep G.u (-x)=Gr.q x at he
  rw [neg_div] at he
  linarith

end
end chebyshev2.Comparison
