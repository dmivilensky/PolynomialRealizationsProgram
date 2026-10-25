import chebyshev2.LocalObstruction.AmplitudeCurve

/-!
Article: chebyshev2, Theorem 6.1.
Actual compact smooth, normalization-preserving perturbations in H.
Use: `chebyshev2.LocalObstruction.curveDensity_uniform_small` feeds
`chebyshev2.LocalObstruction.no_local_lower_bound_of_gradient_with_property` (no local lower
bound of gradient with property).
Proof chain: `chebyshev2.LocalObstruction.theorem_6_1` — chebyshev2, Theorem 6.1; No locally
sharp C1 bound from finitely many spectral observations.
-/
namespace chebyshev2.LocalObstruction
noncomputable section
open Set Real Filter MeasureTheory chebyshev2.SineContinuum
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

 /--
Integrability of the displayed function: `Integrable (curveDensity h w t)`.

Use: a standalone supporting integrability result for the article chain below; no retained
declaration currently has an explicit proof dependency on it.

Article: chebyshev2, Theorem 6.1.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem curveDensity_integrable (h w : SmoothTest) (t : ℝ) : Integrable (curveDensity h w t) := by
  have hi : Integrable (fun x => curveDensity h w t x-m x) :=
    (curveDensity_increment h w t).1.continuous.integrable_of_hasCompactSupport
      (curveDensity_increment h w t).2
  convert! m_integrable.add hi using 1
  funext x
  simp only [Pi.add_apply]
  ring

 /--
Establishes the stated eventual or almost-everywhere assertion `∀ᶠ t in 𝓝 (0:ℝ), (∫ x, sqrt
(curveDensity h w t x))=1`.

Use: `chebyshev2.LocalObstruction.sine_normalized_curve` uses this identity to establish
the identity stated in that declaration.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Prove equality of functions by evaluating both
sides at an arbitrary argument.
-/
theorem curveDensity_sqrt_mass (h w : SmoothTest) (hh : (∫ x, h x)=0)
    (hw₀ : (∫ x, w x)=0) (hw : 0<(∫ x, n x*w x)) :
    ∀ᶠ t in 𝓝 (0:ℝ), (∫ x, sqrt (curveDensity h w t x))=1 := by
  filter_upwards [curveAmplitude_positive h w hw] with t ht
  have he : (fun x => sqrt (curveDensity h w t x))=curveAmplitude h w t := by
    funext x
    exact sqrt_sq (ht x).le
  rw [he,curveAmplitude_mass h w hh hw₀]

 /--
Establishes the stated eventual or almost-everywhere assertion `∀ᶠ t in 𝓝 (0:ℝ), ∀ x,
|curveDensity h w t x-m x|<ε`.

Use: `chebyshev2.LocalObstruction.sine_normalized_curve` uses this bound to establish the
identity stated in that declaration.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Separate `x ∈ K` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Intersect the eventual or almost-everywhere hypotheses, then prove the
asserted relation at an arbitrary point in that intersection.
-/
theorem curveDensity_uniform_small (h w : SmoothTest) (hw : 0<(∫ x, n x*w x))
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ t in 𝓝 (0:ℝ), ∀ x, |curveDensity h w t x-m x|<ε := by
  -- Separate `x ∈ K` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  let K := tsupport (h : ℝ → ℝ) ∪ tsupport (w : ℝ → ℝ)
  have hK : IsCompact K := h.property.2.union w.property.2
  -- Establish continuity hc before using the function at limits or in calculus arguments.
  have hc : ContinuousAt (curveCorrection h w) 0 := (curveCorrection_derivative h w hw).continuousAt
  have hlocal : ∀ x ∈ K, ∀ᶠ p : ℝ × ℝ in 𝓝 (0,x),
      |curveDensity h w p.1 p.2-m p.2|<ε := by
    intro x _
    have ha := hc.comp (f := Prod.fst) (x := ((0:ℝ),x)) continuous_fst.continuousAt
    have hn := n_continuous.continuousAt.comp (f := Prod.snd) (x := ((0:ℝ),x)) continuous_snd.continuousAt
    have hh := h.property.1.continuous.continuousAt.comp (f := Prod.snd) (x := ((0:ℝ),x)) continuous_snd.continuousAt
    have hj := w.property.1.continuous.continuousAt.comp (f := Prod.snd) (x := ((0:ℝ),x)) continuous_snd.continuousAt
    have hm := m_continuous.continuousAt.comp (f := Prod.snd) (x := ((0:ℝ),x)) continuous_snd.continuousAt
    -- Establish continuity hcont before using the function at limits or in calculus arguments.
    have hcont : ContinuousAt (fun p : ℝ × ℝ => |curveDensity h w p.1 p.2-m p.2|) (0,x) :=
      ((((hn.add (continuous_fst.continuousAt.mul hh)).add (ha.mul hj)).pow 2).sub hm).abs
    exact hcont.eventually (p := fun z : ℝ => z<ε)
      (by simpa only [curveDensity_zero,sub_self,abs_zero] using gt_mem_nhds hε)
  have he := hK.eventually_forall_of_forall_eventually
    (P := fun t x => |curveDensity h w t x-m x|<ε) hlocal
  filter_upwards [he] with t ht x
  by_cases hx : x ∈ K
  · exact ht x hx
  · have hh : h x=0 := image_eq_zero_of_notMem_tsupport (fun hi => hx (Or.inl hi))
    have hw : w x=0 := image_eq_zero_of_notMem_tsupport (fun hi => hx (Or.inr hi))
    simpa only [curveDensity,curveAmplitude,hh,hw,mul_zero,add_zero,m,sub_self,abs_zero] using hε

 /--
Constructs witnesses with the exact properties `∃ w : SmoothTest, (∀ x, HasDerivAt (fun t =>
curveDensity (amplitudeDirection v) w t x) (v x) 0) ∧ (∀ ε : ℝ, 0<ε → ∀ᶠ t in 𝓝 (0:ℝ), (∀ x,
0≤curveDensity (amplitudeDirection v) w t x) ∧ (∫ x, curveDensity (amplitudeDirection v) w t
x)=1 ∧ (∫ x, sqrt (curveDensity (amplitudeDirection v) w t x))=1 ∧ ∀ x, |curveDensity
(amplitudeDirection v) w t x-m x|<ε)`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Theorem 6.1.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Clear the denominators using the available nonzero
hypotheses, then verify the remaining algebraic identity.
-/
theorem sine_normalized_curve (v : SmoothTest) (hv : (∫ x, v x)=0)
    (hv₁ : (∫ x, v x/(2*n x))=0) :
    ∃ w : SmoothTest,
      (∀ x, HasDerivAt (fun t => curveDensity (amplitudeDirection v) w t x) (v x) 0) ∧
      (∀ ε : ℝ, 0<ε → ∀ᶠ t in 𝓝 (0:ℝ),
        (∀ x, 0≤curveDensity (amplitudeDirection v) w t x) ∧
        (∫ x, curveDensity (amplitudeDirection v) w t x)=1 ∧
        (∫ x, sqrt (curveDensity (amplitudeDirection v) w t x))=1 ∧
        ∀ x, |curveDensity (amplitudeDirection v) w t x-m x|<ε) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  obtain ⟨w,hw₀,hw⟩ := amplitude_correction_direction
  refine ⟨w,?_,?_⟩
  · intro x
    convert! curveDensity_derivative (amplitudeDirection v) w hw x using 1
    change v x=2*n x*(v x/(2*n x))
    field_simp [(n_positive x).ne']
  · intro ε hε
    filter_upwards [curveAmplitude_positive (amplitudeDirection v) w hw,
      curveDensity_mass (amplitudeDirection v) w (amplitudeDirection_tangent v hv) hw,
      curveDensity_sqrt_mass (amplitudeDirection v) w hv₁ hw₀ hw,
      curveDensity_uniform_small (amplitudeDirection v) w hw hε] with t _ hM hR hsmall
    exact ⟨fun x => sq_nonneg _,hM,hR,hsmall⟩

end
end chebyshev2.LocalObstruction
