import chebyshev2.LocalObstruction.TestFunctions
import chebyshev2.LocalObstruction.SineSmooth

/-!
Article: chebyshev2, Theorem 6.1.
Compact smooth amplitude directions at the actual sine density.
Use: `chebyshev2.LocalObstruction.amplitude_correction_direction` feeds
`chebyshev2.LocalObstruction.no_local_lower_bound_of_gradient_with_property` (no local lower
bound of gradient with property).
Proof chain: `chebyshev2.LocalObstruction.theorem_6_1` — chebyshev2, Theorem 6.1; No locally
sharp C1 bound from finitely many spectral observations.
-/
namespace chebyshev2.LocalObstruction
noncomputable section
open Set Real MeasureTheory Filter chebyshev2.SineContinuum
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

/--
Defines `amplitudeDirection` of type `SmoothTest` by `⟨fun x => v x/(2*n x), v.property.1.div
(contDiff_const.mul n_smooth) (fun x => (mul_pos (by norm_num) (n_positive x)).ne'),by apply
v.property.2.mono intro x hx hz apply hx change v x/(2*n x)=0 rw [hz,zero_div]⟩`.

Use: `chebyshev2.LocalObstruction.amplitudeDirection_tangent` uses this definition to
establish exact identity `(∫ x, n x*amplitudeDirection v x)=0`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.
-/
def amplitudeDirection (v : SmoothTest) : SmoothTest :=
  ⟨fun x => v x/(2*n x),
    v.property.1.div (contDiff_const.mul n_smooth)
      (fun x => (mul_pos (by norm_num) (n_positive x)).ne'),by
      apply v.property.2.mono
      intro x hx hz
      apply hx
      change v x/(2*n x)=0
      rw [hz,zero_div]⟩

 /--
Exact identity `(∫ x, n x*amplitudeDirection v x)=0`.

Use: `chebyshev2.LocalObstruction.no_local_lower_bound_of_gradient` uses this identity to
establish constructs witnesses with the exact properties `∃ f : ℝ → ℝ, ContDiff ℝ ∞ (fun x => f
x-m x) ∧ HasCompactSupport (fun x => f x-m x) ∧ (∀ x, 0≤f x) ∧ (∫ x, f x)=1 ∧ (∫ x, sqrt (f
x))=1 ∧ (∀ x, |f x-m x|<ε) ∧ densityEnergy f<B f`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem amplitudeDirection_tangent (v : SmoothTest) (hv : (∫ x, v x)=0) :
    (∫ x, n x*amplitudeDirection v x)=0 := by
  have he : (fun x => n x*amplitudeDirection v x)=fun x => v x/2 := by
    funext x
    change n x*(v x/(2*n x))=v x/2
    field_simp [(n_positive x).ne']
  rw [he,integral_div,hv,zero_div]

 /--
Constructs witnesses with the exact properties `∃ w : SmoothTest, (∫ x, w x)=0 ∧ 0<(∫ x, n x*w
x)`.

Use: `chebyshev2.LocalObstruction.no_local_lower_bound_of_gradient` uses this identity to
establish constructs witnesses with the exact properties `∃ f : ℝ → ℝ, ContDiff ℝ ∞ (fun x => f
x-m x) ∧ HasCompactSupport (fun x => f x-m x) ∧ (∀ x, 0≤f x) ∧ (∫ x, f x)=1 ∧ (∫ x, sqrt (f
x))=1 ∧ (∀ x, |f x-m x|<ε) ∧ densityEnergy f<B f`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.n_positive`,
`chebyshev2.LocalObstruction.sine_amplitude_tendsto_zero`,
`chebyshev2.SineContinuum.n_continuous` with the arguments shown in the proof.
-/
theorem amplitude_correction_direction :
    ∃ w : SmoothTest, (∫ x, w x)=0 ∧ 0<(∫ x, n x*w x) := by
  -- Use the identities/estimates `chebyshev2.SineContinuum.n_positive`,
  -- `chebyshev2.LocalObstruction.sine_amplitude_tendsto_zero`,
  -- `chebyshev2.SineContinuum.n_continuous` with the arguments shown in the proof.
  have hne : ∃ a b, n a≠n b := by
    have hp := n_positive 0
    obtain ⟨b,hb⟩ := (LocalObstruction.sine_amplitude_tendsto_zero.eventually (gt_mem_nhds hp)).exists
    exact ⟨0,b,by linarith⟩
  obtain ⟨w₀,w₁,h₀,h₁,hd⟩ := independent_normalization_directions n_continuous hne
  let w : SmoothTest := w₀-w₁
  have hw₀ : (∫ x, w x)=0 := by
    have hm : testIntegral (fun _ => 1) continuous_const w=0 := by
      change testIntegral (fun _ => 1) continuous_const (w₀-w₁)=0
      rw [map_sub,h₀,h₁,sub_self]
    simpa [testIntegral] using hm
  have hw : (∫ x, n x*w x)≠0 := by
    have h : testIntegral n n_continuous w≠0 := by
      change testIntegral n n_continuous (w₀-w₁)≠0
      rw [map_sub]
      exact sub_ne_zero.mpr hd
    simpa [testIntegral,mul_comm] using h
  rcases lt_or_gt_of_ne hw with h | h
  · refine ⟨-w,?_,?_⟩
    · change (∫ x, -w x)=0
      rw [integral_neg,hw₀,neg_zero]
    · change 0<(∫ x, n x*(-w x))
      simp only [mul_neg,integral_neg]
      linarith
  · exact ⟨w,hw₀,h⟩

end
end chebyshev2.LocalObstruction
