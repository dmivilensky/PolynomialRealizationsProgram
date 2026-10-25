import chebyshev2.StateRegion.Interpolation
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
Article: chebyshev2, Lemma 8.
The complete two-filter region, using the exact tangent remainder rather than assuming a Jensen
equality theorem for the rational function.
Use: `chebyshev2.StateRegion.Scales.third_moment_bounds` feeds
`chebyshev2.StateRegion.Scales.sharp_moment_bounds` (Sharp three-moment bounds on the entire
closed square, with all degenerate faces included).
Proof chain: `chebyshev2.Calibration.Data.energy_ge_spectral_bound` — chebyshev2, Theorem 3.5;
Pointwise cubic-conjugate criterion, gauge invariance and regular price.
-/
namespace chebyshev2.StateRegion.Scales
noncomputable section
open Set MeasureTheory
variable (S : Scales) {μ : Measure ℝ} [IsProbabilityMeasure μ]
set_option backward.isDefEq.respectTransparency false

/--
Exact identity `(∫ w, a+b*F w ∂μ) = a+b*(∫ w, F w ∂μ)`.

Use: `chebyshev2.StateRegion.Scales.third_moment_bounds` rewrites with this identity to
establish the stated quantitative bound `S.lowerB yLo*(∫ w, w ∂μ)+S.lowerC yLo*(∫ w, S.f w ∂μ)
≤ ∫ w, S.g w ∂μ ∧ (∫ w, S.g w ∂μ) ≤ 1+S.upperB yHi*((∫ w, w ∂μ)-1)+S.upperC yHi*((∫ w, S.f w
∂μ)-1)`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
private theorem integral_affine {F : ℝ → ℝ} (hF : Integrable F μ) (a b : ℝ) :
    (∫ w, a+b*F w ∂μ) = a+b*(∫ w, F w ∂μ) := by
  calc
    _ = (∫ _ : ℝ, a ∂μ)+(∫ w, b*F w ∂μ) := integral_add (integrable_const _) (hF.const_mul _)
    _ = a+b*(∫ w, F w ∂μ) := by
      rw [integral_const_mul]
      simp

/--
Exact identity `(∫ w, F w-a ∂μ) = (∫ w, F w ∂μ)-a`.

Use: `chebyshev2.StateRegion.Scales.third_moment_bounds` rewrites with this identity to
establish the stated quantitative bound `S.lowerB yLo*(∫ w, w ∂μ)+S.lowerC yLo*(∫ w, S.f w ∂μ)
≤ ∫ w, S.g w ∂μ ∧ (∫ w, S.g w ∂μ) ≤ 1+S.upperB yHi*((∫ w, w ∂μ)-1)+S.upperC yHi*((∫ w, S.f w
∂μ)-1)`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
private theorem integral_centered {F : ℝ → ℝ} (hF : Integrable F μ) (a : ℝ) :
    (∫ w, F w-a ∂μ) = (∫ w, F w ∂μ)-a := by
  calc
    _ = (∫ w, F w ∂μ)-(∫ _ : ℝ, a ∂μ) := integral_sub hF (integrable_const _)
    _ = _ := by simp

omit [IsProbabilityMeasure μ] in
/--
Exact identity `(∫ w, a*F w+b*G w ∂μ) = a*(∫ w, F w ∂μ)+b*(∫ w, G w ∂μ)`.

Use: `chebyshev2.StateRegion.Scales.third_moment_bounds` rewrites with this identity to
establish the stated quantitative bound `S.lowerB yLo*(∫ w, w ∂μ)+S.lowerC yLo*(∫ w, S.f w ∂μ)
≤ ∫ w, S.g w ∂μ ∧ (∫ w, S.g w ∂μ) ≤ 1+S.upperB yHi*((∫ w, w ∂μ)-1)+S.upperC yHi*((∫ w, S.f w
∂μ)-1)`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
private theorem integral_two {F G : ℝ → ℝ} (hF : Integrable F μ)
    (hG : Integrable G μ) (a b : ℝ) :
    (∫ w, a*F w+b*G w ∂μ) = a*(∫ w, F w ∂μ)+b*(∫ w, G w ∂μ) := by
  calc
    _ = (∫ w, a*F w ∂μ)+(∫ w, b*G w ∂μ) := integral_add (hF.const_mul _) (hG.const_mul _)
    _ = _ := by rw [integral_const_mul,integral_const_mul]

/--
Integrability of the displayed function: `Integrable (fun w : ℝ => w) μ`.

Use: `chebyshev2.StateRegion.Scales.mean_mem` uses this integrability result to establish
membership in the specified domain/enclosure: `(∫ w, w ∂μ) ∈ Icc (0:ℝ) 1`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.commonMeasure_defect`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem coord_integrable (hμ : ∀ᵐ w ∂μ, w ∈ Icc (0:ℝ) 1) : Integrable (fun w : ℝ => w) μ := by
  apply (integrable_const (1:ℝ)).mono' measurable_id.aestronglyMeasurable
  exact hμ.mono (fun w hw => by simpa only [id_eq, Real.norm_eq_abs, abs_of_nonneg hw.1] using hw.2)

/--
Integrability of the displayed function: `Integrable S.f μ`.

Use: `chebyshev2.StateRegion.Scales.third_moment_bounds` uses this integrability result to
establish the stated quantitative bound `S.lowerB yLo*(∫ w, w ∂μ)+S.lowerC yLo*(∫ w, S.f w ∂μ)
≤ ∫ w, S.g w ∂μ ∧ (∫ w, S.g w ∂μ) ≤ 1+S.upperB yHi*((∫ w, w ∂μ)-1)+S.upperC yHi*((∫ w, S.f w
∂μ)-1)`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.StateRegion.Scales.f_nonneg`,
`chebyshev2.StateRegion.Scales.f_le_self` with the arguments shown in the proof.
-/
theorem f_integrable (hμ : ∀ᵐ w ∂μ, w ∈ Icc (0:ℝ) 1) : Integrable S.f μ := by
  apply (integrable_const (1:ℝ)).mono'
  · exact (by unfold f D; fun_prop : Measurable S.f).aestronglyMeasurable
  · exact hμ.mono (fun w hw => by
      rw [Real.norm_eq_abs, abs_of_nonneg (S.f_nonneg hw)]
      exact (S.f_le_self hw).trans hw.2)

/--
Integrability of the displayed function: `Integrable S.g μ`.

Use: `chebyshev2.StateRegion.Scales.third_moment_bounds` uses this integrability result to
establish the stated quantitative bound `S.lowerB yLo*(∫ w, w ∂μ)+S.lowerC yLo*(∫ w, S.f w ∂μ)
≤ ∫ w, S.g w ∂μ ∧ (∫ w, S.g w ∂μ) ≤ 1+S.upperB yHi*((∫ w, w ∂μ)-1)+S.upperC yHi*((∫ w, S.f w
∂μ)-1)`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.StateRegion.Scales.g_mem` with the
arguments shown in the proof.
-/
theorem g_integrable (hμ : ∀ᵐ w ∂μ, w ∈ Icc (0:ℝ) 1) : Integrable S.g μ := by
  apply (integrable_const (1:ℝ)).mono'
  · exact (by unfold g E; fun_prop : Measurable S.g).aestronglyMeasurable
  · exact hμ.mono (fun w hw => by
      rw [Real.norm_eq_abs, abs_of_nonneg (S.g_mem hw).1]
      exact (S.g_mem hw).2)

/--
Membership in the specified domain/enclosure: `(∫ w, w ∂μ) ∈ Icc (0:ℝ) 1`.

Use: `chebyshev2.StateRegion.Scales.two_moment_bounds` uses this assertion to establish the
stated quantitative bound `S.f (∫ w, w ∂μ) ≤ ∫ w, S.f w ∂μ ∧ (∫ w, S.f w ∂μ) ≤ ∫ w, w ∂μ`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.StateRegion.Scales.coord_integrable` with
the arguments shown in the proof.
-/
theorem mean_mem (hμ : ∀ᵐ w ∂μ, w ∈ Icc (0:ℝ) 1) :
    (∫ w, w ∂μ) ∈ Icc (0:ℝ) 1 := by
  constructor
  · exact integral_nonneg_of_ae (hμ.mono (fun _ hw => hw.1))
  · have h := integral_mono_ae (coord_integrable hμ) (integrable_const (1:ℝ))
      (hμ.mono (fun _ hw => hw.2))
    simpa using h

/--
The complete two-filter region, using the exact tangent remainder rather than assuming a Jensen
equality theorem for the rational function.

The stated quantitative bound `S.f (∫ w, w ∂μ) ≤ ∫ w, S.f w ∂μ ∧ (∫ w, S.f w ∂μ) ≤ ∫ w, w ∂μ`.

Use: `chebyshev2.StateRegion.Scales.mean_one_boundary` uses this bound to establish exact
identity `1-(∫ w, S.g w ∂μ)=0`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.StateRegion.Scales.mean_mem`,
`chebyshev2.StateRegion.Scales.coord_integrable`,
`chebyshev2.StateRegion.Scales.f_integrable` with the arguments shown in the proof.
-/
theorem two_moment_bounds (hμ : ∀ᵐ w ∂μ, w ∈ Icc (0:ℝ) 1) :
    S.f (∫ w, w ∂μ) ≤ ∫ w, S.f w ∂μ ∧ (∫ w, S.f w ∂μ) ≤ ∫ w, w ∂μ := by
  -- Use the identities/estimates `chebyshev2.StateRegion.Scales.mean_mem`,
  -- `chebyshev2.StateRegion.Scales.coord_integrable`,
  -- `chebyshev2.StateRegion.Scales.f_integrable` with the arguments shown in the proof.
  let u := ∫ w, w ∂μ
  have hu := mean_mem hμ
  have hi := coord_integrable hμ
  have hf := S.f_integrable hμ
  constructor
  · have ht : Integrable (fun w => S.f u + S.k₀*S.k₁/(S.D u)^2*(w-u)) μ :=
      (integrable_const _).add ((hi.sub (integrable_const _)).const_mul _)
    have he := integral_mono_ae ht hf (hμ.mono (fun w hw => by
      have hr := S.f_tangent_remainder hu hw
      have hp : 0 ≤ S.k₀*S.k₁*S.gap*(w-u)^2 / ((S.D u)^2*S.D w) := by
        have h₀ := S.k₀_pos
        have h₁ := S.k₁_pos
        have hδ := S.gap_pos
        have hd := S.D_pos hw.2
        positivity
      linarith))
    rw [integral_affine (F := fun w => w-u) (hi.sub (integrable_const u)),
      integral_centered (F := fun w => w) hi] at he
    simpa only [u,sub_self,mul_zero,add_zero] using he
  · exact integral_mono_ae hf hi (hμ.mono (fun _ hw => S.f_le_self hw))

/--
The stated quantitative bound `S.lowerB yLo*(∫ w, w ∂μ)+S.lowerC yLo*(∫ w, S.f w ∂μ) ≤ ∫ w, S.g
w ∂μ ∧ (∫ w, S.g w ∂μ) ≤ 1+S.upperB yHi*((∫ w, w ∂μ)-1)+S.upperC yHi*((∫ w, S.f w ∂μ)-1)`.

Use: `chebyshev2.StateRegion.Scales.sharp_moment_bounds` uses this bound to establish
membership in the specified domain/enclosure: `1-(∫ w, S.g w ∂μ) ∈ Icc (S.thetaMinus u t)
(S.thetaPlus u t)`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.StateRegion.Scales.coord_integrable`,
`chebyshev2.StateRegion.Scales.f_integrable`,
`chebyshev2.StateRegion.Scales.g_integrable` with the arguments shown in the proof.
-/
theorem third_moment_bounds (hμ : ∀ᵐ w ∂μ, w ∈ Icc (0:ℝ) 1)
    {yLo yHi : ℝ} (hyLo : yLo ∈ Icc (0:ℝ) 1) (hyHi : yHi ∈ Icc (0:ℝ) 1) :
    S.lowerB yLo*(∫ w, w ∂μ)+S.lowerC yLo*(∫ w, S.f w ∂μ) ≤ ∫ w, S.g w ∂μ ∧
    (∫ w, S.g w ∂μ) ≤
      1+S.upperB yHi*((∫ w, w ∂μ)-1)+S.upperC yHi*((∫ w, S.f w ∂μ)-1) := by
  -- Use the identities/estimates `chebyshev2.StateRegion.Scales.coord_integrable`,
  -- `chebyshev2.StateRegion.Scales.f_integrable`,
  -- `chebyshev2.StateRegion.Scales.g_integrable` with the arguments shown in the proof.
  have hi := coord_integrable hμ
  have hf := S.f_integrable hμ
  have hg := S.g_integrable hμ
  -- Establish hl as the integrability justification for the later integral estimates or
  -- changes of order.
  have hl : Integrable (S.lowerInterpolant yLo) μ :=
    (hi.const_mul _).add (hf.const_mul _)
  -- Establish hu as the integrability justification for the later integral estimates or
  -- changes of order.
  have hu : Integrable (S.upperInterpolant yHi) μ :=
    ((integrable_const _).add ((hi.sub (integrable_const _)).const_mul _)).add
      ((hf.sub (integrable_const _)).const_mul _)
  constructor
  · have h := integral_mono_ae hl hg (hμ.mono (fun _ hw => S.lowerInterpolant_le hyLo hw))
    change (∫ w, S.lowerB yLo*w+S.lowerC yLo*S.f w ∂μ) ≤ _ at h
    rw [integral_two hi hf] at h
    exact h
  · have h := integral_mono_ae hg hu (hμ.mono (fun _ hw => S.g_le_upperInterpolant hyHi hw))
    have he : (∫ w, S.upperInterpolant yHi w ∂μ) =
        1+S.upperB yHi*((∫ w, w ∂μ)-1)+S.upperC yHi*((∫ w, S.f w ∂μ)-1) := by
      change (∫ w, (1+S.upperB yHi*(w-1))+S.upperC yHi*(S.f w-1) ∂μ) = _
      calc
        _ = (∫ w, 1+S.upperB yHi*(w-1) ∂μ)+(∫ w, S.upperC yHi*(S.f w-1) ∂μ) :=
          integral_add ((integrable_const _).add ((hi.sub (integrable_const _)).const_mul _))
            ((hf.sub (integrable_const _)).const_mul _)
        _ = _ := by
          rw [integral_affine (F := fun w => w-1) (hi.sub (integrable_const _)),
            integral_const_mul, integral_centered (F := fun w => w) hi,
            integral_centered (F := S.f) hf]
    rw [he] at h
    exact h

end
end chebyshev2.StateRegion.Scales
