import chebyshev2.StateRegion.Attainment
import Mathlib.MeasureTheory.Measure.Map

/-!
Article: chebyshev2, Lemma 8.
C.2 in the original common-measure coordinate z, and the boundary and interior formulas printed in
Proposition 12.
Use: `chebyshev2.StateRegion.Scales.interior_yPlus` feeds
`chebyshev2.StateRegion.Scales.article_interior_bounds` (Proposition 12, literally at an
arbitrary interior moment pair (U0,U1)).
Proof chain: `chebyshev2.StateRegion.Scales.article_interior_bounds` — chebyshev2, Lemma 8;
Parametrization and compactness of the state region.
-/
namespace chebyshev2.StateRegion.Scales
noncomputable section
open Set MeasureTheory
variable (S : Scales)
set_option backward.isDefEq.respectTransparency false

/--
Defines `response` of type `ℝ` by `S.k*(1-z)/(S.k+s*z)`.

Use: `chebyshev2.StateRegion.Scales.f_change` rewrites with this definition to establish
exact identity `S.f (S.change z)=S.response S.b z`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.
-/
def response (s z : ℝ) : ℝ := S.k*(1-z)/(S.k+s*z)

/--
Exact identity `S.change z+S.g z=1`.

Use: `chebyshev2.StateRegion.Scales.g_change` uses this identity to establish exact
identity `S.g (S.change z)=1-z`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem change_add_g {z : ℝ} (hz : z ∈ Icc (0:ℝ) 1) : S.change z+S.g z=1 := by
  have he := (S.E_pos hz.1).ne'
  simp only [change,g]
  field_simp
  dsimp [E,k₀]
  ring

/--
Exact identity `S.g (S.change z)=1-z`.

Use: `chebyshev2.StateRegion.Scales.original_moments_mem` rewrites with this identity to
establish membership in the specified domain/enclosure: `((∫ z, S.response S.a z ∂μ),(∫ z,
S.response S.b z ∂μ),(∫ z, z ∂μ)) ∈ S.normalized`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.StateRegion.Scales.change_add_g`,
`chebyshev2.StateRegion.Scales.change_mem`,
`chebyshev2.StateRegion.Scales.change_involution` with the arguments shown in the proof.
-/
theorem g_change {z : ℝ} (hz : z ∈ Icc (0:ℝ) 1) : S.g (S.change z)=1-z := by
  have h := S.change_add_g (S.change_mem hz)
  rw [S.change_involution hz] at h
  linarith

/--
Exact identity `S.f (S.change z)=S.response S.b z`.

Use: `chebyshev2.StateRegion.Scales.original_moments_mem` uses this identity to establish
membership in the specified domain/enclosure: `((∫ z, S.response S.a z ∂μ),(∫ z, S.response S.b
z ∂μ),(∫ z, z ∂μ)) ∈ S.normalized`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem f_change {z : ℝ} (hz : z ∈ Icc (0:ℝ) 1) : S.f (S.change z)=S.response S.b z := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hD := (S.D_pos (S.change_mem hz).2).ne'
  have hE := (S.E_pos hz.1).ne'
  have hB : S.k+S.b*z ≠ 0 := ne_of_gt (by
    have hb : 0 < S.b := add_pos S.a_pos S.gap_pos
    exact add_pos_of_pos_of_nonneg S.k_pos (mul_nonneg hb.le hz.1))
  rw [f,response,div_eq_div_iff hD hB]
  simp only [D,change]
  field_simp
  dsimp [E,k₀,k₁,b]
  ring

/--
Measurability of the displayed map: `Measurable S.change`.

Use: `chebyshev2.StateRegion.Scales.mapped_supported` uses this measurability result to
establish establishes the stated eventual or almost-everywhere assertion `∀ᵐ w ∂Measure.map
S.change μ, w ∈ Icc (0:ℝ) 1`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem change_measurable : Measurable S.change := by unfold change E; fun_prop
/--
Measurability of the displayed map: `Measurable S.f`.

Use: `chebyshev2.StateRegion.Scales.original_moments_mem` rewrites with this measurability
result to establish membership in the specified domain/enclosure: `((∫ z, S.response S.a z
∂μ),(∫ z, S.response S.b z ∂μ),(∫ z, z ∂μ)) ∈ S.normalized`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem f_measurable : Measurable S.f := by unfold f D; fun_prop
/--
Measurability of the displayed map: `Measurable S.g`.

Use: `chebyshev2.StateRegion.Scales.original_moments_mem` rewrites with this measurability
result to establish membership in the specified domain/enclosure: `((∫ z, S.response S.a z
∂μ),(∫ z, S.response S.b z ∂μ),(∫ z, z ∂μ)) ∈ S.normalized`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem g_measurable : Measurable S.g := by unfold g E; fun_prop

/--
Establishes the stated eventual or almost-everywhere assertion `∀ᵐ w ∂Measure.map S.change μ, w
∈ Icc (0:ℝ) 1`.

Use: `chebyshev2.StateRegion.Scales.original_moments_mem` uses this assertion to establish
membership in the specified domain/enclosure: `((∫ z, S.response S.a z ∂μ),(∫ z, S.response S.b
z ∂μ),(∫ z, z ∂μ)) ∈ S.normalized`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.StateRegion.Scales.change_measurable`,
`chebyshev2.StateRegion.Scales.change_mem` with the arguments shown in the proof.
-/
theorem mapped_supported {μ : Measure ℝ} (hμ : ∀ᵐ z ∂μ, z ∈ Icc (0:ℝ) 1) :
    ∀ᵐ w ∂Measure.map S.change μ, w ∈ Icc (0:ℝ) 1 :=
  (ae_map_iff S.change_measurable.aemeasurable
    (show MeasurableSet {w : ℝ | w ∈ Icc (0:ℝ) 1} from measurableSet_Icc)).mpr
      (hμ.mono (fun _ hz => S.change_mem hz))
/--
The original three integrands of (22) land in the proved compact moment region. The pushforward
is an actual probability measure.

Membership in the specified domain/enclosure: `((∫ z, S.response S.a z ∂μ),(∫ z, S.response S.b
z ∂μ),(∫ z, z ∂μ)) ∈ S.normalized`.

Use: `chebyshev2.StateRegion.Scales.normalized_iff_original` uses this assertion to
establish equivalence of the displayed criteria: `(u,v,theta) ∈ S.normalized ↔ Nonempty
(S.OriginalWitness u v theta)`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem original_moments_mem {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ z ∂μ, z ∈ Icc (0:ℝ) 1) :
    ((∫ z, S.response S.a z ∂μ),(∫ z, S.response S.b z ∂μ),(∫ z, z ∂μ)) ∈ S.normalized := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  let ν := Measure.map S.change μ
  have : IsProbabilityMeasure ν :=
    (Measure.isProbabilityMeasure_map_iff S.change_measurable.aemeasurable).mpr inferInstance
  have hν := S.mapped_supported hμ
  have h := S.moments_mem_normalized hν
  have h₀ : (∫ w, w ∂ν) = ∫ z, S.response S.a z ∂μ := by
    calc
      _ = ∫ z, S.change z ∂μ := integral_map S.change_measurable.aemeasurable
        (show AEStronglyMeasurable (fun w : ℝ => w) ν from measurable_id.aestronglyMeasurable)
      _ = _ := rfl
  have h₁ : (∫ w, S.f w ∂ν) = ∫ z, S.response S.b z ∂μ := by
    rw [integral_map S.change_measurable.aemeasurable S.f_measurable.aestronglyMeasurable]
    exact integral_congr_ae (hμ.mono (fun _ hz => S.f_change hz))
  have h₂ : 1-(∫ w, S.g w ∂ν) = ∫ z, z ∂μ := by
    rw [integral_map S.change_measurable.aemeasurable S.g_measurable.aestronglyMeasurable]
    rw [integral_congr_ae (hμ.mono (fun _ hz => S.g_change hz)),
      integral_sub (integrable_const _) (coord_integrable hμ)]
    simp
  rw [h₀,h₁,h₂] at h
  exact h

/--
Exact identity `1-(∫ w, S.g w ∂μ)=S.k*(1-u)/S.E u`.

Use: `chebyshev2.StateRegion.Scales.mean_one_boundary` uses this identity to establish
exact identity `1-(∫ w, S.g w ∂μ)=0`.

Article: chebyshev2, Lemma 8 via `chebyshev2.StateRegion.Scales.mean_zero_boundary`.

Proof: Use the identities/estimates `chebyshev2.StateRegion.Scales.mean_mem`,
`chebyshev2.StateRegion.Scales.sharp_moment_bounds`,
`chebyshev2.StateRegion.Scales.theta_at_zero` with the arguments shown in the proof.
-/
theorem lower_boundary {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ w ∂μ, w ∈ Icc (0:ℝ) 1) {u : ℝ}
    (hmean : (∫ w, w ∂μ)=u) (hf : (∫ w, S.f w ∂μ)=S.f u) :
    1-(∫ w, S.g w ∂μ)=S.k*(1-u)/S.E u := by
  -- Use the identities/estimates `chebyshev2.StateRegion.Scales.mean_mem`,
  -- `chebyshev2.StateRegion.Scales.sharp_moment_bounds`,
  -- `chebyshev2.StateRegion.Scales.theta_at_zero` with the arguments shown in the proof.
  have hu : u ∈ Icc (0:ℝ) 1 := hmean ▸ mean_mem hμ
  have hf' : (∫ w, S.f w ∂μ)=S.V u 0 := by simpa [V] using hf
  have hb := S.sharp_moment_bounds hμ hu ⟨le_rfl,zero_le_one⟩ hmean hf'
  rw [(S.theta_at_zero hu).1,(S.theta_at_zero hu).2] at hb
  exact le_antisymm hb.2 hb.1

/--
Exact identity `1-(∫ w, S.g w ∂μ)=1-u`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 8.

Proof: Use the identities/estimates `chebyshev2.StateRegion.Scales.mean_mem`,
`chebyshev2.StateRegion.Scales.sharp_moment_bounds`,
`chebyshev2.StateRegion.Scales.theta_at_one` with the arguments shown in the proof.
-/
theorem upper_boundary {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ w ∂μ, w ∈ Icc (0:ℝ) 1) {u : ℝ}
    (hmean : (∫ w, w ∂μ)=u) (hf : (∫ w, S.f w ∂μ)=u) :
    1-(∫ w, S.g w ∂μ)=1-u := by
  -- Use the identities/estimates `chebyshev2.StateRegion.Scales.mean_mem`,
  -- `chebyshev2.StateRegion.Scales.sharp_moment_bounds`,
  -- `chebyshev2.StateRegion.Scales.theta_at_one` with the arguments shown in the proof.
  have hu : u ∈ Icc (0:ℝ) 1 := hmean ▸ mean_mem hμ
  have hf' : (∫ w, S.f w ∂μ)=S.V u 1 := by simpa [V] using hf
  have hb := S.sharp_moment_bounds hμ hu ⟨zero_le_one,le_rfl⟩ hmean hf'
  rw [(S.theta_at_one hu).1,(S.theta_at_one hu).2] at hb
  exact le_antisymm hb.2 hb.1

/--
Exact identity `S.yMinus u t=(S.k₁*S.V u t-S.k₀*u)/(S.gap*S.V u t)`.

Use: `chebyshev2.StateRegion.Scales.article_interior_bounds` rewrites with this identity to
establish the bound stated in that declaration.

Article: chebyshev2, Lemma 8 via `chebyshev2.StateRegion.Scales.article_interior_bounds`.

Proof: Use the identities/estimates `chebyshev2.StateRegion.Scales.k₀_pos`,
`chebyshev2.StateRegion.Scales.D_pos`, `chebyshev2.StateRegion.Scales.V_bounds` with
the arguments shown in the proof.
-/
theorem interior_yMinus {u t : ℝ} (hu : u ∈ Ioo (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1) :
    S.yMinus u t=(S.k₁*S.V u t-S.k₀*u)/(S.gap*S.V u t) := by
  have hf : 0 < S.f u := div_pos (mul_pos S.k₀_pos hu.1) (S.D_pos hu.2.le)
  have hv : 0 < S.V u t := hf.trans_le (S.V_bounds ⟨hu.1.le,hu.2.le⟩ ht).1
  apply (eq_div_iff (mul_pos S.gap_pos hv).ne').mpr
  have hm := S.yMinus_moment ⟨hu.1.le,hu.2.le⟩ ht
  dsimp [D] at hm
  nlinarith

/--
Exact identity `S.yPlus u t=S.k₁*(u-S.V u t)/(S.gap*(1-S.V u t))`.

Use: `chebyshev2.StateRegion.Scales.article_interior_bounds` rewrites with this identity to
establish the bound stated in that declaration.

Article: chebyshev2, Lemma 8 via `chebyshev2.StateRegion.Scales.article_interior_bounds`.

Proof: Use the identities/estimates `chebyshev2.StateRegion.Scales.V_bounds`,
`chebyshev2.StateRegion.Scales.yPlus_moment` with the arguments shown in the proof.
-/
theorem interior_yPlus {u t : ℝ} (hu : u ∈ Ioo (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1) :
    S.yPlus u t=S.k₁*(u-S.V u t)/(S.gap*(1-S.V u t)) := by
  have hv : S.V u t < 1 := ((S.V_bounds ⟨hu.1.le,hu.2.le⟩ ht).2).trans_lt hu.2
  apply (eq_div_iff (mul_pos S.gap_pos (sub_pos.mpr hv)).ne').mpr
  have hm := S.yPlus_moment ⟨hu.1.le,hu.2.le⟩ ht
  dsimp [D] at hm
  nlinarith

end
end chebyshev2.StateRegion.Scales
