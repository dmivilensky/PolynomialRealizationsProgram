import krylov.XR.UnknownConditionalBound

/-!
Article: main_krylov, prop:cond, strict defect improvement.
Use: prove strict monotonicity on the full closed consistency interval,
including its nondifferentiable radical endpoint. Source: the actual
quadratic root identity; no differentiability at a double root is assumed.
-/
namespace krylov.XR
noncomputable section

/-- The actual data-only radius is strictly decreasing in the squared
normalized defect on the entire consistent interval. Article: prop:cond. -/
theorem conditional_root_strictAnti {ω a b : ℝ} (hω : 0<ω) (hω₁ : ω<1)
    (ha : 0≤a) (hab : a<b) (hb : b≤2-2*Real.sqrt (1-ω^2)) :
    -conditionalKlo ω b< -conditionalKlo ω a := by
  have hb₀ : 0≤b := ha.trans hab.le
  have ha' : a≤2-2*Real.sqrt (1-ω^2) := hab.le.trans hb
  obtain ⟨_hda,_hkma,hkman,_hordera,hla,_hhia,hqa,_hqhia,_hkhia⟩ :=
    conditional_endpoint_geometry hω hω₁ ha ha'
  obtain ⟨_hdb,_hkmb,hkmbn,_horderb,hlb,_hhib,hqb,_hqhib,_hkhib⟩ :=
    conditional_endpoint_geometry hω hω₁ hb₀ hb
  have hla' : -conditionalKlo ω a≤ω := by rwa [abs_of_nonpos hkman] at hla
  have hlb' : -conditionalKlo ω b≤ω := by rwa [abs_of_nonpos hkmbn] at hlb
  have hhalf : a≤2*(-conditionalKlo ω a) := by
    unfold conditionalKlo
    nlinarith [Real.sqrt_nonneg (conditionalDiscriminant ω a)]
  by_contra! hle
  have hnon := mul_nonneg (sub_nonneg.mpr hle)
    (show 0≤(-conditionalKlo ω b)+(-conditionalKlo ω a)-a by linarith)
  have hpos := mul_pos (sub_pos.mpr hab) (show 0<1-(-conditionalKlo ω b) by linarith)
  nlinarith

/-- The literal unknown-base radical decreases strictly with the
modulus of the observed defect. Article: main_krylov, prop:cond(b). -/
theorem unknownConditionalRadius_strictAnti {ω a b fresh : ℝ} (hω : 0<ω) (hω₁ : ω<1)
    (ha : 0≤a) (hab : a<b) (hb : b^2≤2-2*Real.sqrt (1-ω^2)) :
    unknownConditionalRadius ω b fresh<unknownConditionalRadius ω a fresh := by
  rw [unknownConditionalRadius_root,unknownConditionalRadius_root]
  have hh := conditional_root_strictAnti hω hω₁ (sq_nonneg a) (by nlinarith : a^2<b^2) hb
  simpa only [add_comm] using add_lt_add_right hh fresh

/-- The intermediate square-root envelope has the same strict defect
improvement on its full genuine feasibility interval. Article: prop:cond(a). -/
theorem conditional_sqrt_strictAnti {ω a b fresh : ℝ} (ha : 0≤a) (hab : a<b)
    (hb : b^2≤ω^2) :
    Real.sqrt (ω^2-b^2)+fresh<Real.sqrt (ω^2-a^2)+fresh := by
  have hh := Real.sqrt_lt_sqrt (sub_nonneg.mpr hb) (by nlinarith : ω^2-b^2<ω^2-a^2)
  linarith

end
end krylov.XR
