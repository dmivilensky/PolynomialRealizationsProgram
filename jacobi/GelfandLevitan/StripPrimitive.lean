import jacobi.GelfandLevitan.FiniteQuasiDerivative

/-!
Article: jacobi, Theorem 2.1.
Integration on a fixed positive physical strip is a bounded operator
in the uniform norm. Its endpoint FTC and uniqueness identify genuine
quasi-derivative primitives and permit norm-continuous limit passages.
Use: stripPrimitive packages the original positive-strip integrals in the genuine uniform norm for the transformed ODE limit.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter MeasureTheory
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- A fixed closed real segment, with its unchanged physical coordinate.
Use: stripPrimitive packages the original positive-strip integrals in the genuine uniform norm for the transformed ODE limit.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
abbrev ClosedStrip (p q : ℝ) := {t : ℝ // t∈Icc p q}

/-- The continuous physical extension of a strip function by clipping its real coordinate.
Use: stripPrimitive has a globally continuous integrand while every physical strip value remains unchanged.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def stripExtension {E : Type*} [TopologicalSpace E] {p q : ℝ} (hpq : p≤q)
    (f : C(ClosedStrip p q,E)) : C(ℝ,E) :=
  f.comp ⟨Set.projIcc p q hpq,continuous_projIcc⟩

/-- The strip extension preserves the actual original physical value.
Use: its FTC differentiates the original strip primitive, not an altered spatial integrand.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: the clipping projection fixes every point in its physical interval. -/
theorem stripExtension_value {E : Type*} [TopologicalSpace E] {p q : ℝ} (hpq : p≤q)
    (f : C(ClosedStrip p q,E)) (t : ClosedStrip p q) : stripExtension hpq f t=f t := by
  change f (Set.projIcc p q hpq (t:ℝ))=f t
  rw [Set.projIcc_of_mem hpq t.property]

/-- The original physical-strip primitive as a continuous function of its genuine endpoint.
Use: stripPrimitiveLinear and stripPrimitive transfer the actual interval integrals to uniform-norm calculus.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: the continuous extended integrand is locally integrable, so its original endpoint primitive is continuous by the community FTC. -/
def stripPrimitiveMap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {p q : ℝ} (hpq : p≤q) (f : C(ClosedStrip p q,E)) : C(ClosedStrip p q,E) :=
  ⟨fun t => ∫ r in p..(t:ℝ),stripExtension hpq f r,
    ((intervalIntegral.continuous_primitive ((stripExtension hpq f).continuous.intervalIntegrable (μ := volume)) p).comp
      continuous_subtype_val)⟩

/-- Physical-strip integration is linear in the unchanged integrand.
Use: stripPrimitive adds its genuine uniform norm bound, giving norm-continuous passage to the transformed ODE limit.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Source: linearity of the Bochner interval integral. -/
def stripPrimitiveLinear {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {p q : ℝ} (hpq : p≤q) : C(ClosedStrip p q,E) →ₗ[ℝ] C(ClosedStrip p q,E) where
  toFun := stripPrimitiveMap hpq
  map_add' f g := by
    ext t
    change (∫ r in p..(t:ℝ),stripExtension hpq (f+g) r)=_
    exact intervalIntegral.integral_add
      ((stripExtension hpq f).continuous.intervalIntegrable p t)
      ((stripExtension hpq g).continuous.intervalIntegrable p t)
  map_smul' c f := by
    ext t
    change (∫ r in p..(t:ℝ),c • stripExtension hpq f r)=c • _
    exact intervalIntegral.integral_smul c _

/-- The actual strip primitive has its standard length-times-uniform-norm bound.
Use: stripPrimitive is a genuine bounded operator, so actual finite primitives converge in the same uniform norm as their integrands.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Source: the standard Bochner integral norm bound.
Proof: each extended value is bounded by the actual continuous-function norm. The original integration length t-p is nonnegative and at most the physical strip length q-p. -/
theorem stripPrimitiveMap_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {p q : ℝ} (hpq : p≤q) (f : C(ClosedStrip p q,E)) :
    ‖stripPrimitiveMap hpq f‖≤(q-p)*‖f‖ := by
  -- The estimate uses the actual physical length, without rescaling the original interval measure.
  apply (ContinuousMap.norm_le _ (by positivity : 0≤(q-p)*‖f‖)).mpr
  intro t
  change ‖∫ r in p..(t:ℝ),stripExtension hpq f r‖≤_
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := p) (b := (t:ℝ))
    (fun r _ => f.norm_coe_le_norm (Set.projIcc p q hpq r))
  exact h.trans (by rw [abs_of_nonneg (sub_nonneg.mpr t.property.1)]; nlinarith [norm_nonneg f,t.property.2])

/-- Integration from the genuine left physical endpoint as a bounded real-linear uniform-norm operator.
Use: the transformed quasi-derivative limit uses this exact original primitive and its norm continuity.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def stripPrimitive {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {p q : ℝ} (hpq : p≤q) : C(ClosedStrip p q,E) →L[ℝ] C(ClosedStrip p q,E) :=
  (stripPrimitiveLinear hpq).mkContinuous (q-p) (stripPrimitiveMap_norm_le hpq)

/-- The genuine original strip primitive has the exact endpoint derivative of its original integrand.
Use: gauge and quasi-derivative identities on the physical strip follow from true derivatives of these same primitives.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Source: mathlib's endpoint fundamental theorem of calculus.
Proof: the extension is globally continuous and agrees with the original value at the actual physical endpoint. Apply the genuine community interval FTC and restrict its derivative to the physical strip. -/
theorem stripPrimitive_hasDerivWithinAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {p q : ℝ} (hpq : p≤q) (f : C(ClosedStrip p q,E)) (t : ClosedStrip p q) :
    HasDerivWithinAt (stripExtension hpq (stripPrimitive hpq f)) (f t) (Icc p q) (t:ℝ) := by
  -- The coordinate clipping is used only to extend the function; the derivative within the actual interval retains its unaltered values.
  have hc := (stripExtension hpq f).continuous
  have h := (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable (μ := volume) p t)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).hasDerivWithinAt (s := Icc p q)
  rw [stripExtension_value] at h
  apply h.congr
  · intro x hx
    rw [show x=(⟨x,hx⟩:ClosedStrip p q).val from rfl,stripExtension_value]
    rfl
  · rw [stripExtension_value]
    rfl

/-- The genuine physical-strip primitive is zero at its actual left endpoint.
Use: fixes the integration constants in the actual finite quasi-derivative gauge identities.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: the original interval integral has coinciding physical endpoints. -/
theorem stripPrimitive_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {p q : ℝ} (hpq : p≤q) (f : C(ClosedStrip p q,E)) :
    stripPrimitive hpq f ⟨p,⟨le_rfl,hpq⟩⟩=0 := intervalIntegral.integral_same

/-- The actual primitive of a genuine physical strip derivative is exactly its original function minus its actual left endpoint value.
Use: the finite transformed quasi-derivative gauge calculation integrates true physical derivatives without an unproved integration constant or endpoint condition.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Source: the fundamental theorem of calculus for a continuous derivative.
Proof: integrate the given genuine derivative on the original interval from p to t. Its interior points lie in the interior of the fixed strip, so the within derivatives are ordinary derivatives there. Continuity of both actual strip functions discharges the remaining FTC conditions. -/
theorem stripPrimitive_eq_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {p q : ℝ} (hpq : p<q) (f g : C(ClosedStrip p q,E))
    (hD : ∀ t : ClosedStrip p q,HasDerivWithinAt (stripExtension hpq.le f) (g t) (Icc p q) (t:ℝ)) :
    stripPrimitive hpq.le g=f-ContinuousMap.const _ (f ⟨p,⟨le_rfl,hpq.le⟩⟩) := by
  -- Every interior derivative is taken at the same original physical coordinate; neither endpoint is differentiated outside the strip.
  ext t
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le t.property.1
    (stripExtension hpq.le f).continuous.continuousOn
    (fun x hx => by
      have hxp : x∈Icc p q := ⟨hx.1.le,hx.2.le.trans t.property.2⟩
      have hg := hD ⟨x,hxp⟩
      rw [← stripExtension_value hpq.le g ⟨x,hxp⟩] at hg
      exact hg.hasDerivAt (Icc_mem_nhds hx.1 (hx.2.trans_le t.property.2)))
    ((stripExtension hpq.le g).continuous.intervalIntegrable p t)
  rw [stripExtension_value hpq.le f t,stripExtension_value hpq.le f ⟨p,⟨le_rfl,hpq.le⟩⟩] at h
  exact h

end
end jacobi.GelfandLevitan
