import jacobi.Rearrangement.Polarization

/-!
Article: jacobi, Appendix D.1.
Integrating the orbit of two independent reflections gives four times the
original integral. Absolute integrability is transported by actual
measure-preserving maps; the factor four is therefore an integral identity,
not a formal symmetry assumption.
Source: Haar invariance of Lebesgue measure and product measures in mathlib.
Use: reduces the Riesz polarization inequality to pointwise four-value algebra.
-/
namespace jacobi.Rearrangement
noncomputable section
open MeasureTheory
set_option backward.isDefEq.respectTransparency false

/-- The four values in an orbit of two independent real reflections.
Use: reduces the Riesz polarization inequality to pointwise four-value algebra.
Article: jacobi, Appendix D.1 (rearrangement).
-/
def orbitFour (F : ℝ × ℝ → ℝ) (a x y : ℝ) : ℝ :=
  F (x,y)+F (reflect a x,y)+F (x,reflect a y)+F (reflect a x,reflect a y)

/-- Reflecting the first coordinate merely permutes its four-point orbit.
Use: reduces arbitrary integration points to the preferred half-line.
Article: jacobi, Appendix D.1 (rearrangement).
Proof: cancel double reflections and commute the four real summands. -/
@[simp] theorem orbitFour_reflect_left (F : ℝ × ℝ → ℝ) (a x y : ℝ) :
    orbitFour F a (reflect a x) y=orbitFour F a x y := by
  simp only [orbitFour,reflect_reflect]
  ring

/-- Reflecting the second coordinate merely permutes its four-point orbit.
Use: reduces the second integration point to the preferred half-line as well.
Article: jacobi, Appendix D.1 (rearrangement).
Proof: cancel double reflections and commute the four real summands. -/
@[simp] theorem orbitFour_reflect_right (F : ℝ × ℝ → ℝ) (a x y : ℝ) :
    orbitFour F a x (reflect a y)=orbitFour F a x y := by
  simp only [orbitFour,reflect_reflect]
  ring

/-- Each of the three nontrivial plane reflections preserves the product Lebesgue measure.
Use: proves integrability and exact integral identities for four-point orbit averages.
Article: jacobi, Appendix D.1 (rearrangement).
Proof: take products of the real reflection map and the identity map. -/
theorem plane_reflections_preserve (a : ℝ) :
    MeasurePreserving (fun z : ℝ × ℝ => (reflect a z.1,z.2)) (volume.prod volume) (volume.prod volume) ∧
    MeasurePreserving (fun z : ℝ × ℝ => (z.1,reflect a z.2)) (volume.prod volume) (volume.prod volume) ∧
    MeasurePreserving (fun z : ℝ × ℝ => (reflect a z.1,reflect a z.2))
      (volume.prod volume) (volume.prod volume) := by
  have hr := volume.measurePreserving_sub_left (2*a)
  exact ⟨hr.prod (MeasurePreserving.id volume),(MeasurePreserving.id volume).prod hr,hr.prod hr⟩

/-- Absolute integrability is preserved by summing the four reflected copies.
Use: licenses integration of the pointwise Riesz orbit comparison.
Article: jacobi, Appendix D.1 (rearrangement).
Proof: transport integrability by each product reflection, then add the four L1 functions. -/
theorem orbitFour_integrable {F : ℝ × ℝ → ℝ}
    (hF : Integrable F (volume.prod volume)) (a : ℝ) :
    Integrable (fun z : ℝ × ℝ => orbitFour F a z.1 z.2) (volume.prod volume) := by
  -- Product reflection preserves the full measure, so it also preserves genuine integrability.
  obtain ⟨hL,hR,hB⟩ := plane_reflections_preserve a
  have hiL := (hL.integrable_comp hF.aestronglyMeasurable).mpr hF
  have hiR := (hR.integrable_comp hF.aestronglyMeasurable).mpr hF
  have hiB := (hB.integrable_comp hF.aestronglyMeasurable).mpr hF
  exact ((hF.add hiL).add hiR).add hiB

/-- The four-point orbit integrates to exactly four times the original integral.
Use: cancels orbit multiplicity in the actual two-density Riesz polarization theorem.
Article: jacobi, Appendix D.1 (rearrangement).
Proof: each reflection is a measure-preserving measurable equivalence, so all
four integrals agree. Absolute integrability licenses their sum. -/
theorem integral_orbitFour {F : ℝ × ℝ → ℝ}
    (hF : Integrable F (volume.prod volume)) (a : ℝ) :
    (∫ z : ℝ × ℝ, orbitFour F a z.1 z.2 ∂volume.prod volume) =
      4*(∫ z, F z ∂volume.prod volume) := by
  -- Explicit measurable equivalences justify the change of variables, including the whole plane.
  obtain ⟨hL,hR,hB⟩ := plane_reflections_preserve a
  have hiL := (hL.integrable_comp hF.aestronglyMeasurable).mpr hF
  have hiR := (hR.integrable_comp hF.aestronglyMeasurable).mpr hF
  have hiB := (hB.integrable_comp hF.aestronglyMeasurable).mpr hF
  let eL := (MeasurableEquiv.subLeft (2*a)).prodCongr (MeasurableEquiv.refl ℝ)
  let eR := (MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.subLeft (2*a))
  let eB := (MeasurableEquiv.subLeft (2*a)).prodCongr (MeasurableEquiv.subLeft (2*a))
  have heL := hL.integral_comp eL.measurableEmbedding F
  have heR := hR.integral_comp eR.measurableEmbedding F
  have heB := hB.integral_comp eB.measurableEmbedding F
  change (∫ z, F (reflect a z.1,z.2) ∂volume.prod volume)=∫ z, F z ∂volume.prod volume at heL
  change (∫ z, F (z.1,reflect a z.2) ∂volume.prod volume)=∫ z, F z ∂volume.prod volume at heR
  change (∫ z, F (reflect a z.1,reflect a z.2) ∂volume.prod volume)=∫ z, F z ∂volume.prod volume at heB
  change Integrable (fun z : ℝ × ℝ => F (reflect a z.1,z.2)) (volume.prod volume) at hiL
  change Integrable (fun z : ℝ × ℝ => F (z.1,reflect a z.2)) (volume.prod volume) at hiR
  change Integrable (fun z : ℝ × ℝ => F (reflect a z.1,reflect a z.2)) (volume.prod volume) at hiB
  change (∫ z : ℝ × ℝ, ((F z+F (reflect a z.1,z.2))+F (z.1,reflect a z.2))+
    F (reflect a z.1,reflect a z.2) ∂volume.prod volume)=_
  have h1 := integral_add hF hiL
  have h2 := integral_add (hF.add hiL) hiR
  have h3 := integral_add ((hF.add hiL).add hiR) hiB
  simp only [Pi.add_apply] at h1 h2 h3
  rw [h3,h2,h1,heL,heR,heB]
  ring

end
end jacobi.Rearrangement
