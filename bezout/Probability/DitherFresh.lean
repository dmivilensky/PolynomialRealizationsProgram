import bezout.Probability.Dither
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Independence.Basic

/-!
Article: bezout, fresh subtractive dithers at adaptively chosen gradient queries.
Use: an input may depend arbitrarily and measurably on the whole past;
the newly rounded error still has the same uniform law and is independent
of that past. Its actual conditional moments therefore have the stated values.
Proof: the input-dependent circle rotation is a measure-preserving skew product.
-/

namespace bezout.Probability.Dither
noncomputable section
open MeasureTheory ProbabilityTheory
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- A fresh scalar dither preserves the joint law of past and quantization error. -/
theorem fresh_preserving (g : Ω → ℝ) (hg : Measurable g) :
    MeasurePreserving (fun p : Ω×ℝ => (p.1, normalizedError (g p.1) p.2))
      (μ.prod law) (μ.prod law) := by
  have hgm : Measurable (fun p : Ω×ℝ => normalizedError (g p.1) p.2) := by
    change Measurable (fun p : Ω×ℝ => representative ((-(g p.1+p.2):ℝ) : AddCircle (1:ℝ)))
    exact representative_preserving.measurable.comp
      (AddCircle.measurable_mk'.comp (((hg.comp measurable_fst).add measurable_snd).neg))
  have he := (MeasurePreserving.id μ).skew_product
    (g := fun ω u => normalizedError (g ω) u) (μc := law) (μd := law) hgm
    (Filter.Eventually.of_forall (fun ω => (normalizedError_preserving (g ω)).map_eq))
  simpa only [id_eq] using he

/-- The fresh rounded error itself has the same centered uniform law for any adaptive input. -/
theorem fresh_error_preserving (g : Ω → ℝ) (hg : Measurable g) :
    MeasurePreserving (fun p : Ω×ℝ => normalizedError (g p.1) p.2) (μ.prod law) law :=
  (measurePreserving_snd (μ := μ) (ν := law)).comp (fresh_preserving μ g hg)

/-- The realized rounded error is independent of every event determined by the past. -/
theorem fresh_independent (g : Ω → ℝ) (hg : Measurable g) :
    IndepFun (Prod.fst : Ω×ℝ → Ω) (fun p => normalizedError (g p.1) p.2) (μ.prod law) := by
  apply (indepFun_iff_map_prod_eq_prod_map_map measurable_fst.aemeasurable
    (fresh_error_preserving μ g hg).measurable.aemeasurable).mpr
  rw [(fresh_preserving μ g hg).map_eq, (measurePreserving_fst (μ := μ) (ν := law)).map_eq,
    (fresh_error_preserving μ g hg).map_eq]

/-- The actual fresh adaptive error has zero ordinary mean. -/
theorem fresh_mean (g : Ω → ℝ) (hg : Measurable g) :
    (∫ p, normalizedError (g p.1) p.2 ∂μ.prod law)=0 := by
  have h := fresh_error_preserving μ g hg
  have he := integral_map (μ := μ.prod law) h.measurable.aemeasurable
    (f := fun x : ℝ => x) (by fun_prop)
  rw [h.map_eq] at he
  simpa only [integral_id] using he.symm

/-- The actual fresh adaptive error has second moment one over twelve. -/
theorem fresh_square (g : Ω → ℝ) (hg : Measurable g) :
    (∫ p, normalizedError (g p.1) p.2^2 ∂μ.prod law)=(1/12:ℝ) := by
  have h := fresh_error_preserving μ g hg
  have he := integral_map (μ := μ.prod law) h.measurable.aemeasurable
    (f := fun x : ℝ => x^2) (by fun_prop)
  rw [h.map_eq] at he
  simpa only [integral_square] using he.symm

/-- Conditional centering holds with respect to the complete previous history. -/
theorem fresh_conditional_mean (g : Ω → ℝ) (hg : Measurable g) :
    (μ.prod law)[(fun p : Ω×ℝ => normalizedError (g p.1) p.2) |
      MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace Ω)] =ᵐ[μ.prod law]
      fun _ => (0:ℝ) := by
  have hm := (fresh_error_preserving μ g hg).measurable
  have he := condExp_indep_eq hm.comap_le measurable_fst.comap_le
    (comap_measurable (fun p : Ω×ℝ => normalizedError (g p.1) p.2)).stronglyMeasurable
    (fresh_independent μ g hg).symm
  simpa only [fresh_mean μ g hg] using he

/-- The exact conditional variance is unchanged by any measurable past-dependent input. -/
theorem fresh_conditional_square (g : Ω → ℝ) (hg : Measurable g) :
    (μ.prod law)[(fun p : Ω×ℝ => normalizedError (g p.1) p.2^2) |
      MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace Ω)] =ᵐ[μ.prod law]
      fun _ => (1/12:ℝ) := by
  have hm := (fresh_error_preserving μ g hg).measurable
  have he := condExp_indep_eq hm.comap_le measurable_fst.comap_le
    ((comap_measurable (fun p : Ω×ℝ => normalizedError (g p.1) p.2)).pow_const 2).stronglyMeasurable
    (fresh_independent μ g hg).symm
  simpa only [fresh_square μ g hg] using he

end
end bezout.Probability.Dither
