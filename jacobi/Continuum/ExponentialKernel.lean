import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Asymptotics

/-!
Article: jacobi, Lemma D.1.
Exact L1 normalization of exp(-a|x-y|), for every positive a. The argument uses
ordinary improper exponential integrals and translation invariance of volume.
Source: the elementary exponential integral, formalized with mathlib's FTC.
Use: domination of the truncated second moment and of convolution potentials.
-/
namespace jacobi.Continuum
noncomputable section
open MeasureTheory Real Set Filter Asymptotics

/-- Positive exponential kernels are integrable over the full real line.
Use: domination of the truncated second moment and of convolution potentials.
Article: jacobi, Lemma D.1.
Proof: integrate the positive half-line; continuity and reflection cover the other half. -/
theorem exponential_integrable {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : ℝ => exp (-a*|x|)) := by
  -- Reflection turns the single integrable tail into a global integrability proof.
  have hi : IntegrableOn (fun x : ℝ => exp (-a*|x|)) (Ioi 0) := by
    apply (integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) 0).congr_fun _ measurableSet_Ioi
    intro x hx
    dsimp only
    rw [abs_of_pos (show 0 < x from hx)]
  have hc : Continuous (fun x : ℝ => exp (-a*|x|)) := by fun_prop
  exact hc.locallyIntegrable.integrable_of_isBigO_atTop_of_norm_isNegInvariant
    (Filter.Eventually.of_forall fun x => by simp [Function.comp_def,abs_neg])
    (isBigO_refl _ atTop) ⟨Ioi 0,Ioi_mem_atTop 0,hi⟩

/-- Exact integral of the centered exponential kernel.
Use: the uniform potential bound has the exact factor 2/a.
Article: jacobi, Lemma D.1.
Proof: the two half-line integrals coincide and each is 1/a. -/
theorem exponential_integral {a : ℝ} (ha : 0 < a) :
    (∫ x : ℝ, exp (-a*|x|)) = 2/a := by
  -- Compute the positive tail and reflect it before adding both half-lines.
  have hi := exponential_integrable ha
  have hr : (∫ x : ℝ in Ioi 0, exp (-a*|x|)) = 1/a := by
    calc
      _ = ∫ x : ℝ in Ioi 0, exp (-a*x) :=
        setIntegral_congr_fun measurableSet_Ioi (fun x hx => by rw [abs_of_pos hx])
      _ = _ := by rw [integral_exp_mul_Ioi (neg_neg_of_pos ha)]; simp
  have hl : (∫ x : ℝ in Iic 0, exp (-a*|x|)) = 1/a := by
    have h := integral_comp_neg_Iic 0 (fun x : ℝ => exp (-a*|x|))
    simpa only [abs_neg,neg_zero,hr] using h
  rw [← intervalIntegral.integral_Iic_add_Ioi (b := 0) hi.integrableOn hi.integrableOn,hl,hr]
  ring

/-- Every translated/reflected exponential kernel is integrable.
Use: pointwise convolution estimates at arbitrary centers x.
Article: jacobi, Lemma D.1.
Proof: Lebesgue measure is invariant under y↦x-y. -/
theorem exponential_shift_integrable {a : ℝ} (ha : 0 < a) (x : ℝ) :
    Integrable (fun y : ℝ => exp (-a*|x-y|)) :=
  (exponential_integrable ha).comp_sub_left x

/-- Translation does not change the exact exponential-kernel mass.
Use: bounds a convolution by the essential supremum of its density.
Article: jacobi, Lemma D.1.
Proof: apply translation/reflection invariance to the centered integral. -/
theorem exponential_shift_integral {a : ℝ} (ha : 0 < a) (x : ℝ) :
    (∫ y : ℝ, exp (-a*|x-y|)) = 2/a := by
  rw [integral_sub_left_eq_self (fun y : ℝ => exp (-a*|y|)) volume x,exponential_integral ha]

end
end jacobi.Continuum
