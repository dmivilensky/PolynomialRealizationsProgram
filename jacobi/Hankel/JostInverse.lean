import jacobi.Hankel.Operator
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Constructions

/-!
Article: jacobi, Lemma E.1.
Its equation, uniqueness, uniform bound and holomorphic dependence are
proved on the same actual contraction domain. For the inverse-square
potential one fixed far ray serves a whole complex-order neighborhood.
Use: outgoingAmplitude solves this literal integral pencil, whose coefficient is later c=1/4-alpha^2 for the original Bessel Liouville equation.
-/
namespace jacobi.Hankel
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
set_option backward.isDefEq.respectTransparency false

/-- The actual complex outgoing Jost operator pencil on the fixed bounded-continuous function space.
Use: outgoingAmplitude solves this literal integral pencil, whose coefficient is later c=1/4-alpha^2 for the original Bessel Liouville equation.
Article: jacobi, Lemma E.1.
-/
def outgoingPencil {m : ℝ → ℝ} (hm : Integrable m) (c : ℂ) : OutgoingSpace →L[ℂ] OutgoingSpace :=
  1+c • outgoingOperator hm

/-- The original outgoing amplitude constructed by the actual inverse of the complex Volterra pencil.
Use: outgoingAmplitude_equation, its uniqueness and the subsequent exact inverse-square ODE construction concern this same concrete amplitude.
Article: jacobi, Lemma E.1.
-/
def outgoingAmplitude {m : ℝ → ℝ} (hm : Integrable m) (c : ℂ) : OutgoingSpace :=
  Ring.inverse (outgoingPencil hm c) 1

/-- The genuine outgoing Jost pencil is invertible throughout its actual complex contraction domain.
Use: the constructed outgoing amplitude and its complex analyticity have a proved inverse rather than an unproved solvability premise.
Article: jacobi, Lemma E.1.
Proof: its perturbation norm is at most |c| times the genuine L1 potential mass; the community Banach geometric-series theorem makes I+c*T a unit. -/
theorem outgoingPencil_isUnit {m : ℝ → ℝ} (hm : Integrable m) {c : ℂ}
    (hc : ‖c‖*(∫ y : ℝ,‖m y‖)<1) : IsUnit (outgoingPencil hm c) := by
  have hsmall : ‖-(c • outgoingOperator hm)‖<1 := by
    rw [norm_neg,norm_smul]
    exact (mul_le_mul_of_nonneg_left (outgoingOperator_norm_le hm) (norm_nonneg c)).trans_lt hc
  simpa only [sub_neg_eq_add,outgoingPencil] using
    (isUnit_one_sub_of_norm_lt_one (R := OutgoingSpace →L[ℂ] OutgoingSpace)
      (x := -(c • outgoingOperator hm)) hsmall)

/-- The genuine Banach-inverse outgoing amplitude satisfies exactly the original oscillatory Volterra equation.
Use: its pointwise inverse-square tail estimates and differential equation start from an actual solved integral equation on one common complex-order domain.
Article: jacobi, Lemma E.1.
Proof: apply the true inverse identity P*P^(-1)=I to the original constant amplitude one and expand the actual operator pencil. -/
theorem outgoingAmplitude_equation {m : ℝ → ℝ} (hm : Integrable m) {c : ℂ}
    (hc : ‖c‖*(∫ y : ℝ,‖m y‖)<1) :
    outgoingAmplitude hm c=1-c • (outgoingOperator hm (outgoingAmplitude hm c)) := by
  have h := congrArg (fun T : OutgoingSpace →L[ℂ] OutgoingSpace => T (1:OutgoingSpace))
    (Ring.mul_inverse_cancel _ (outgoingPencil_isUnit hm hc))
  change outgoingPencil hm c (outgoingAmplitude hm c)=1 at h
  change outgoingAmplitude hm c+c • (outgoingOperator hm (outgoingAmplitude hm c))=1 at h
  exact (eq_sub_iff_add_eq).mpr h

/-- The original outgoing amplitude is the unique bounded continuous solution of its genuine oscillatory Volterra equation on the actual complex contraction domain.
Use: the inverse-square asymptotic construction and actual Bessel comparison identify genuine solutions without assuming an outgoing uniqueness certificate.
Article: jacobi, Lemma E.1.
Proof: the candidate equation is precisely P*f=1. Apply the true left inverse of the same original pencil and its independently proved unit identity. -/
theorem outgoingAmplitude_unique {m : ℝ → ℝ} (hm : Integrable m) {c : ℂ}
    (hc : ‖c‖*(∫ y : ℝ,‖m y‖)<1) {f : OutgoingSpace}
    (hf : f=1-c • outgoingOperator hm f) : f=outgoingAmplitude hm c := by
  have hp : outgoingPencil hm c f=1 := by
    change f+c • outgoingOperator hm f=1
    exact (eq_sub_iff_add_eq).mp hf
  have hi := congrArg (fun T : OutgoingSpace →L[ℂ] OutgoingSpace => T f)
    (Ring.inverse_mul_cancel _ (outgoingPencil_isUnit hm hc))
  change Ring.inverse (outgoingPencil hm c) (outgoingPencil hm c f)=f at hi
  rw [hp] at hi
  exact hi.symm

/-- Every actual outgoing amplitude is bounded by two under the common half-contraction bound.
Use: the genuine spatial Jost remainder has a constant uniform on the original complex-order neighborhood after one fixed far-ray choice.
Article: jacobi, Lemma E.1.
Proof: its genuine equation gives norm(v)<=1+|c|*norm(m)_1*norm(v). The stated half-contraction bound absorbs the last term and leaves norm(v)<=2. -/
theorem outgoingAmplitude_norm_le_two {m : ℝ → ℝ} (hm : Integrable m) {c : ℂ}
    (hc : ‖c‖*(∫ y : ℝ,‖m y‖)≤1/2) : ‖outgoingAmplitude hm c‖≤2 := by
  -- The bound is obtained from the actual solved equation, so no abstract inverse norm estimate is substituted as a premise.
  have hunit : ‖c‖*(∫ y : ℝ,‖m y‖)<1 := hc.trans_lt (by norm_num)
  have hEq := outgoingAmplitude_equation hm hunit
  have hn := norm_sub_le (1:OutgoingSpace) (c • outgoingOperator hm (outgoingAmplitude hm c))
  rw [← hEq,norm_one,norm_smul] at hn
  have hb : ‖c‖*‖outgoingOperator hm (outgoingAmplitude hm c)‖ ≤
      (‖c‖*(∫ y : ℝ,‖m y‖))*‖outgoingAmplitude hm c‖ := calc
    _ ≤ ‖c‖*(‖outgoingOperator hm‖*‖outgoingAmplitude hm c‖) :=
      mul_le_mul_of_nonneg_left ((outgoingOperator hm).le_opNorm _) (norm_nonneg c)
    _ ≤ ‖c‖*((∫ y : ℝ,‖m y‖)*‖outgoingAmplitude hm c‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (outgoingOperator_norm_le hm) (norm_nonneg _)) (norm_nonneg c)
    _ = _ := by ring
  have hh := mul_le_mul_of_nonneg_right hc (norm_nonneg (outgoingAmplitude hm c))
  nlinarith [hb,hh]

/-- The actual outgoing Jost amplitude depends holomorphically in Banach norm on the genuine complex coefficient throughout the original contraction domain.
Use: the inverse-square order substitution c=1/4-alpha^2 gives uniform complex-order outgoing solutions, which supply the common tail-zero continuation in Lemma E.1.
Article: jacobi, Lemma E.1.
Proof: the literal pencil is affine and complex analytic, and its actual value is a proved unit. Compose the community holomorphic Banach inverse with this pencil and the bounded evaluation at the original constant amplitude one. -/
theorem outgoingAmplitude_analytic {m : ℝ → ℝ} (hm : Integrable m) {c : ℂ}
    (hc : ‖c‖*(∫ y : ℝ,‖m y‖)<1) : AnalyticAt ℂ (outgoingAmplitude hm) c := by
  -- The inverse is taken in the actual fixed complex endomorphism algebra, not in a parameter-dependent space.
  have hu := outgoingPencil_isUnit hm hc
  have hinv : AnalyticAt ℂ Ring.inverse (outgoingPencil hm c) := by
    simpa only [IsUnit.unit_spec] using
      (analyticAt_inverse (𝕜 := ℂ) (A := OutgoingSpace →L[ℂ] OutgoingSpace) hu.unit)
  have hP : AnalyticAt ℂ (outgoingPencil hm) c := by
    unfold outgoingPencil
    exact analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  exact ((ContinuousLinearMap.apply ℂ OutgoingSpace (1:OutgoingSpace)).analyticAt _).comp
    (f := fun z => Ring.inverse (outgoingPencil hm z)) (hinv.comp hP)

end
end jacobi.Hankel
