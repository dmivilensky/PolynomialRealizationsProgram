import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
Article: 2610.05164v2, Proposition 13.
C1 finite-dimensional parameter integrals.
Use: `«2610.05164v2».Calculus.unit_parameter_integral_c1` feeds
`«2610.05164v2».Primal.familyMoment_c1` (family Moment c1).
Proof chain: `«2610.05164v2».Primal.familyConstraintMap_c1` — 2610.05164v2, Theorem 5.2; Contraction
implies exact feasible density, uniqueness, iteration error and energy bound.
Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral remainder
and implicit-function calculus. The needed form is proved here.
-/
namespace «2610.05164v2».Calculus
noncomputable section
open Set Metric Filter MeasureTheory
open scoped Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {H E : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [FiniteDimensional ℝ H] [NormedAddCommGroup E] [NormedSpace ℝ E]

/--
The actual Fréchet derivative: `HasFDerivAt (fun a => ∫ t in (0:ℝ)..1,F a t) (∫ t in (0:ℝ)..1,G
a t) a`.

Use: `«2610.05164v2».Calculus.unit_parameter_integral_c1` uses this Fréchet derivative formula
to establish smoothness to the stated order: `ContDiff ℝ 1 (fun a => ∫ t in (0:ℝ)..1,F a t)`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem unit_parameter_integral_derivative {F : H → ℝ → E} {G : H → ℝ → H →L[ℝ] E}
    (hF : Continuous F.uncurry) (hG : Continuous G.uncurry)
    (hd : ∀ a : H,∀ t∈Icc (0:ℝ) 1,HasFDerivAt (fun a => F a t) (G a t) a) (a : H) :
    HasFDerivAt (fun a => ∫ t in (0:ℝ)..1,F a t) (∫ t in (0:ℝ)..1,G a t) a := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  obtain ⟨M,hM⟩ := (isCompact_closedBall (x:=a) (r:=1)).prod isCompact_Icc |>.exists_bound_of_continuousOn hG.continuousOn
  -- Establish continuity hFc before using the function at limits or in calculus arguments.
  have hFc (b : H) : Continuous (F b) := hF.comp (continuous_const.prodMk continuous_id)
  -- Establish continuity hGc before using the function at limits or in calculus arguments.
  have hGc (b : H) : Continuous (G b) := hG.comp (continuous_const.prodMk continuous_id)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le'' (μ:=volume)
    (s:=ball a 1) (bound:=fun _ => M) (ball_mem_nhds a (by norm_num))
    (Eventually.of_forall (fun b => (hFc b).aestronglyMeasurable))
    (hFc a |>.intervalIntegrable _ _) (hGc a |>.aestronglyMeasurable)
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    have ht' : t∈Icc (0:ℝ) 1 := by
      have hh : t∈Ioc (0:ℝ) 1 := by simpa only [uIoc_of_le zero_le_one] using ht
      exact ⟨hh.1.le,hh.2⟩
    intro b hb
    exact hM (b,t) ⟨ball_subset_closedBall hb,ht'⟩
  · exact intervalIntegrable_const
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    have ht' : t∈Icc (0:ℝ) 1 := by
      have hh : t∈Ioc (0:ℝ) 1 := by simpa only [uIoc_of_le zero_le_one] using ht
      exact ⟨hh.1.le,hh.2⟩
    exact fun b _ => hd b t ht'

/--
Smoothness to the stated order: `ContDiff ℝ 1 (fun a => ∫ t in (0:ℝ)..1,F a t)`.

Use: `«2610.05164v2».Primal.familyMoment_c1` uses this identity to establish smoothness to the
stated order: `ContDiff ℝ 1 (familyMoment ψ θ κ j)`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Use the proved fundamental theorem of calculus with its explicit integrability and
endpoint hypotheses.
-/
theorem unit_parameter_integral_c1 {F : H → ℝ → E} {G : H → ℝ → H →L[ℝ] E}
    (hF : Continuous F.uncurry) (hG : Continuous G.uncurry)
    (hd : ∀ a : H,∀ t∈Icc (0:ℝ) 1,HasFDerivAt (fun a => F a t) (G a t) a) :
    ContDiff ℝ 1 (fun a => ∫ t in (0:ℝ)..1,F a t) := by
  -- Use the proved fundamental theorem of calculus with its explicit integrability and
  -- endpoint hypotheses.
  refine contDiff_one_iff_hasFDerivAt.mpr ⟨fun a => ∫ t in (0:ℝ)..1,G a t,?_,
    unit_parameter_integral_derivative hF hG hd⟩
  simpa only [Function.comp_def,id_eq] using
    (intervalIntegral.continuous_parametric_primitive_of_continuous (a₀:=(0:ℝ)) hG).comp
      (continuous_id.prodMk (continuous_const : Continuous (fun _ : H => (1:ℝ))))

end
end «2610.05164v2».Calculus
