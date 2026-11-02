import krylov.Design.HyperbolicIntegral
import jacobi.Young.IntrinsicCoordinate
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
Article: main_krylov, apC:lem:poisson, improper beta-coordinate substitution.
Use: transport a genuine integrable unit-interval integrand through the actual
coordinate t=(1+tanh x)/2 by differentiating its integral primitive and checking
both infinite endpoints. This avoids an assumed improper substitution rule.
Source: mathlib's fundamental theorem of calculus, and the actual intrinsic
coordinate and endpoint limits from the jacobi formalization.
-/

namespace krylov.Design
noncomputable section
open MeasureTheory Real Set Filter jacobi.Young
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The actual intrinsic logistic coordinate gives the rigorous improper unit-interval substitution.
Article: main_krylov, apC:lem:poisson, the beta-integral route to hyperbolic transforms.
Proof: differentiate the genuine interval-integral primitive along the actual
coordinate, then apply the whole-line fundamental theorem with its proved endpoint limits. -/
theorem integral_intrinsic_substitution (g : ℝ → E) (hi : IntervalIntegrable g volume 0 1)
    (hc : ContinuousOn g (Ioo 0 1))
    (hpull : Integrable (fun x : ℝ => ((1 / 2 : ℝ) * sech x ^ 2) • g (intrinsic x))) :
    (∫ x : ℝ, ((1 / 2 : ℝ) * sech x ^ 2) • g (intrinsic x)) = ∫ t in (0 : ℝ)..1, g t := by
  let F : ℝ → E := fun t => ∫ u in (0 : ℝ)..t, g u
  have hFcont : ContinuousOn F (Icc (0 : ℝ) 1) := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
      intervalIntegral.continuousOn_primitive_interval' hi (left_mem_uIcc : (0 : ℝ) ∈ uIcc 0 1)
  have hd (x : ℝ) : HasDerivAt (fun y => F (intrinsic y))
      (((1 / 2 : ℝ) * sech x ^ 2) • g (intrinsic x)) x := by
    have hu := intrinsic_mem x
    have hiu : IntervalIntegrable g volume 0 (intrinsic x) := by
      apply hi.mono_set
      rw [uIcc_of_le hu.1.le, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      intro t ht
      exact ⟨ht.1, ht.2.trans hu.2.le⟩
    have hg : HasDerivAt F (g (intrinsic x)) (intrinsic x) :=
      intervalIntegral.integral_hasDerivAt_right hiu
        (hc.stronglyMeasurableAtFilter isOpen_Ioo _ hu)
        (hc.continuousAt (Ioo_mem_nhds hu.1 hu.2))
    simpa only [Function.comp_def] using! hg.scomp x (intrinsic_derivative x)
  have huBot : Tendsto intrinsic atBot (𝓝[Icc (0 : ℝ) 1] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨intrinsic_atBot,
      Eventually.of_forall (fun x => ⟨(intrinsic_mem x).1.le, (intrinsic_mem x).2.le⟩)⟩
  have huTop : Tendsto intrinsic atTop (𝓝[Icc (0 : ℝ) 1] 1) :=
    tendsto_nhdsWithin_iff.mpr ⟨intrinsic_atTop,
      Eventually.of_forall (fun x => ⟨(intrinsic_mem x).1.le, (intrinsic_mem x).2.le⟩)⟩
  have hbot := (hFcont 0 (by constructor <;> norm_num)).tendsto.comp huBot
  have htop := (hFcont 1 (by constructor <;> norm_num)).tendsto.comp huTop
  have h := integral_of_hasDerivAt_of_tendsto hd hpull hbot htop
  simpa only [F, intervalIntegral.integral_same, sub_zero] using h

/-- The genuine complex beta integrand is continuous throughout the open integration interval.
Article: main_krylov, apC:lem:poisson, the beta route to Fourier transforms.
Proof: both real bases are strictly positive, so their complex powers avoid the branch cut. -/
theorem betaIntegrand_continuousOn (z w : ℂ) :
    ContinuousOn (fun t : ℝ => (t : ℂ) ^ (z - 1) * (1 - (t : ℂ)) ^ (w - 1)) (Ioo 0 1) := by
  intro t ht
  apply ContinuousAt.continuousWithinAt
  have htz : (t : ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    exact ht.1
  have how : (1 - (t : ℂ)) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    change 0 < 1 - t
    linarith [ht.2]
  have hsub : ContinuousAt (fun r : ℝ => (1 : ℂ) - (r : ℂ)) t :=
    continuousAt_const.sub Complex.continuous_ofReal.continuousAt
  have ha : ContinuousAt (fun r : ℝ => (r : ℂ) ^ (z - 1)) t :=
    (continuousAt_cpow_const (b := z - 1) htz).comp (f := Complex.ofReal) Complex.continuous_ofReal.continuousAt
  have hb : ContinuousAt (fun r : ℝ => (1 - (r : ℂ)) ^ (w - 1)) t :=
    (continuousAt_cpow_const (b := w - 1) how).comp (f := fun r : ℝ => 1 - (r : ℂ)) hsub
  exact ha.mul hb

end
end krylov.Design
