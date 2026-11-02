import jacobi.GelfandLevitan.FiniteGreenIdentity
import jacobi.GelfandLevitan.TransformedGreenStrip
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
Article: jacobi, Proposition C.2.
The actual original finite primitive solutions converge on the full
physical half interval in the true uniform function norm. Their actual
products consequently converge under the original physical integrals
from zero, supplying the integral side of the full Green limit.
Use: the full original finite solution and Green product limits keep this same constructed u, including its genuine selected singular endpoint.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual original infinite transformed solution in the genuine full-half uniform norm.
Use: the full original finite solution and Green product limits keep this same constructed u, including its genuine selected singular endpoint.
Article: jacobi, Proposition C.2.
-/
def transformedHalfMap (a : ℝ) (ha : -1<a) (z : ℂ) : C(HalfInterval,ℂ) :=
  ⟨fun t => transformedSolution a ha t z,transformedSolution_continuous a ha z⟩

/-- The original finite primitive solution in the full-half uniform norm beyond its proved continuity threshold.
Use: finiteTransformedHalfMap_values removes every totalization fallback and finiteTransformedHalfMap_tendsto gives the actual full-half original norm limit for the Green integral passage.
Article: jacobi, Proposition C.2.
Source: mathlib ContinuousMap.mkD, with eventual original source equality proved below. -/
def finiteTransformedHalfMap (a : ℝ) (ha : -1<a) (N : ℕ) (z : ℂ) : C(HalfInterval,ℂ) :=
  ContinuousMap.mkD (fun t => finiteTransformedFunction a ha N z t) 0

/-- The actual sufficiently long finite full-half continuous approximations retain every original finite transformed solution value.
Use: the genuine full-half norm limit and the original zero-endpoint Green integrals contain exactly the actual original finite primitive solutions.
Article: jacobi, Proposition C.2.
Proof: the actual original finite feature systems are eventually genuine units at every parameter, so the original finite solution is continuous up to zero. The community continuous-domain restriction and mkD value theorem remove the fallback everywhere. -/
theorem finiteTransformedHalfMap_values (a : ℝ) (ha : -1<a) :
    ∀ᶠ N : ℕ in atTop,∀ (z : ℂ) (t : HalfInterval),
      finiteTransformedHalfMap a ha N z t=finiteTransformedFunction a ha N z t := by
  filter_upwards [finiteFeatureSystem_isUnit a ha] with N hN z t
  have hc := continuousOn_iff_continuous_domRestrict.mp (finiteTransformedFunction_continuousOn a ha N hN z)
  exact ContinuousMap.mkD_apply_of_continuous hc

/-- The genuine original finite full-half transformed solutions converge in uniform norm to the actual original infinite GL solution.
Use: products preserve this same norm limit, and the original zero-endpoint Green product integrals therefore converge without a separate domination hypothesis.
Article: jacobi, Proposition C.2.
Proof: the original actual inverse-row solutions have their independently proved full-half uniform limit. The genuine finite primitive solution identification and the eventual true continuous-map values retain precisely that sequence. The community compact-domain equivalence identifies the genuine uniform norm topology. -/
theorem finiteTransformedHalfMap_tendsto (a : ℝ) (ha : -1<a) (z : ℂ) :
    Tendsto (fun N => finiteTransformedHalfMap a ha N z) atTop (𝓝 (transformedHalfMap a ha z)) := by
  -- The original finite GL uniform limit, including zero, is retained under the actual primitive-solution identification.
  apply ContinuousMap.tendsto_iff_tendstoUniformly.mpr
  have he : (fun N t => finiteTransformedSolution a ha N t z)=ᶠ[atTop]
      (fun N t => finiteTransformedHalfMap a ha N z t) := by
    filter_upwards [finiteTransformedHalfMap_values a ha,finiteTransformedFunction_eq a ha] with N hN hEq
    funext t
    exact ((hN z t).trans (hEq t z)).symm
  exact (tendstoUniformly_congr he).mp (finiteTransformedSolution_uniform_limit a ha z)

/-- The genuine original finite transformed Green product integrals converge from the singular endpoint zero to every physical half-interval point.
Use: transformed_green_identity passes the actual original finite Green identity to its true infinite GL solution, with no unproved zero-endpoint integral convergence premise.
Article: jacobi, Proposition C.2.
Proof: products of the independently proved actual full-half norm limits converge in the same original uniform norm. Pull back to the unchanged real physical coordinate; the genuine finite values agree with the original primitive solution on the entire actual integration interval. Eventual genuine continuity and the community uniform-convergence integral theorem give the original integral limit. -/
theorem finiteTransformedFunction_integral_tendsto (a : ℝ) (ha : -1<a) (z w : ℂ) (t : HalfInterval) :
    Tendsto (fun N => ∫ r in (0:ℝ)..(t:ℝ),finiteTransformedFunction a ha N z r*finiteTransformedFunction a ha N w r)
      atTop (𝓝 (∫ r in (0:ℝ)..(t:ℝ),transformedSolution a ha (halfParameterClamp r) z*
        transformedSolution a ha (halfParameterClamp r) w)) := by
  -- The actual physical product integrands are identified throughout the interval before passing their original integral to the limit.
  have hp := (finiteTransformedHalfMap_tendsto a ha z).mul (finiteTransformedHalfMap_tendsto a ha w)
  have hU := ((ContinuousMap.tendsto_iff_tendstoUniformly.mp hp).comp halfParameterClamp).tendstoUniformlyOn
    (s := uIcc (0:ℝ) (t:ℝ))
  have he : ∀ᶠ N : ℕ in atTop,EqOn
      (fun r => (finiteTransformedHalfMap a ha N z*finiteTransformedHalfMap a ha N w) (halfParameterClamp r))
      (fun r => finiteTransformedFunction a ha N z r*finiteTransformedFunction a ha N w r) (uIcc (0:ℝ) (t:ℝ)) := by
    filter_upwards [finiteTransformedHalfMap_values a ha] with N hN r hr
    have hr' : r∈Icc (0:ℝ) (1/2) := by
      rw [uIcc_of_le t.property.1] at hr
      exact ⟨hr.1,hr.2.trans t.property.2⟩
    dsimp only
    rw [ContinuousMap.mul_apply,hN,hN,show halfParameterClamp r=(⟨r,hr'⟩:HalfInterval) from Set.projIcc_of_mem (by norm_num) hr']
  have hc : ∀ᶠ N : ℕ in atTop,ContinuousOn
      (fun r => finiteTransformedFunction a ha N z r*finiteTransformedFunction a ha N w r) (uIcc (0:ℝ) (t:ℝ)) := by
    filter_upwards [finiteFeatureSystem_isUnit a ha] with N hN
    rw [uIcc_of_le t.property.1]
    exact ((finiteTransformedFunction_continuousOn a ha N hN z).mul
      (finiteTransformedFunction_continuousOn a ha N hN w)).mono (Icc_subset_Icc le_rfl t.property.2)
  exact (hU.congr he).tendsto_intervalIntegral_of_continuousOn hc

end
end jacobi.GelfandLevitan
