import jacobi.Analytic.OrderEnergyAnalytic
import jacobi.Analytic.YoungBounds
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
Article: jacobi, Theorem 4.2.
The original upper-minus-Young gap is analytic, nonnegative and zero
at U. Its linear Taylor coefficient therefore vanishes, and the genuine
analytic Taylor remainder is of order (alpha-1/2)^2.
Source: Fermat's theorem and Taylor's theorem for analytic functions.
Use: proves the printed quadratic contact of the original upper and Young constants from their actual analyticity and order bounds.
-/
namespace jacobi.Analytic
noncomputable section
open Set Filter Asymptotics jacobi.Parameter jacobi.Comparison jacobi.GelfandLevitan
open scoped Topology
set_option maxHeartbeats 1000000

/-- An analytic function with a zero local minimum has a genuine quadratic remainder at that point.
Use: proves the printed quadratic contact of the original upper and Young constants from their actual analyticity and order bounds.
Article: jacobi, Theorem 4.2.
Source: Fermat's stationary-point theorem and mathlib's analytic power-series remainder theorem.
Proof: the true Taylor constant and linear coefficients vanish by the value and local-minimum hypotheses. The actual second-order power-series remainder bound therefore bounds the original function; translate the increment back to the original coordinate. -/
theorem analytic_zero_min_quadratic {f : ℝ → ℝ} {x : ℝ} (hf : AnalyticAt ℝ f x)
    (h0 : f x=0) (hm : IsLocalMin f x) : f=O[𝓝 x] (fun y => (y-x)^2) := by
  -- Both removed Taylor coefficients are proved zero for this same original function.
  obtain ⟨p,hp⟩ := hf
  have h1 : p 1 (fun _ => 1)=0 := hm.hasDerivAt_eq_zero hp.hasDerivAt
  have hp1 (y:ℝ) : p 1 (fun _ => y)=0 := by
    have hh := (p 1).map_smul_univ (fun _ => y) (fun _ => (1:ℝ))
    simpa only [smul_eq_mul,mul_one,h1,mul_zero] using hh
  have hpartial (y:ℝ) : p.partialSum 2 y=0 := by
    simp only [FormalMultilinearSeries.partialSum,Finset.sum_range_succ,Finset.sum_range_zero,
      hp.coeff_zero,h0,hp1,add_zero]
  have ho := hp.isBigO_sub_partialSum_pow 2
  simp only [hpartial,sub_zero] at ho
  have ht : Tendsto (fun y:ℝ => y-x) (𝓝 x) (𝓝 0) := by
    have hc : ContinuousAt (fun y:ℝ => y-x) x := continuousAt_id.sub continuousAt_const
    simpa only [sub_self] using hc.tendsto
  have he (y:ℝ) : x+(y-x)=y := by ring
  simpa only [Function.comp_def,he,Real.norm_eq_abs,sq_abs] using ho.comp_tendsto ht

/-- The original analytic upper-minus-Young gap, with no optimizer choice in its definition.
Use: one beta-independent function controls both errors in the full-fibre energy squeeze near U.
Article: jacobi, Theorem 4.2.
-/
def upperYoungGap (a : ℝ) : ℝ := originalPersymmetricEnergy a-youngLower a

/-- The actual source contact gap is analytic at U.
Use: Taylor's theorem applies to the genuine original persymmetric energy, rather than to an assumed analytic surrogate.
Article: jacobi, Theorem 4.2.
Proof: subtract the independently proved real-analytic original upper and explicit Young functions. -/
theorem upperYoungGap_analytic_U : AnalyticAt ℝ upperYoungGap (1/2) :=
  (originalPersymmetricEnergy_analyticAt (by norm_num : -1<(1/2:ℝ))).sub
    (youngLower_analytic (by norm_num : -1<(1/2:ℝ)))

/-- The original contact gap vanishes exactly at U.
Use: removes its actual constant Taylor coefficient in the source contact argument.
Article: jacobi, Theorem 4.2.
Proof: use the exact original upper value and the independently proved exact Young value. -/
theorem upperYoungGap_U : upperYoungGap (1/2)=0 := by
  rw [upperYoungGap,originalPersymmetricEnergy_eq (by norm_num : -1<(1/2:ℝ)),
    half_sine_persymmetricConstant,youngLower_U,sub_self]

/-- U is a genuine local minimum of the original analytic contact gap.
Use: Fermat's theorem removes the true linear coefficient and fixes the original upper derivative.
Article: jacobi, Theorem 4.2.
Proof: the complete original finite-fibre squeeze proves nonnegativity throughout alpha>-1, an open neighborhood of U, while the exact gap value is zero. -/
theorem upperYoungGap_localMin_U : IsLocalMin upperYoungGap (1/2) := by
  change ∀ᶠ a in 𝓝 (1/2:ℝ),upperYoungGap (1/2)≤upperYoungGap a
  filter_upwards [Ioi_mem_nhds (by norm_num : -1<(1/2:ℝ))] with a ha
  rw [upperYoungGap_U,upperYoungGap,originalPersymmetricEnergy_eq ha]
  exact upper_young_gap_nonneg ha

/-- The original upper and Young constants have the printed quadratic contact, unconditionally.
Use: bounds both actual optimal-energy errors uniformly in the second Jacobi parameter and proves Theorem 4.2's derivative statements.
Article: jacobi, Theorem 4.2.
Proof: apply the proved analytic zero-minimum Taylor theorem to the actual analytic contact gap and its original exact minimum. -/
theorem upperYoungGap_quadratic : upperYoungGap=O[𝓝 (1/2:ℝ)] (fun a => (a-1/2)^2) :=
  analytic_zero_min_quadratic upperYoungGap_analytic_U upperYoungGap_U upperYoungGap_localMin_U

/-- The actual original upper energy has the exact printed derivative -13/75 at U.
Use: the genuine finite-fibre optimum inherits this same derivative by the original beta-independent squeeze.
Article: jacobi, Theorem 4.2.
Proof: Fermat's theorem makes the actual gap derivative zero. Subtract the known genuine Young derivative from the actual analytic upper derivative; their difference is exactly that same stationary gap derivative. -/
theorem originalPersymmetricEnergy_hasDerivAt_U :
    HasDerivAt originalPersymmetricEnergy (-13/75) (1/2) := by
  -- The stationary function is the proved original gap, not an independently prescribed expansion.
  have hu := (originalPersymmetricEnergy_analyticAt (by norm_num : -1<(1/2:ℝ))).differentiableAt.hasDerivAt
  have hd := upperYoungGap_localMin_U.hasDerivAt_eq_zero (hu.sub youngLower_hasDerivAt_U)
  have he : deriv originalPersymmetricEnergy (1/2)= -13/75 := by linarith
  rw [he] at hu
  exact hu

end
end jacobi.Analytic
