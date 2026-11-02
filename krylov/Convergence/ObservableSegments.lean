import krylov.Convergence.ObservableFCSource
import krylov.Nonlinear.RFCSAveraged
import krylov.XR.LocalCurvatureIntegral

/-!
Article: main_krylov, apG:Dunif, genuine accepted and proposed segments.
Use: derive actual averaged-Hessian secants and the precise one-half
function Taylor upper bound on every enclosed line/correction segment.
Source: the original scalar derivatives, Schwarz symmetry, gradient FTC
and the already proved true weighted-Hessian Taylor identity.
-/
namespace krylov.Convergence
noncomputable section
open Set Metric krylov.Functions krylov.Nonlinear krylov.XR chebyshev1.Nonlinear
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Genuine canonical source segments have their true secant operator,
symmetry and a length-independent reference error bound.
Article: main_krylov, apG:Dunif. -/
theorem ObservableLocalSource.segment_data {T : E ≃L[ℝ] E} {f : E → ℝ} {G : E → E}
    {H : E → E →L[ℝ] E} {r : ℝ} {L : ℝ≥0} (S : ObservableLocalSource T f G H r L)
    (a b : E) (R : ℝ) (ha : ‖a‖≤R) (hb : ‖b‖≤R) (hR : R<r) :
    let A := averagedDerivative (coordinateDerivative T H) a (b-a)
    coordinateGradient T G b-coordinateGradient T G a=A (b-a) ∧
      A.toLinearMap.IsSymmetric ∧ ‖A-ContinuousLinearMap.id ℝ E‖≤(L:ℝ)*R := by
  have hseg t (ht : t∈Icc (0:ℝ) 1) : ‖a+t • (b-a)‖≤R :=
    segment_norm_le_endpoints a b R ha hb t ht
  have hball t (ht : t∈Icc (0:ℝ) 1) : a+t • (b-a)∈closedBall (0:E) r := by
    rw [mem_closedBall,dist_zero_right]
    exact (hseg t ht).trans hR.le
  have hc := S.lipschitz.continuousOn.comp
    (continuous_const.add (continuous_id.smul continuous_const)).continuousOn hball
  have hftc := averagedDerivative_apply (coordinateGradient T G) (coordinateDerivative T H) a (b-a) hc
    (fun t ht=>S.coordinate_g _ ((hseg t ht).trans hR.le))
  rw [add_sub_cancel] at hftc
  refine ⟨hftc.symm,?_,?_⟩
  · apply averagedDerivative_symmetric _ _ _ hc
    intro t ht
    exact genuine_hessian_symmetric (ContinuousLinearEquiv.refl ℝ E) (coordinateObjective T f)
      (coordinateGradient T G) (coordinateDerivative T H)
      (fun z hz=>S.coordinate_f z hz) (fun z hz=>S.coordinate_g z hz) _ ((hseg t ht).trans_lt hR)
  · apply averagedDerivative_sub_const_norm_le _ _ _ _ hc
    intro t ht
    have hh := S.lipschitz.norm_sub_le (hball t ht) (mem_closedBall_self S.radius_pos.le)
    rw [S.hessian_zero,sub_zero] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (hseg t ht) L.coe_nonneg)

omit [CompleteSpace E] in
/-- The true scalar objective on an actually enclosed source segment has
the precise one-half quadratic upper estimate. In particular the RFC
value acceptance is proved from source data rather than assumed.
Article: main_krylov, apG:Dunif. -/
theorem ObservableLocalSource.segment_value_upper {T : E ≃L[ℝ] E} {f : E → ℝ} {G : E → E}
    {H : E → E →L[ℝ] E} {r : ℝ} {L : ℝ≥0} (S : ObservableLocalSource T f G H r L)
    (a b : E) (R : ℝ) (ha : ‖a‖≤R) (hb : ‖b‖≤R) (hR : R<r) :
    coordinateObjective T f b≤coordinateObjective T f a+
      inner ℝ (coordinateGradient T G a) (b-a)+((1+(L:ℝ)*R)/2)*‖b-a‖^2 := by
  have hseg t (ht : t∈Icc (0:ℝ) 1) : ‖a+t • (b-a)‖≤R :=
    segment_norm_le_endpoints a b R ha hb t ht
  have hball t (ht : t∈Icc (0:ℝ) 1) : a+t • (b-a)∈closedBall (0:E) r := by
    rw [mem_closedBall,dist_zero_right]
    exact (hseg t ht).trans hR.le
  have hc := S.lipschitz.continuousOn.comp
    (continuous_const.add (continuous_id.smul continuous_const)).continuousOn hball
  have htaylor := weightedCurvature_eq_values (coordinateObjective T f) (coordinateGradient T G)
    (coordinateDerivative T H) a (b-a)
    (fun t ht=>S.coordinate_f _ ((hseg t ht).trans hR.le))
    (fun t ht=>S.coordinate_g _ ((hseg t ht).trans hR.le)) hc
  have hR0 : 0≤R := (norm_nonneg a).trans ha
  have herror := weightedCurvature_error (coordinateDerivative T H) (ContinuousLinearMap.id ℝ E)
    a (b-a) ((L:ℝ)*R) (by positivity) hc (by
      intro t ht
      have hh := S.lipschitz.norm_sub_le (hball t ht) (mem_closedBall_self S.radius_pos.le)
      rw [S.hessian_zero,sub_zero] at hh
      exact hh.trans (mul_le_mul_of_nonneg_left (hseg t ht) L.coe_nonneg))
  rw [ContinuousLinearMap.id_apply,real_inner_self_eq_norm_sq,htaylor,add_sub_cancel] at herror
  linarith only [(abs_le.mp herror).2]

end
end krylov.Convergence
