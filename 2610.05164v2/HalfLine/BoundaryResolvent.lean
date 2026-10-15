import «2610.05164v2».HalfLine.WeightedVector
import «2610.05164v2».HalfLine.CommonMeasure

/-!
Article: 2610.05164v2, Theorem 3.3.
A literal Green integral equation becomes the actual L2 pencil equation.
Use: `«2610.05164v2».HalfLine.inverseOfUnit_apply_of_eq` feeds
`«2610.05164v2».LocalObstruction.volterraSolution_actual` (volterra Solution actual).
Proof chain: `«2610.05164v2».HalfLine.commonMeasure_ode_probability` — 2610.05164v2, Theorem 3.3; A
common compact probability measure for all scales.
-/
namespace «2610.05164v2».HalfLine
noncomputable section
open Set MeasureTheory Real Filter «2610.05164v2».Continuum «2610.05164v2».GroundState
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/--
A literal Green integral equation becomes the actual L2 pencil equation.

Exact identity `(ContinuousLinearMap.id ℝ FeatureSpace+s • operator hm hn x) (weightedVector hm
hn x hy hC)=vector hm hn x`.

Use: `«2610.05164v2».HalfLine.groundResolvent_vector` uses this identity to establish exact
identity `groundResolvent G x (vector hm hn x)=groundVector G x`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_ode_probability`.

Proof: Separate `t < x` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Intersect the eventual or almost-everywhere hypotheses, then prove the
asserted relation at an arbitrary point in that intersection.
-/
theorem pencil_of_green_equation {m y : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    (x : ℝ) (hy : AEStronglyMeasurable y volume) {C : ℝ} (hC : ∀ t < x, ‖y t‖ ≤ C)
    (s : ℝ) (he : ∀ t < x, y t+s*greenSolution x (fun z => leftDensity m x z*y z) t=exp (t-x)) :
    (ContinuousLinearMap.id ℝ FeatureSpace+s • operator hm hn x)
      (weightedVector hm hn x hy hC)=vector hm hn x := by
  -- Separate `t < x` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  let f := weightedVector hm hn x hy hC
  apply Lp.ext
  filter_upwards [Lp.coeFn_add f (s • operator hm hn x f), Lp.coeFn_smul s (operator hm hn x f),
    weightedVector_coe hm hn x hy hC, operator_weightedVector hm hn x hy hC,
    vector_coe_density hm hn x] with t hadd hsm hf hK hv
  change (f+s • operator hm hn x f) t=vector hm hn x t
  rw [hadd]
  change f t+(s • operator hm hn x f) t=_
  rw [hsm]
  change f t+s*(operator hm hn x f t)=_
  change f t=_ at hf
  change operator hm hn x f t=_ at hK
  rw [hf,hK,hv]
  by_cases ht : t < x
  · calc
      _ = sqrt (leftDensity m x t)*(y t+s*greenSolution x (fun z => leftDensity m x z*y z) t) := by ring
      _ = _ := by rw [he t ht]
  · simp [leftDensity,ht]

/--
Exact identity `inverseOfUnit T h v=f`.

Use: `«2610.05164v2».HalfLine.featureResolvent_quadratic` uses this identity to establish exact
identity `inner ℝ (feature x) (featureResolvent hm hn x s hs (feature x)) =
2/(2+Filters.nonlinear s m x)`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_ode_probability`.

Proof: Use the identities/estimates `«2610.05164v2».HalfLine.inverseOfUnit_left` with the
arguments shown in the proof.
-/
theorem inverseOfUnit_apply_of_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : E →L[ℝ] E) (h : IsUnit T) {f v : E} (he : T f=v) : inverseOfUnit T h v=f := by
  rw [← he]
  exact DFunLike.congr_fun (inverseOfUnit_left T h) f

end
end «2610.05164v2».HalfLine
