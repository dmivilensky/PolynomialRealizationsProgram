import «2610.05164v2».HalfLine.JostResolvent
import «2610.05164v2».Continuum.SpectralIdentification

/-!
Article: 2610.05164v2, Proposition 3.
The diagonal of the full truncated resolvent, expressed through the already constructed causal
Riccati filter.
Use: `«2610.05164v2».HalfLine.featureResolvent_quadratic` feeds
`«2610.05164v2».Filters.leftLogDeterminant_increment` (Nuclear linearization of the spatial
determinant).
Proof chain: `«2610.05164v2».Comparison.Profile.signed_determinant_comparison` — 2610.05164v2,
Theorem 3.4; Signed determinant and square-trace comparisons.
-/
namespace «2610.05164v2».HalfLine
noncomputable section
open Set MeasureTheory Real «2610.05164v2».Continuum
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/--
Positive pencils have contractive inverses, including on their kernels.

The stated quantitative bound `‖inverseOfUnit _ h v‖ ≤ ‖v‖`.

Use: `«2610.05164v2».LocalObstruction.fullResolvent_norm` uses this bound to establish the
stated quantitative bound `‖fullResolvent m s u‖≤‖u‖`.

Article: 2610.05164v2, Theorem 6.1 via `«2610.05164v2».LocalObstruction.sine_green_scale_tail`.

Proof: Separate `‖u‖ = 0` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem positive_inverse_norm {T : E →L[ℝ] E} (hp : T.IsPositive)
    {a : ℝ} (ha : 0 ≤ a) (h : IsUnit (ContinuousLinearMap.id ℝ E+a • T)) (v : E) :
    ‖inverseOfUnit _ h v‖ ≤ ‖v‖ := by
  -- Separate `‖u‖ = 0` from its negation; prove the goal under each of these mutually
  -- exclusive hypotheses.
  let u := inverseOfUnit _ h v
  have he : u+a • T u=v := DFunLike.congr_fun (inverseOfUnit_right _ h) v
  have ht := hp.re_inner_nonneg_right u
  change 0 ≤ inner ℝ u (T u) at ht
  have hb : ‖u‖^2 ≤ inner ℝ u v := by
    rw [← he, inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
    nlinarith [mul_nonneg ha ht]
  have hc := real_inner_le_norm u v
  by_cases hz : ‖u‖ = 0
  · change ‖u‖ ≤ ‖v‖
    rw [hz]
    exact norm_nonneg v
  · exact (mul_le_mul_iff_right₀ (lt_of_le_of_ne (norm_nonneg u) (Ne.symm hz))).mp
      (by nlinarith [hb.trans hc])

/--
The full feature pencil for a spatially truncated density.

Use: `«2610.05164v2».HalfLine.featureResolvent_quadratic` uses this definition to establish
exact identity `inner ℝ (feature x) (featureResolvent hm hn x s hs (feature x)) =
2/(2+Filters.nonlinear s m x)`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.
-/
def featureResolvent {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    (x : ℝ) (s : ℝ) (hs : 0 ≤ s) : FeatureSpace →L[ℝ] FeatureSpace :=
  inverseOfUnit (ContinuousLinearMap.id ℝ FeatureSpace+(s/2) • densityOperator (leftDensity m x))
    (positive_pencil_unit (densityOperator_positive (leftDensity_integrable hm x)
      (leftDensity_nonneg hn x)) (div_nonneg hs (by norm_num)))

/--
The diagonal of the full truncated resolvent, expressed through the already constructed causal
Riccati filter. This is the local Jost bridge.

Exact identity `inner ℝ (feature x) (featureResolvent hm hn x s hs (feature x)) =
2/(2+Filters.nonlinear s m x)`.

Use: `«2610.05164v2».Filters.leftLogDeterminant_increment` rewrites with this identity to
establish the stated quantitative bound `|leftLogDeterminant hm hn s y-leftLogDeterminant hm hn
s x- log (1+(y-x)*(s*m x/(2+nonlinear s m x)))| ≤ s/2*‖leftTraceClass m y-leftTraceClass m
x-(y-x) • (m x • traceClassFeature x)‖`.

Article: 2610.05164v2, Theorem 5.1 via `«2610.05164v2».Primal.determinant_cubic`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem featureResolvent_quadratic {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) (x : ℝ) :
    inner ℝ (feature x) (featureResolvent hm hn x s hs (feature x)) =
      2/(2+Filters.nonlinear s m x) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  let A := evaluation hm hn x
  let v := vector hm hn x
  let w := positiveResolvent (hm := hm) (hn := hn) x s hs v
  let h := inner ℝ v w
  let a := s/2
  let d := 1+a*h
  have hr : s*h=Filters.nonlinear s m x := responseQuadratic_eq_nonlinear hm hn hs x
  have hd : 0 < d := by
    have hn' := (Filters.nonlinear_bounds hm hn hs x).1
    dsimp [d,a]
    nlinarith
  have hw : w+s • operator hm hn x w=v :=
    DFunLike.congr_fun (inverseOfUnit_right _
      (positive_pencil_unit (operator_positive hm hn x) hs)) v
  have hK : operator hm hn x w=(1/2:ℝ) • (A (A.adjoint w)-h • v) := by
    rw [operator_rankOne]
    rfl
  have hw' : w+a • A (A.adjoint w)=d • v := by
    rw [hK, smul_smul, smul_sub] at hw
    have hw'' : w+a • A (A.adjoint w)-(a*h) • v=v := by
      convert hw using 1; dsimp only [a]; module
    calc
      _ = (w+a • A (A.adjoint w)-(a*h) • v)+(a*h) • v := by module
      _ = v+(a*h) • v := by rw [hw'']
      _ = d • v := by dsimp [d]; module
  have hA : A.adjoint ∘L A=densityOperator (leftDensity m x) :=
    evaluationOperator_adjoint_comp (leftDensity_integrable hm x) (leftDensity_nonneg hn x)
  let z := feature x-(a/d) • A.adjoint w
  have hz : (ContinuousLinearMap.id ℝ FeatureSpace+a • densityOperator (leftDensity m x)) z=
      feature x := by
    have he := congrArg A.adjoint hw'
    simp only [map_add, map_smul] at he
    have he' : A.adjoint w+a • densityOperator (leftDensity m x) (A.adjoint w)=
        d • densityOperator (leftDensity m x) (feature x) := by
      simpa only [← hA, ContinuousLinearMap.comp_apply, A,v,vector] using he
    change z+a • densityOperator (leftDensity m x) z=feature x
    have hc : (a/d)*d=a := div_mul_cancel₀ a hd.ne'
    calc
      _ = feature x-(a/d) • (A.adjoint w+a • densityOperator (leftDensity m x) (A.adjoint w))+
          a • densityOperator (leftDensity m x) (feature x) := by
        dsimp [z]
        simp only [map_sub,map_smul]
        module
      _ = feature x := by rw [he',smul_smul,hc]; module
  have he : featureResolvent hm hn x s hs (feature x)=z :=
    inverseOfUnit_apply_of_eq _ _ hz
  rw [he]
  dsimp only [z]
  rw [inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq,feature_norm,one_pow,
    ContinuousLinearMap.adjoint_inner_right]
  change 1-(a/d)*h=2/(2+Filters.nonlinear s m x)
  have heq : 2+Filters.nonlinear s m x=2*d := by dsimp [d,a]; linarith [hr]
  rw [heq]
  have hd' : 1+a*h ≠ 0 := hd.ne'
  dsimp [d]
  field_simp [hd']
  ring

end
end «2610.05164v2».HalfLine
