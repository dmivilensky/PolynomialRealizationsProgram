import «2610.05164v2».HalfLine.SpectralGap
import «2610.05164v2».HalfLine.Vector

/-!
Article: 2610.05164v2, Theorem 3.3.
Resolvent quadratic forms in the complete compact eigenbasis.
Use: `«2610.05164v2».HalfLine.resolvent_quadratic_hasSum` feeds
`«2610.05164v2».HalfLine.responseQuadratic_hasSum` (response Quadratic has Sum).
Proof chain: `«2610.05164v2».HalfLine.commonMeasure_filter` — 2610.05164v2, Theorem 3.3; A common
compact probability measure for all scales.
-/
namespace «2610.05164v2».HalfLine
noncomputable section
open Set MeasureTheory Real «2610.05164v2».Continuum «2610.05164v2».GroundState
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/--
The precise assertion is `IsUnit (ContinuousLinearMap.id ℝ E+s • T)`.

Use: `«2610.05164v2».Continuum.rankOne_logDeterminant` uses this assertion to establish exact
identity `logDeterminant D'.eigenvalue s = logDeterminant D.eigenvalue s+ log (1+s/2*u*inner ℝ
v (inverseOfUnit _ (positive_pencil_unit hp (show 0 ≤ s/2 by positivity)) v))`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_filter`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem positive_pencil_unit {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {T : E →L[ℝ] E} (hp : T.IsPositive) {s : ℝ} (hs : 0 ≤ s) :
    IsUnit (ContinuousLinearMap.id ℝ E+s • T) := by
  -- Expand/rewrite the named definitions and identities appearing in the tactic block; the
  -- remaining goal is a direct simplification or algebraic consequence.
  apply ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map _ (c := 1) (by norm_num)
  intro u
  change ‖u‖^2*1 ≤ ‖inner ℝ (u+s • T u) u‖
  rw [inner_add_left,real_inner_smul_left,real_inner_self_eq_norm_sq]
  have hT := hp.re_inner_nonneg_left u
  change 0 ≤ inner ℝ (T u) u at hT
  rw [Real.norm_eq_abs,abs_of_nonneg (add_nonneg (sq_nonneg _) (mul_nonneg hs hT))]
  nlinarith [mul_nonneg hs hT]

/--
The precise assertion is `IsUnit (ContinuousLinearMap.id ℝ FeatureSpace-groundParameter hm hn •
operator hm hn x)`.

Use: `«2610.05164v2».HalfLine.ground_pencil_add_unit` uses this assertion to establish the
precise assertion is `IsUnit (ContinuousLinearMap.id ℝ FeatureSpace+ (-groundParameter hm hn) •
operator hm hn x)`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_ode_probability`.

Proof: Use the identities/estimates `«2610.05164v2».HalfLine.operator_norm_strict`,
`«2610.05164v2».GroundState.GroundWitness.coupling_positive` with the arguments shown in the
proof.
-/
theorem ground_pencil_unit {m : ℝ → ℝ} {hm : Integrable m} {hn : ∀ t, 0 ≤ m t}
    (G : GroundWitness hm hn) (x : ℝ) :
    IsUnit (ContinuousLinearMap.id ℝ FeatureSpace-groundParameter hm hn • operator hm hn x) := by
  -- Use the identities/estimates `«2610.05164v2».HalfLine.operator_norm_strict`,
  -- `«2610.05164v2».GroundState.GroundWitness.coupling_positive` with the arguments shown in
  -- the proof.
  let T := operator hm hn x
  let c := 1-groundParameter hm hn*‖T‖
  have hc : 0 < c := by
    have h := operator_norm_strict G x
    have h' := (lt_div_iff₀ G.coupling_positive).mp h
    dsimp [c,T]
    nlinarith
  apply ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map _
    (c := ⟨c,hc.le⟩) (by exact_mod_cast hc)
  intro u
  change ‖u‖^2*c ≤ ‖inner ℝ (u-groundParameter hm hn • T u) u‖
  rw [inner_sub_left,real_inner_smul_left,real_inner_self_eq_norm_sq]
  have h : inner ℝ (T u) u ≤ ‖T‖*‖u‖^2 := by
    calc
      _ ≤ ‖T u‖*‖u‖ := real_inner_le_norm _ _
      _ ≤ (‖T‖*‖u‖)*‖u‖ := mul_le_mul_of_nonneg_right (T.le_opNorm u) (norm_nonneg _)
      _ = _ := by ring
  have hle : ‖u‖^2*c ≤ ‖u‖^2-groundParameter hm hn*inner ℝ (T u) u := by
    dsimp [c]
    nlinarith [mul_le_mul_of_nonneg_left h G.coupling_positive.le]
  exact hle.trans (le_abs_self _)

/--
Defines `inverseOfUnit` of type `E →L[ℝ] E` by `↑h.unit⁻¹`.

Use: `«2610.05164v2».HalfLine.resolvent_quadratic_hasSum` uses this definition to establish the
value of a convergent infinite sum: `HasSum (fun i => (inner ℝ (D.basis i) v)^2/(1+s*D.eig i))
(inner ℝ v (inverseOfUnit _ hunit v))`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_ode_probability`.
-/
def inverseOfUnit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : E →L[ℝ] E) (h : IsUnit T) : E →L[ℝ] E := ↑h.unit⁻¹

/--
Exact identity `T ∘L inverseOfUnit T h=ContinuousLinearMap.id ℝ E`.

Use: `«2610.05164v2».HalfLine.resolvent_quadratic_hasSum` uses this identity to establish the
value of a convergent infinite sum: `HasSum (fun i => (inner ℝ (D.basis i) v)^2/(1+s*D.eig i))
(inner ℝ v (inverseOfUnit _ hunit v))`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_filter`.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
theorem inverseOfUnit_right {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : E →L[ℝ] E) (h : IsUnit T) : T ∘L inverseOfUnit T h=ContinuousLinearMap.id ℝ E := by
  change T * (↑h.unit⁻¹ : E →L[ℝ] E)=1
  calc
    _ = (↑h.unit : E →L[ℝ] E) * ↑h.unit⁻¹ := by congr 1
    _ = _ := Units.mul_inv h.unit

/--
Exact identity `inverseOfUnit T h ∘L T=ContinuousLinearMap.id ℝ E`.

Use: `«2610.05164v2».HalfLine.inverseOfUnit_apply_of_eq` uses this identity to establish exact
identity `inverseOfUnit T h v=f`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_ode_probability`.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
theorem inverseOfUnit_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : E →L[ℝ] E) (h : IsUnit T) : inverseOfUnit T h ∘L T=ContinuousLinearMap.id ℝ E := by
  change (↑h.unit⁻¹ : E →L[ℝ] E) * T=1
  calc
    _ = (↑h.unit⁻¹ : E →L[ℝ] E) * ↑h.unit := by congr 1
    _ = _ := Units.inv_mul h.unit

/--
Resolvent quadratic forms in the complete compact eigenbasis. The series contains the kernel
components, which contribute at eigenvalue zero.

The value of a convergent infinite sum: `HasSum (fun i => (inner ℝ (D.basis i) v)^2/(1+s*D.eig
i)) (inner ℝ v (inverseOfUnit _ hunit v))`.

Use: `«2610.05164v2».Continuum.resolvent_remainder_tendsto` uses this infinite-sum formula to
establish convergence along the specified source filter to the specified limit: `Tendsto (fun F
: Finset D.Index => ‖v‖^2- ∑ i ∈ F, a*D.eig i/(1+a*D.eig i)*(inner ℝ (D.basis i) v)^2) atTop (𝓝
(inner ℝ v (inverseOfUnit _ (positive_pencil_unit hp ha) v)))`.

Article: 2610.05164v2, Theorem 3.3 via `«2610.05164v2».HalfLine.commonMeasure_filter`.

Proof: Use the identities/estimates `«2610.05164v2».HalfLine.inverseOfUnit_right` with the
arguments shown in the proof.
-/
theorem resolvent_quadratic_hasSum {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {T : E →L[ℝ] E} (D : PositiveSpectralData T) (hp : T.IsPositive)
    (s : ℝ) (hunit : IsUnit (ContinuousLinearMap.id ℝ E+s • T))
    (hden : ∀ i, 1+s*D.eig i ≠ 0) (v : E) :
    HasSum (fun i => (inner ℝ (D.basis i) v)^2/(1+s*D.eig i))
      (inner ℝ v (inverseOfUnit _ hunit v)) := by
  -- Use the identities/estimates `«2610.05164v2».HalfLine.inverseOfUnit_right` with the
  -- arguments shown in the proof.
  let R := inverseOfUnit _ hunit
  have he : (ContinuousLinearMap.id ℝ E+s • T) (R v)=v :=
    DFunLike.congr_fun (inverseOfUnit_right _ hunit) v
  have hcoef (i : D.Index) : inner ℝ (D.basis i) (R v)=inner ℝ (D.basis i) v/(1+s*D.eig i) := by
    have h := congrArg (fun u => inner ℝ (D.basis i) u) he
    change inner ℝ (D.basis i) (R v+s • T (R v))=inner ℝ (D.basis i) v at h
    rw [inner_add_right,real_inner_smul_right] at h
    have hs := hp.isSymmetric (D.basis i) (R v)
    change inner ℝ (T (D.basis i)) (R v)=inner ℝ (D.basis i) (T (R v)) at hs
    rw [D.equation,real_inner_smul_left] at hs
    apply (eq_div_iff (hden i)).mpr
    linear_combination h+s*hs
  have h := (innerSL ℝ (R v)).hasSum (D.basis.hasSum_repr v)
  change HasSum (fun i => inner ℝ (R v) ((D.basis.repr v i) • D.basis i)) (inner ℝ (R v) v) at h
  have hi (i : D.Index) : inner ℝ (R v) ((D.basis.repr v i) • D.basis i)=
      (inner ℝ (D.basis i) v)^2/(1+s*D.eig i) := by
    rw [real_inner_smul_right,HilbertBasis.repr_apply_apply,
      real_inner_comm (D.basis i) (R v),hcoef]
    ring
  change HasSum _ (inner ℝ v (R v))
  simpa only [hi,real_inner_comm v (R v)] using h

end
end «2610.05164v2».HalfLine
