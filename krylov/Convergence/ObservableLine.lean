import krylov.Convergence.ObservableSegments

/-!
Article: main_krylov, apG:Dunif, genuine RFC pre-correction search.
Use: localize and identify the true search at an arbitrary admitted
observable history, before its correction-energy and value decisions.
Source: actual metric chord existence, scalar sublevels, stationarity
and the proved true averaged-Hessian quotient dictionary.
-/
namespace krylov.Convergence
noncomputable section
open Set Metric krylov.Methods krylov.Functions krylov.Nonlinear krylov.Reference chebyshev1.Nonlinear
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every admitted real observable state has a genuine actual metric
chord minimum for its computed direction, irrespective of later tests.
Article: main_krylov, apG:Dunif. -/
theorem ObservableLocalSource.line_chord {T : E ≃L[ℝ] E} {f : E → ℝ} {G : E → E}
    {H : E → E →L[ℝ] E} {r : ℝ} {L : ℝ≥0} (S : ObservableLocalSource T f G H r L)
    (x₀ : E) (B : History E) (hx : ‖T (x₀+B.displacement)‖≤r) :
    IsChordMinimum (coordinateObjective T f) (T (x₀+B.displacement))
      (T (rfcFunctionDirection fullMemory B)) r
      (T (rfcFunctionLinePoint T f fullMemory r x₀ B)) := by
  have hf z (hz : z∈closedBall (0:E) r) := S.coordinate_f z
    (by simpa only [mem_closedBall,dist_zero_right] using hz)
  have hg z (hz : z∈closedBall (0:E) r) := S.coordinate_g z
    (by simpa only [mem_closedBall,dist_zero_right] using hz)
  change IsChordMinimum _ _ _ r (T (T.symm (localExactPoint _ _ _ r)))
  rw [T.apply_symm_apply]
  exact localExactPoint_spec _ _ _ r (existsUnique_local_chord_minimum _ _ _ S.radius_pos
    S.hessian_zero S.small S.lipschitz hf hg _ _
      (by simpa only [mem_closedBall,dist_zero_right] using hx))

variable [CompleteSpace E]

/-- A true observable current sublevel supplies a uniformly localized
actual line endpoint and its genuine stationarity equation.
Article: main_krylov, apG:Dunif. -/
theorem ObservableLocalSource.line_localization {T : E ≃L[ℝ] E} {f : E → ℝ} {G : E → E}
    {H : E → E →L[ℝ] E} {r : ℝ} {L : ℝ≥0} (S : ObservableLocalSource T f G H r L)
    (x₀ : E) (B : History E) (he : ‖T x₀‖<r/4)
    (hx : ‖T (x₀+B.displacement)‖≤2*‖T x₀‖) (hv : f (x₀+B.displacement)≤f x₀) :
    let y := rfcFunctionLinePoint T f fullMemory r x₀ B
    ‖T y‖≤2*‖T x₀‖ ∧ f y≤f (x₀+B.displacement) ∧
      inner ℝ (coordinateGradient T G (T y)) (T (rfcFunctionDirection fullMemory B))=0 := by
  have hr := S.radius_pos
  have hxin : ‖T (x₀+B.displacement)‖<r/2 := hx.trans_lt (by linarith)
  have hm := S.line_chord x₀ B (by linarith [norm_nonneg (T (x₀+B.displacement))])
  have hf z (hz : z∈closedBall (0:E) r) := S.coordinate_f z
    (by simpa only [mem_closedBall,dist_zero_right] using hz)
  have hg z (hz : z∈closedBall (0:E) r) := S.coordinate_g z
    (by simpa only [mem_closedBall,dist_zero_right] using hz)
  have hgzero : coordinateGradient T G 0=0 := by simp only [coordinateGradient,map_zero,S.gradient_zero]
  have hval : f (rfcFunctionLinePoint T f fullMemory r x₀ B)≤f (x₀+B.displacement) := by
    have hh := hm.2.2 0 (by
      change T (x₀+B.displacement)+(0:ℝ) • T (rfcFunctionDirection fullMemory B)∈closedBall (0:E) r
      simpa only [zero_smul,add_zero,mem_closedBall,dist_zero_right] using hxin.le.trans (by linarith))
    simpa only [coordinateObjective_apply,zero_smul,add_zero] using hh
  have hsub := local_sublevel_search_bounds (coordinateObjective T f) (coordinateGradient T G)
    (coordinateDerivative T H) S.radius_pos hgzero S.hessian_zero S.small S.lipschitz hf hg
    (T x₀) (T (rfcFunctionLinePoint T f fullMemory r x₀ B)) (by linarith) hm.1
    (by simpa only [coordinateObjective_apply] using hval.trans hv)
  have hspec := local_chord_minimum_spec (coordinateObjective T f) (coordinateGradient T G)
    (coordinateDerivative T H) S.radius_pos hgzero S.hessian_zero S.small S.lipschitz hf hg
    (T (x₀+B.displacement)) (T (rfcFunctionDirection fullMemory B))
    (T (rfcFunctionLinePoint T f fullMemory r x₀ B)) hxin hm
  have hsqrt : Real.sqrt (3:ℝ)≤2 := Real.sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
  exact ⟨hsub.1.trans (mul_le_mul_of_nonneg_right hsqrt (norm_nonneg _)),hval,hspec.2.2.1⟩

/-- Every true admitted descending observable direction executes the
real canonical averaged-Hessian quotient with a strictly positive search
scalar, and a nonzero actual searched step.
Article: main_krylov, apG:Dunif, native pre-correction dictionary. -/
theorem ObservableLocalSource.line_model_data {T : E ≃L[ℝ] E} {f : E → ℝ} {G : E → E}
    {H : E → E →L[ℝ] E} {r : ℝ} {L : ℝ≥0} (S : ObservableLocalSource T f G H r L)
    (x₀ : E) (B : History E) (he : ‖T x₀‖<r/4)
    (hx : ‖T (x₀+B.displacement)‖≤2*‖T x₀‖) (hv : f (x₀+B.displacement)≤f x₀)
    (hcache : B.gradient=G (x₀+B.displacement))
    (hslope : inner ℝ B.gradient (rfcFunctionDirection fullMemory B)<0) :
    let x := T (x₀+B.displacement)
    let y := T (rfcFunctionLinePoint T f fullMemory r x₀ B)
    let d := T (rfcFunctionDirection fullMemory B)
    let g := T.symm B.gradient
    let A := averagedDerivative (coordinateDerivative T H) x (y-x)
    y-x=lineLength g d (A d) • d ∧
      coordinateGradient T G y=searchedGradient g d (A d) ∧
      A.toLinearMap.IsSymmetric ∧ ‖A-ContinuousLinearMap.id ℝ E‖≤2*(L:ℝ)*‖T x₀‖ ∧
      0<lineLength g d (A d) ∧ y-x≠0 := by
  have hr := S.radius_pos
  let x := T (x₀+B.displacement)
  let y := T (rfcFunctionLinePoint T f fullMemory r x₀ B)
  let d := T (rfcFunctionDirection fullMemory B)
  let g := T.symm B.gradient
  let A := averagedDerivative (coordinateDerivative T H) x (y-x)
  have hline := S.line_localization x₀ B he hx hv
  have hsegment := S.segment_data x y (2*‖T x₀‖) hx hline.1 (by linarith)
  have hm := S.line_chord x₀ B (hx.trans (by linarith))
  have hf z (hz : z∈closedBall (0:E) r) := S.coordinate_f z
    (by simpa only [mem_closedBall,dist_zero_right] using hz)
  have hg z (hz : z∈closedBall (0:E) r) := S.coordinate_g z
    (by simpa only [mem_closedBall,dist_zero_right] using hz)
  have hgzero : coordinateGradient T G 0=0 := by simp only [coordinateGradient,map_zero,S.gradient_zero]
  have hquot := local_chord_operator_search (coordinateObjective T f) (coordinateGradient T G)
    (coordinateDerivative T H) S.radius_pos hgzero S.hessian_zero S.small S.lipschitz hf hg
    x d y (hx.trans_lt (by linarith)) hm
  have hcachec : coordinateGradient T G x=g := by
    simp only [x,g,coordinateGradient,T.symm_apply_apply,hcache]
  rw [hcachec] at hquot
  have hpair : inner ℝ g d=inner ℝ B.gradient (rfcFunctionDirection fullMemory B) := by
    dsimp only [g,d]
    rw [real_inner_comm,metric_primal_dual_pairing T S.inverse_symmetric,real_inner_comm]
  have hd : d≠0 := by intro hz;rw [←hpair,hz,inner_zero_right] at hslope;exact (lt_irrefl 0) hslope
  have hAhalf : ‖A-ContinuousLinearMap.id ℝ E‖≤1/2 := hsegment.2.2.trans
    ((mul_le_mul_of_nonneg_left (show 2*‖T x₀‖≤r by linarith) L.coe_nonneg).trans S.small)
  have hcurv : 0 < inner ℝ d (A d) :=
    (by positivity : 0<‖d‖^2/2).trans_le (inner_lower_of_identity_bound A hAhalf d)
  have halpha : 0<lineLength g d (A d) := by
    have hgcomm : inner ℝ d g=inner ℝ g d := real_inner_comm _ _
    rw [lineLength,hgcomm,hpair]
    exact div_pos (neg_pos.mpr hslope) hcurv
  refine ⟨hquot.1,hquot.2,hsegment.2.1,?_,halpha,?_⟩
  · exact hsegment.2.2.trans_eq (by ring)
  · rw [hquot.1]
    exact smul_ne_zero halpha.ne' hd

end
end krylov.Convergence
