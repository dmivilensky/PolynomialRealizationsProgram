import krylov.Convergence.ObservableFCTrace
import krylov.Functions.NativeRFCSymmetry

/-!
Article: main_krylov, apG:Dunif, genuine source of observable FC prefixes.
Use: localize every actual searched observation using its real scalar
objective before any inverse-domain or normalized secant estimate.
Source: the existing true metric chord search, local scalar potential
comparison and Bochner averaged-Hessian fundamental theorem of calculus.
-/
namespace krylov.Convergence
noncomputable section
open Set Metric Matrix krylov.Methods krylov.Functions krylov.Nonlinear chebyshev1.Nonlinear
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Primitive true local scalar derivative data in the actual reference
metric. No trajectory, step length, rank or rate is a field.
Article: main_krylov, apG:Dunif. -/
structure ObservableLocalSource (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (H : E → E →L[ℝ] E) (r : ℝ) (L : ℝ≥0) : Prop where
  inverse_symmetric : T.symm.toContinuousLinearMap.IsSymmetric
  radius_pos : 0<r
  gradient_zero : G 0=0
  hessian_zero : coordinateDerivative T H 0=ContinuousLinearMap.id ℝ E
  small : (L:ℝ)*r≤1/2
  lipschitz : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r)
  f_derivative : ∀ z,‖T z‖≤r → HasFDerivAt f (innerSL ℝ (G z)) z
  g_derivative : ∀ z,‖T z‖≤r → HasFDerivAt G (H z) z

/-- The actual appended FC record ends at its genuinely searched point.
Article: main_krylov, apG:Dunif, exact native endpoint dictionary. -/
theorem observableFCSearchPoint_succ (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (r : ℝ) (x₀ : E) (k : ℕ) :
    observableFCSearchPoint T f G r x₀ (k+1)=
      rfcFunctionLinePoint T f fullMemory r x₀ (observableFCSearchRun T f G r x₀ k) := by
  have hh := observableRecord_endpoint T f G r x₀ (observableFCSearchRun T f G r x₀ k) 0 false
  simp only [add_zero] at hh
  change x₀+((observableRecord T f G r x₀ (observableFCSearchRun T f G r x₀ k) 0 false).step+
    (observableFCSearchRun T f G r x₀ k).displacement)=_
  rw [←hh]
  abel

/-- Every true local source supplies the actual pulled-back scalar
gradient derivative; this is an actual chain rule, not an oracle field.
Article: main_krylov, apG:Dunif. -/
theorem ObservableLocalSource.coordinate_f {T : E ≃L[ℝ] E} {f : E → ℝ} {G : E → E}
    {H : E → E →L[ℝ] E} {r : ℝ} {L : ℝ≥0} (S : ObservableLocalSource T f G H r L)
    (z : E) (hz : ‖z‖≤r) :
    HasFDerivAt (coordinateObjective T f) (innerSL ℝ (coordinateGradient T G z)) z := by
  apply coordinateObjective_hasFDerivAt T S.inverse_symmetric f G z
  exact S.f_derivative _ (by simpa only [T.apply_symm_apply] using hz)

/-- The pulled-back true gradient has the actual congruence Hessian.
Article: main_krylov, apG:Dunif. -/
theorem ObservableLocalSource.coordinate_g {T : E ≃L[ℝ] E} {f : E → ℝ} {G : E → E}
    {H : E → E →L[ℝ] E} {r : ℝ} {L : ℝ≥0} (S : ObservableLocalSource T f G H r L)
    (z : E) (hz : ‖z‖≤r) :
    HasFDerivAt (coordinateGradient T G) (coordinateDerivative T H z) z := by
  apply coordinateGradient_hasFDerivAt T G H z
  exact S.g_derivative _ (by simpa only [T.apply_symm_apply] using hz)

/-- Every actual searched FC prefix is a true metric chord minimum,
including prefixes whose later observable direction test will fail.
Article: main_krylov, apG:Dunif, no nondegeneracy prerequisite. -/
theorem ObservableLocalSource.fc_chord_steps {T : E ≃L[ℝ] E} {f : E → ℝ} {G : E → E}
    {H : E → E →L[ℝ] E} {r : ℝ} {L : ℝ≥0} (S : ObservableLocalSource T f G H r L)
    (x₀ : E) (hx₀ : ‖T x₀‖≤r) :
    ∀ k,IsChordMinimum (coordinateObjective T f) (T (observableFCSearchPoint T f G r x₀ k))
      (T (rfcFunctionDirection fullMemory (observableFCSearchRun T f G r x₀ k))) r
      (T (observableFCSearchPoint T f G r x₀ (k+1))) := by
  have hf z (hz : z∈closedBall (0:E) r) := S.coordinate_f z
    (by simpa only [mem_closedBall,dist_zero_right] using hz)
  have hg z (hz : z∈closedBall (0:E) r) := S.coordinate_g z
    (by simpa only [mem_closedBall,dist_zero_right] using hz)
  have hb : ∀ k,T (observableFCSearchPoint T f G r x₀ k)∈closedBall (0:E) r := by
    intro k
    induction k with
    | zero => simpa only [observableFCSearchPoint,observableFCSearchRun,History.displacement,
        List.map_nil,List.sum_nil,add_zero,mem_closedBall,dist_zero_right] using hx₀
    | succ k ih =>
      rw [observableFCSearchPoint_succ]
      change T (T.symm (localExactPoint _ _ _ r))∈_
      rw [T.apply_symm_apply]
      exact (localExactPoint_spec _ _ _ r (existsUnique_local_chord_minimum _ _ _ S.radius_pos
        S.hessian_zero S.small S.lipschitz hf hg _ _ ih)).1
  intro k
  rw [observableFCSearchPoint_succ]
  change IsChordMinimum _ _ _ r (T (T.symm (localExactPoint _ _ _ r)))
  rw [T.apply_symm_apply]
  exact localExactPoint_spec _ _ _ r (existsUnique_local_chord_minimum _ _ _ S.radius_pos
    S.hessian_zero S.small S.lipschitz hf hg _ _ (hb k))

variable [CompleteSpace E]

/-- Every actual search-only FC query lies in the original starting
sublevel and in a ball at most twice its true initial canonical error.
Article: main_krylov, apG:Dunif, actual query localization. -/
theorem ObservableLocalSource.fc_localization {T : E ≃L[ℝ] E} {f : E → ℝ} {G : E → E}
    {H : E → E →L[ℝ] E} {r : ℝ} {L : ℝ≥0} (S : ObservableLocalSource T f G H r L)
    (x₀ : E) (hx₀ : ‖T x₀‖<r/2) (k : ℕ) :
    ‖T (observableFCSearchPoint T f G r x₀ k)‖≤2*‖T x₀‖ ∧
      f (observableFCSearchPoint T f G r x₀ k)≤f x₀ := by
  have hx : ‖T x₀‖≤r := by linarith [norm_nonneg (T x₀)]
  have hsteps := S.fc_chord_steps x₀ hx
  have hzero : observableFCSearchPoint T f G r x₀ 0=x₀ := by
    simp only [observableFCSearchPoint,observableFCSearchRun,History.displacement,List.map_nil,List.sum_nil,add_zero]
  have hf z (hz : z∈closedBall (0:E) r) := S.coordinate_f z
    (by simpa only [mem_closedBall,dist_zero_right] using hz)
  have hg z (hz : z∈closedBall (0:E) r) := S.coordinate_g z
    (by simpa only [mem_closedBall,dist_zero_right] using hz)
  have hgzero : coordinateGradient T G 0=0 := by simp only [coordinateGradient,map_zero,S.gradient_zero]
  let x := fun j=>T (observableFCSearchPoint T f G r x₀ j)
  let d := fun j=>T (rfcFunctionDirection fullMemory (observableFCSearchRun T f G r x₀ j))
  have hloc := exact_search_trajectory_localization _ _ _ S.radius_pos hgzero S.hessian_zero
    S.small S.lipschitz hf hg x d k (by simpa only [x,hzero] using hx₀)
      (fun j _=>hsteps j) k le_rfl
  have hval := exact_search_trajectory_sublevel (coordinateObjective T f) x d r k
    (by simpa only [x,hzero,mem_closedBall,dist_zero_right] using hx) (fun j _=>hsteps j) k le_rfl
  have hsqrt : Real.sqrt (3:ℝ)≤2 := Real.sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
  refine ⟨?_,?_⟩
  · simpa only [x,hzero] using hloc.1.trans (mul_le_mul_of_nonneg_right hsqrt (norm_nonneg (x 0)))
  · simpa only [x,hzero,coordinateObjective_apply] using hval.2

end
end krylov.Convergence
