import krylov.Convergence.ObservableFCData
import krylov.Nonlinear.RFCSAveraged

/-!
Article: main_krylov, apG:Dunif, genuine canonical FC segment bounds.
Use: supply the finite staircase theorem with true averaged Hessians of
the actual scalar objective. Every segment enclosure and derivative
identity is derived from native search localization.
Source: the gradient FTC, Schwarz symmetry and Bochner integral norm bound.
-/
namespace krylov.Convergence
noncomputable section
open Set Metric Matrix krylov.Methods krylov.Functions krylov.Nonlinear chebyshev1.Nonlinear
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The true canonical gradient at the actual searched point.
Article: main_krylov, apG:Dunif. -/
def observableFCCanonicalGradient (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (r : ℝ) (x₀ : E) (k : ℕ) : E :=
  coordinateGradient T G (T (observableFCSearchPoint T f G r x₀ k))

/-- The true canonical displacement of the actual physical step.
Article: main_krylov, apG:Dunif. -/
def observableFCCanonicalStep (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (r : ℝ) (x₀ : E) (k : ℕ) : E := T (observableFCSearchStep T f G r x₀ k)

/-- The actual canonical average on the genuinely queried FC segment.
Article: main_krylov, apG:Dunif. -/
def observableFCCanonicalOperator (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (H : E → E →L[ℝ] E) (r : ℝ) (x₀ : E) (k : ℕ) : E →L[ℝ] E :=
  averagedDerivative (coordinateDerivative T H) (T (observableFCSearchPoint T f G r x₀ k))
    (observableFCCanonicalStep T f G r x₀ k)

/-- Actual FC segment averages have their genuine secant action,
symmetry and the uniform O(e_c) identity perturbation bound.
Article: main_krylov, apG:Dunif. -/
theorem ObservableLocalSource.fc_averaged_data {T : E ≃L[ℝ] E} {f : E → ℝ} {G : E → E}
    {H : E → E →L[ℝ] E} {r : ℝ} {L : ℝ≥0} (S : ObservableLocalSource T f G H r L)
    (x₀ : E) (hx₀ : ‖T x₀‖<r/4) (k : ℕ) :
    observableFCCanonicalGradient T f G r x₀ (k+1)-observableFCCanonicalGradient T f G r x₀ k=
      observableFCCanonicalOperator T f G H r x₀ k (observableFCCanonicalStep T f G r x₀ k) ∧
    (observableFCCanonicalOperator T f G H r x₀ k).toLinearMap.IsSymmetric ∧
    ‖observableFCCanonicalOperator T f G H r x₀ k-ContinuousLinearMap.id ℝ E‖≤2*(L:ℝ)*‖T x₀‖ := by
  have hr := S.radius_pos
  let x := fun j=>T (observableFCSearchPoint T f G r x₀ j)
  let s := observableFCCanonicalStep T f G r x₀ k
  have hs : s=x (k+1)-x k := by rw [←map_sub];rfl
  have hx j : ‖x j‖≤2*‖T x₀‖ := (S.fc_localization x₀ (by linarith) j).1
  have hseg t (ht : t∈Icc (0:ℝ) 1) : ‖x k+t • s‖≤2*‖T x₀‖ := by
    rw [hs]
    exact segment_norm_le_endpoints _ _ _ (hx k) (hx (k+1)) t ht
  have hball t (ht : t∈Icc (0:ℝ) 1) : x k+t • s∈closedBall (0:E) r := by
    rw [mem_closedBall,dist_zero_right]
    exact (hseg t ht).trans (by linarith [norm_nonneg (T x₀)])
  have hc := S.lipschitz.continuousOn.comp
    (continuous_const.add (continuous_id.smul continuous_const)).continuousOn hball
  have hftc := averagedDerivative_apply (coordinateGradient T G) (coordinateDerivative T H) (x k) s hc
    (fun t ht=>S.coordinate_g _ (by simpa only [mem_closedBall,dist_zero_right] using hball t ht))
  have hend : x k+s=x (k+1) := by rw [hs,add_sub_cancel]
  rw [hend] at hftc
  refine ⟨hftc.symm,?_,?_⟩
  · apply averagedDerivative_symmetric _ _ _ hc
    intro t ht
    apply genuine_hessian_symmetric (ContinuousLinearEquiv.refl ℝ E) (coordinateObjective T f)
      (coordinateGradient T G) (coordinateDerivative T H)
      (fun z hz=>S.coordinate_f z hz) (fun z hz=>S.coordinate_g z hz)
    exact (hseg t ht).trans_lt (by linarith)
  · apply averagedDerivative_sub_const_norm_le _ _ _ _ hc
    intro t ht
    have hh := S.lipschitz.norm_sub_le (hball t ht) (mem_closedBall_self S.radius_pos.le)
    rw [S.hessian_zero,sub_zero] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left (hseg t ht) L.coe_nonneg).trans_eq (by ring))

/-- Every actual FC search step is orthogonal to its actual returned
canonical gradient. Article: main_krylov, apG:Dunif. -/
theorem ObservableLocalSource.fc_line_orthogonal {T : E ≃L[ℝ] E} {f : E → ℝ} {G : E → E}
    {H : E → E →L[ℝ] E} {r : ℝ} {L : ℝ≥0} (S : ObservableLocalSource T f G H r L)
    (x₀ : E) (hx₀ : ‖T x₀‖<r/4) (k : ℕ) :
    inner ℝ (observableFCCanonicalStep T f G r x₀ k)
      (observableFCCanonicalGradient T f G r x₀ (k+1))=0 := by
  have hr := S.radius_pos
  let x := fun j=>T (observableFCSearchPoint T f G r x₀ j)
  let d := T (rfcFunctionDirection fullMemory (observableFCSearchRun T f G r x₀ k))
  have hx : ‖x k‖<r/2 := (S.fc_localization x₀ (by linarith) k).1.trans_lt (by linarith)
  have hm := S.fc_chord_steps x₀ (by linarith [norm_nonneg (T x₀)]) k
  have hf z (hz : z∈closedBall (0:E) r) := S.coordinate_f z
    (by simpa only [mem_closedBall,dist_zero_right] using hz)
  have hg z (hz : z∈closedBall (0:E) r) := S.coordinate_g z
    (by simpa only [mem_closedBall,dist_zero_right] using hz)
  have hgzero : coordinateGradient T G 0=0 := by simp only [coordinateGradient,map_zero,S.gradient_zero]
  have hstat := (local_chord_minimum_spec _ _ _ S.radius_pos hgzero S.hessian_zero S.small
    S.lipschitz hf hg (x k) d (x (k+1)) hx hm).2.2.1
  obtain ⟨alpha,halpha⟩ := hm.2.1
  change x (k+1)=x k+alpha • d at halpha
  have hs : observableFCCanonicalStep T f G r x₀ k=alpha • d := by
    change T (_-_) = _
    rw [map_sub]
    change x (k+1)-x k=_
    rw [halpha,add_sub_cancel_left]
  rw [hs,real_inner_smul_left,real_inner_comm]
  exact mul_eq_zero_of_right alpha hstat

omit [CompleteSpace E] in
/-- Actual past solved direction tests yield genuine canonical measured
triangular conjugacy. Article: main_krylov, apG:Dunif. -/
theorem ObservableLocalSource.fc_canonical_conjugate {T : E ≃L[ℝ] E} {f : E → ℝ} {G : E → E}
    {H : E → E →L[ℝ] E} {r : ℝ} {L : ℝ≥0} (S : ObservableLocalSource T f G H r L)
    (x₀ : E) (hx₀ : ‖T x₀‖<r/4) {i j : ℕ} (hij : i<j)
    (hgood : ObservableFCGood (observableFCSearchRun T f G r x₀ j)) :
    inner ℝ (observableFCCanonicalGradient T f G r x₀ (i+1)-observableFCCanonicalGradient T f G r x₀ i)
      (observableFCCanonicalStep T f G r x₀ j)=0 := by
  have hh := S.fc_step_conjugate x₀ hx₀ hij hgood
  have he : observableFCCanonicalGradient T f G r x₀ (i+1)-observableFCCanonicalGradient T f G r x₀ i=
      T.symm (observableFCSearchSecant T f G r x₀ i) := by
    simp only [observableFCCanonicalGradient,coordinateGradient,T.symm_apply_apply,map_sub,observableFCSearchSecant]
  rw [he]
  change inner ℝ (T.symm _) (T _)=0
  rw [real_inner_comm,metric_primal_dual_pairing T S.inverse_symmetric,real_inner_comm]
  exact hh

end
end krylov.Convergence
