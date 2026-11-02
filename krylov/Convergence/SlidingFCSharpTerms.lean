import krylov.Convergence.SlidingFCWeightedResidual
import krylov.Convergence.WindowSuperlinear

/-!
Article: main_krylov, thm:G, unique surviving FC staircase pair.
Use: derive that all pairs except the oldest/next pair are little-o of
its actual error product. Source: genuine segment-Hessian endpoint FTC
and superlinearity of the true trajectory, with no residual assumption.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Filter Topology Asymptotics krylov.Methods krylov.Functions chebyshev1.Nonlinear
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {n : ℕ}
set_option maxHeartbeats 1000000

/-- Genuine segment operator on the actual chronological path. -/
def fcPathSegment (H : E → E →L[ℝ] E) (x : ℕ → E) (k j : ℕ) : E →L[ℝ] E :=
  averagedDerivative H (x (k+j)) (x (k+j+1)-x (k+j))

/-- Genuine absolute mass of a real triangular staircase pair. -/
def fcPathPairMass (H : E → E →L[ℝ] E) (x : ℕ → E) (k : ℕ)
    (p : Fin (n+2) × Fin (n+2)) : ℝ :=
  if p.1<p.2 then ‖fcPathSegment H x k p.2.val-fcPathSegment H x k p.1.val‖*
    ‖x (k+p.2.val+1)-x (k+p.2.val)‖ else 0

/-- The sum of all actual staircase pairs except the oldest/next pair. -/
def fcPathNewerMass (H : E → E →L[ℝ] E) (x : ℕ → E) (k : ℕ) : ℝ :=
  ∑ p∈(Finset.univ.erase ((0,1):Fin (n+2) × Fin (n+2))),fcPathPairMass H x k p

/- Every step of age at least two is negligible relative to the actual
second-oldest error on a superlinear trajectory. -/
omit [InnerProductSpace ℝ E] in
theorem superlinear_late_step (x : ℕ → E)
    (hs : (fun k=>x (k+1))=o[atTop](fun k=>‖x k‖)) (j : ℕ) (hj : 2≤j) :
    (fun k=>‖x (k+j+1)-x (k+j)‖)=o[atTop](fun k=>‖x (k+1)‖) := by
  have ha : (fun k=>‖x (k+j)‖)=o[atTop](fun k=>‖x (k+1)‖) := by
    have hh := (superlinear_window_tail x hs (j-2)).comp_tendsto (tendsto_add_atTop_nat 1)
    simpa only [Function.comp_def,show ∀ k : ℕ,k+1+(j-2)+1=k+j from fun _=>by omega] using hh
  have hb : (fun k=>‖x (k+j+1)‖)=o[atTop](fun k=>‖x (k+1)‖) := by
    have hh := (superlinear_window_tail x hs (j-1)).comp_tendsto (tendsto_add_atTop_nat 1)
    simpa only [Function.comp_def,show ∀ k : ℕ,k+1+(j-1)+1=k+j+1 from fun _=>by omega] using hh
  apply IsLittleO.of_bound
  intro ε hε
  filter_upwards [(hb.add ha).def hε] with k hk
  simp only [norm_norm] at hk ⊢
  exact (norm_sub_le _ _).trans (by simpa only [Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))] using hk)

/-- Every true segment difference in the finite full FC frame is O of
its actual oldest error, by the original Hessian Lipschitz assumption. -/
theorem superlinear_fc_segment_difference
    (H : E → E →L[ℝ] E) (S : Set E) (hS : Convex ℝ S) (hn : S∈𝓝 (0:E))
    {L : ℝ≥0} (hH : LipschitzOnWith L H S) (x : ℕ → E)
    (hconv : Tendsto x atTop (𝓝 0)) (hs : (fun k=>x (k+1))=o[atTop](fun k=>‖x k‖))
    (i j : Fin (n+2)) :
    (fun k=>‖fcPathSegment H x k j.val-fcPathSegment H x k i.val‖)=O[atTop](fun k=>‖x k‖) := by
  have hmem : ∀ᶠ k in atTop,∀ a : Fin (n+3),x (k+a.val)∈S :=
    Filter.eventually_all.mpr fun a=>(hconv.comp (tendsto_add_atTop_nat a.val)).eventually hn
  have hage : ∀ᶠ k in atTop,∀ a : Fin (n+3),‖x (k+a.val)‖≤‖x k‖ := by
    apply Filter.eventually_all.mpr
    intro a
    by_cases ha : a.val=0
    · exact Filter.Eventually.of_forall fun k=>by simp only [ha,Nat.add_zero,le_refl]
    · have hh := (superlinear_window_tail x hs (a.val-1)).def (by norm_num : (0:ℝ)<1)
      simpa only [norm_norm,one_mul,show ∀ k : ℕ,k+(a.val-1)+1=k+a.val from fun _=>by omega] using hh
  apply IsBigO.of_bound (2*(L:ℝ))
  filter_upwards [hmem,hage] with k hm ha
  have hj₀ := hm ⟨j.val,by omega⟩
  have hj₁ := hm ⟨j.val+1,by omega⟩
  have hi₀ := hm ⟨i.val,by omega⟩
  have hi₁ := hm ⟨i.val+1,by omega⟩
  have hh := source_segment_comparison H S hS hH _ _ _ _ hj₀ hj₁ hi₀ hi₁
  have h₁ := (norm_sub_le (x (k+j.val)) (x (k+i.val))).trans
    (add_le_add (ha ⟨j.val,by omega⟩) (ha ⟨i.val,by omega⟩))
  have h₂ := (norm_sub_le (x (k+j.val+1)) (x (k+i.val+1))).trans
    (add_le_add (by simpa only [Nat.add_assoc] using ha ⟨j.val+1,by omega⟩)
      (by simpa only [Nat.add_assoc] using ha ⟨i.val+1,by omega⟩))
  simp only [Nat.add_assoc] at h₂
  simp only [norm_norm,fcPathSegment]
  apply hh.trans
  nlinarith only [h₁,h₂,L.coe_nonneg]

/-- Only the actual oldest/next pair survives on the printed error-product
scale; every other genuine staircase term is proved lower order. -/
theorem fcPathNewerMass_littleo
    (H : E → E →L[ℝ] E) (S : Set E) (hS : Convex ℝ S) (hn : S∈𝓝 (0:E))
    {L : ℝ≥0} (hH : LipschitzOnWith L H S) (x : ℕ → E)
    (hconv : Tendsto x atTop (𝓝 0)) (hs : (fun k=>x (k+1))=o[atTop](fun k=>‖x k‖)) :
    (fun k=>fcPathNewerMass (n:=n) H x k)=o[atTop](fun k=>‖x k‖*‖x (k+1)‖) := by
  have hp (p : Fin (n+2) × Fin (n+2)) (hpn : p≠(0,1)) :
      (fun k=>fcPathPairMass H x k p)=o[atTop](fun k=>‖x k‖*‖x (k+1)‖) := by
    by_cases hij : p.1<p.2
    · have hj : 2≤p.2.val := by
        by_contra! h
        have hi : p.1.val=0 := by have hh : p.1.val<p.2.val := hij;omega
        have hj' : p.2.val=1 := by have hh : p.1.val<p.2.val := hij;omega
        apply hpn
        exact Prod.ext (Fin.ext hi) (Fin.ext hj')
      have hh := (superlinear_fc_segment_difference H S hS hn hH x hconv hs p.1 p.2).mul_isLittleO
        (superlinear_late_step x hs p.2.val hj)
      simpa only [fcPathPairMass,ite_eq_left hij] using hh
    · simpa only [fcPathPairMass,ite_eq_right hij] using
        (isLittleO_zero (fun k=>‖x k‖*‖x (k+1)‖) atTop : (fun _ : ℕ=>(0:ℝ))=o[atTop]_)
  have hh := IsLittleO.sum (s:=Finset.univ.erase ((0,1):Fin (n+2) × Fin (n+2)))
    (fun p hp'=>hp p (Finset.mem_erase.mp hp').1)
  apply hh.congr_left
  intro k
  simp only [fcPathNewerMass,Finset.sum_apply]

end
end krylov.Convergence
