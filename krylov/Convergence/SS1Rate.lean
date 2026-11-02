import krylov.Convergence.SS1Execution
import krylov.Convergence.SS1LocalBounds
import krylov.Convergence.RecurrenceOrder

/-!
Article: main_krylov, thm:Ip, SS1 R-order per gradient.
Use: derive the real delayed product recurrence from actual local secants and
the genuine recursive executor, then apply the proved scalar order theorem.
Source: Burdakov83 multipoint secant iteration, Appendix G local estimates,
and Ortega--Rheinboldt's characteristic majorant argument.
-/

namespace krylov.Convergence
noncomputable section
open Matrix Filter Topology Asymptotics Set krylov.LinearAlgebra
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {n : ℕ}

/-- The original convergent, uniformly independent SS1 trajectory satisfies
an actual delayed error product. This recurrence is derived, not an input
to the subsequent characteristic-order theorem. -/
theorem ss1Sequence_product_recurrence
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (H : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+1)))
    (S : Set (EuclideanSpace ℝ (Fin (n+1)))) (hS : Convex ℝ S)
    (h₀ : (0:EuclideanSpace ℝ (Fin (n+1)))∈S) (hnbhd : S∈𝓝 0)
    {L : ℝ≥0} (hH : LipschitzOnWith L H S) (hH₀ : H 0=ContinuousLinearMap.id ℝ _)
    (hG : ∀ z∈S, HasFDerivAt G (H z) z) (hG₀ : G 0=0)
    (seed : Fin (n+2) → EuclideanSpace ℝ (Fin (n+1)))
    (hconv : Tendsto (ss1Sequence G seed) atTop (𝓝 0)) {σ : ℝ} (hσ : 0<σ)
    (hind : ∀ᶠ k in atTop,
      IsUnit (windowMatrix (unitWindow (windowStep (ss1Sequence G seed) k))).det ∧
      σ≤leastGain (windowMatrix (unitWindow (windowStep (ss1Sequence G seed) k)))) :
    ∃ K : ℝ,0<K ∧∀ᶠ k in atTop,
      ‖ss1Sequence G seed (k+1)‖≤K*‖ss1Sequence G seed (k-(n+1))‖*‖ss1Sequence G seed k‖ := by
  let x := ss1Sequence G seed
  let C := σ⁻¹
  have hC : 0≤C := inv_nonneg.mpr hσ.le
  have hs := ss1Sequence_superlinear G H S hS h₀ hnbhd hH hH₀ hG hG₀ seed hconv hσ hind
  have hmono : ∀ᶠ k in atTop,‖x (k+1)‖≤‖x k‖ := by
    simpa only [one_mul,norm_norm] using hs.def (by norm_num : (0:ℝ)<1)
  have hmem : ∀ᶠ k in atTop,x k∈S := hconv.eventually hnbhd
  have hsmall : ∀ᶠ k in atTop,C^2*(((n+1:ℕ):ℝ)*((L:ℝ)*‖x k‖))≤1/2 := by
    have ht : Tendsto (fun k=>C^2*(((n+1:ℕ):ℝ)*((L:ℝ)*‖x k‖))) atTop (𝓝 0) := by
      simpa only [norm_zero,mul_zero] using
        ((hconv.norm.const_mul (L:ℝ)).const_mul ((n+1:ℕ):ℝ)).const_mul (C^2)
    exact (ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))).mono fun _ h=>h.le
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hmono.and (hmem.and (hind.and hsmall)))
  have htail (o : ℕ) (ho : N≤o) (j : ℕ) : ‖x (o+j)‖≤‖x o‖ := by
    induction j with
    | zero => simp only [Nat.add_zero]; exact le_rfl
    | succ j ih =>
      have hh := (hN (o+j) (by omega)).1
      exact hh.trans ih
  let K := 2*(L:ℝ)*(1+((n+1:ℕ):ℝ)*C^2)+1
  have hK : 0<K := by dsimp only [K]; positivity
  refine ⟨K,hK,?_⟩
  filter_upwards [eventually_ge_atTop (N+n+1)] with k hk
  let o := k-(n+1)
  have ho : N≤o := by dsimp only [o]; omega
  have hidx : o+n+1=k := by dsimp only [o]; omega
  have hV := (hN o ho).2.2.1
  have hinv := Secant.inverse_bound_of_leastGain _ hV.1 hσ hV.2
  have hm (i : ℕ) : x (o+i)∈S := (hN (o+i) (by omega)).2.1
  have hh := ss1_local_step_bound G H S hS h₀ hH hH₀ hG hG₀
    (fun i : Fin (n+1)=>x (o+i.val)) (fun i=>x (o+i.val+1)) (x (o+n+1))
    (fun i=>hm i.val) (fun i=>by simpa only [Nat.add_assoc] using hm (i.val+1))
    (by simpa only [Nat.add_assoc] using hm (n+1)) (norm_nonneg _) hC
    (fun i=>htail o ho i.val) (fun i=>by simpa only [Nat.add_assoc] using htail o ho (i.val+1))
    (by simpa only [Nat.add_assoc] using htail o ho (n+1)) hV.1 hinv (hN o ho).2.2.2
  have hquery : ss1Point (fun i : Fin (n+1)=>x (o+i.val+1)-x (o+i.val))
      (fun i=>G (x (o+i.val+1))-G (x (o+i.val))) (G (x (o+n+1))) (x (o+n+1))=
      x (o+n+2) := (ss1Sequence_step G seed o).symm
  rw [hquery,show o+n+2=k+1 by omega,hidx] at hh
  apply hh.trans
  have hcoef : 2*(L:ℝ)*(1+((n+1:ℕ):ℝ)*C^2)≤K := by dsimp only [K]; linarith
  have he := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef (norm_nonneg (x o)))
    (norm_nonneg (x k))
  convert he using 1
  dsimp only [o]
  ring

/-- SS1 has its printed characteristic R-order per gradient, on the genuine
recursive observed-gradient execution and under the original local source
and window independence hypotheses. -/
theorem ss1Sequence_rorder
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (H : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+1)))
    (S : Set (EuclideanSpace ℝ (Fin (n+1)))) (hS : Convex ℝ S)
    (h₀ : (0:EuclideanSpace ℝ (Fin (n+1)))∈S) (hnbhd : S∈𝓝 0)
    {L : ℝ≥0} (hH : LipschitzOnWith L H S) (hH₀ : H 0=ContinuousLinearMap.id ℝ _)
    (hG : ∀ z∈S, HasFDerivAt G (H z) z) (hG₀ : G 0=0)
    (seed : Fin (n+2) → EuclideanSpace ℝ (Fin (n+1)))
    (hconv : Tendsto (ss1Sequence G seed) atTop (𝓝 0)) {σ : ℝ} (hσ : 0<σ)
    (hind : ∀ᶠ k in atTop,
      IsUnit (windowMatrix (unitWindow (windowStep (ss1Sequence G seed) k))).det ∧
      σ≤leastGain (windowMatrix (unitWindow (windowStep (ss1Sequence G seed) k)))) :
    HasROrder (fun k=>‖ss1Sequence G seed k‖) (oneGradientRoot (n+2)) := by
  have hh := ss1Sequence_product_recurrence G H S hS h₀ hnbhd hH hH₀ hG hG₀ seed hconv hσ hind
  simpa only [oneGradientRoot,show n+2-1=n+1 by omega,Nat.sub_zero] using
    rorder_product_recurrence (fun k=>‖ss1Sequence G seed k‖) (fun _=>norm_nonneg _)
      (by simpa only [norm_zero] using hconv.norm) (n+1) 0 (Nat.zero_le _) hh

end
end krylov.Convergence
