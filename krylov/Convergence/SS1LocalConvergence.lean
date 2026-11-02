import krylov.Convergence.SS1Execution
import krylov.Convergence.SS1LocalBounds

/-!
Article: main_krylov, lem:ss1-local.
Use: prove convergence of the actual recursive SS1 execution from a small
finite initial history. The window condition concerns only its actual
normalized observed steps; no convergence assumption is made here.
Source: the Appendix G invariant-ball argument and a geometric majorant.
-/

namespace krylov.Convergence
noncomputable section
open Matrix Filter Topology Asymptotics Set Metric krylov.LinearAlgebra
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {n : ℕ}

/-- Every genuine SS1 trajectory whose actual windows remain uniformly
independent converges from the stated small initial ball. The inverse domain
and the invariant ball follow from the genuine local model estimate. -/
theorem ss1Sequence_local_convergence
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (H : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+1)))
    (S : Set (EuclideanSpace ℝ (Fin (n+1)))) (hS : Convex ℝ S)
    {L : ℝ≥0} (hH : LipschitzOnWith L H S) (hH₀ : H 0=ContinuousLinearMap.id ℝ _)
    (hG : ∀ z∈S, HasFDerivAt G (H z) z) (hG₀ : G 0=0)
    (seed : Fin (n+2) → EuclideanSpace ℝ (Fin (n+1)))
    {r C : ℝ} (hr : 0<r) (hC : 0≤C)
    (hball : closedBall (0:EuclideanSpace ℝ (Fin (n+1))) r⊆S)
    (hseed : ∀ i,‖seed i‖≤r)
    (hind : ∀ k,
      IsUnit (windowMatrix (unitWindow (windowStep (n:=n+1) (ss1Sequence G seed) k))).det ∧
      ‖(windowMatrix (unitWindow (windowStep (n:=n+1) (ss1Sequence G seed) k)))⁻¹‖≤C)
    (hsmall : 2*(L:ℝ)*r*(1+(n+1)*C^2)≤1/2) :
    (∀ k,‖ss1Sequence G seed k‖≤r) ∧
    (∀ k,‖ss1Sequence G seed (k+n+2)‖≤(1/2:ℝ)*‖ss1Sequence G seed (k+n+1)‖) ∧
    Tendsto (ss1Sequence G seed) atTop (𝓝 0) := by
  let x := ss1Sequence G seed
  have h₀ : (0:EuclideanSpace ℝ (Fin (n+1)))∈S := hball (by simpa using hr.le)
  have hsmall' : C^2*((n+1)*((L:ℝ)*r))≤1/2 := by
    have hpos : 0≤(L:ℝ)*r := mul_nonneg L.coe_nonneg hr.le
    have hdim : 0≤(n+1:ℝ)*C^2 := mul_nonneg (by positivity) (sq_nonneg C)
    nlinarith only [hsmall,hpos,hdim,mul_nonneg hpos hdim]
  have hstep (o : ℕ) (hp : ∀ j<o+n+2,‖x j‖≤r) :
      ‖x (o+n+2)‖≤(1/2:ℝ)*‖x (o+n+1)‖ := by
    have ha (i : Fin (n+1)) : ‖x (o+i.val)‖≤r := hp _ (by omega)
    have hb (i : Fin (n+1)) : ‖x (o+i.val+1)‖≤r := hp _ (by omega)
    have hx : ‖x (o+n+1)‖≤r := hp _ (by omega)
    have hmem (j : ℕ) (hj : ‖x j‖≤r) : x j∈S :=
      hball (by simpa only [mem_closedBall,dist_zero_right] using hj)
    rw [show x (o+n+2)=ss1Point (windowStep (n:=n+1) x o) (windowImage G x o)
      (G (x (o+n+1))) (x (o+n+1)) from ss1Sequence_step G seed o]
    exact (ss1_local_step_bound G H S hS h₀ hH hH₀ hG hG₀
      (fun i : Fin (n+1)=>x (o+i.val)) (fun i=>x (o+i.val+1)) (x (o+n+1))
      (fun i=>hmem _ (ha i)) (fun i=>hmem _ (hb i)) (hmem _ hx) hr.le hC
      ha hb hx (hind o).1 (hind o).2
      (by simpa only [Nat.cast_add,Nat.cast_one] using hsmall')).trans
      (mul_le_mul_of_nonneg_right
        (by simpa only [Nat.cast_add,Nat.cast_one] using hsmall) (norm_nonneg _))
  have hall : ∀ k,‖x k‖≤r := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      by_cases hk : k<n+2
      · have hxseed : x k=seed ⟨k,hk⟩ := slidingSequence_seed (ss1WindowRule G) seed ⟨k,hk⟩
        rw [hxseed]
        exact hseed ⟨k,hk⟩
      · let o := k-(n+2)
        have ho : o+n+2=k := by dsimp [o]; omega
        rw [←ho]
        have hh := hstep o (by simpa only [ho] using ih)
        exact hh.trans ((mul_le_mul_of_nonneg_left (ih (o+n+1) (by omega))
          (by norm_num : (0:ℝ)≤1/2)).trans (by linarith))
  have hc (k : ℕ) : ‖x (k+n+2)‖≤(1/2:ℝ)*‖x (k+n+1)‖ := hstep k (fun j _=>hall j)
  have hgeom (k : ℕ) : ‖x (k+n+1)‖≤(1/2:ℝ)^k*‖x (n+1)‖ := by
    induction k with
    | zero => simp only [Nat.zero_add,pow_zero,one_mul]; exact le_rfl
    | succ k ih =>
      rw [show k+1+n+1=k+n+2 by omega]
      calc
        _ ≤ (1/2:ℝ)*‖x (k+n+1)‖ := hc k
        _ ≤ (1/2:ℝ)*((1/2:ℝ)^k*‖x (n+1)‖) := mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = _ := by rw [pow_succ]; ring
  have ht : Tendsto (fun k=>x (k+(n+1))) atTop (𝓝 0) := by
    apply squeeze_zero_norm
    · intro k
      simpa only [Nat.add_assoc] using hgeom k
    · simpa only [zero_mul] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2)
          (by norm_num : (1/2:ℝ)<1)).mul_const ‖x (n+1)‖
  exact ⟨hall,hc,(tendsto_add_atTop_iff_nat (n+1)).mp ht⟩

end
end krylov.Convergence
