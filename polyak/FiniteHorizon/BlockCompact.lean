import polyak.FiniteHorizon.BlockCone

/-!
Article: Appendix C, actual global block compactness behind nearkernel.
Use: normalization of the initial window bounds every later Gram coordinate
by the elementary recurrence envelope, uniformly over all realization dimensions.
-/
noncomputable section
namespace polyak.FiniteHorizon
open Growth Growth.FiniteHorizon
open scoped BigOperators Topology Matrix.Norms.Elementwise

def blockPrefixTrace (H n : ℕ) (hHN : H≤n) (Y : WindowSpace n) : ℝ :=
  ∑ i : Fin (H+2), Y.1 ⟨i.val,by omega⟩ ⟨i.val,by omega⟩

@[fun_prop] theorem continuous_blockPrefixTrace (H n : ℕ) (hHN : H≤n) :
    Continuous (blockPrefixTrace H n hHN) := by unfold blockPrefixTrace; fun_prop

theorem normalized_block_norm_le {A B β : ℝ} {H n : ℕ} (hB : B≠0) (hHN : H≤n)
    {Y : WindowSpace n} (hY : Y∈blockCone A B β H n) (htrace : blockPrefixTrace H n hHN Y=1) :
    ‖Y‖≤(1+|A|+|B|+|β|)^(2*n) := by
  classical
  obtain ⟨x,hx⟩:=exists_gram_vectors hY.1
  let s:=segmentOfBlock hB hY x hx
  let C:=1+|A|+|B|+|β|
  have hC : 1≤C:=by dsimp [C]; linarith [abs_nonneg A,abs_nonneg B,abs_nonneg β]
  have hC0 : 0≤C:=by linarith
  have hp (i : Fin (n+2)) : s.x i=x i:=realizedPosition_fin x i
  have hg (i : Fin (n+2)) : Y.1 i i=‖x i‖^2:=by
    rw [←hx]
    exact real_inner_self_eq_norm_sq (x i)
  have hprefix : (∑ i : Fin (H+2), ‖s.x i‖^2)=1 := by
    rw [←htrace]
    unfold blockPrefixTrace
    apply Finset.sum_congr rfl
    intro i _
    rw [hg]
    have he:=hp ⟨i.val,by omega⟩
    exact congrArg (fun z => ‖z‖^2) he
  let i₀ : Fin (H+2):=⟨0,by omega⟩
  let i₁ : Fin (H+2):=⟨1,by omega⟩
  have hi : i₀≠i₁:=by intro h; have hh:=congrArg Fin.val h; simp [i₀,i₁] at hh
  have hsmall : (∑ i ∈ ({i₀,i₁} : Finset (Fin (H+2))), ‖s.x i‖^2)≤
      ∑ i : Fin (H+2), ‖s.x i‖^2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => sq_nonneg _)
  rw [Finset.sum_pair hi,hprefix] at hsmall
  have hstate : stateNorm s.x 0^2≤1:=by
    rw [stateNorm_sq]
    simpa only [i₀,i₁,Fin.val_mk,zero_add] using hsmall
  have hdiag (i : Fin (n+2)) : Y.1 i i≤C^(2*n) := by
    let l:=min i.val n
    have hni : ‖s.x i‖≤stateNorm s.x l := by
      by_cases hin : i.val≤n
      · dsimp [l]
        rw [Nat.min_eq_left hin]
        exact norm_left_le_stateNorm s.x i.val
      · have hilast : i.val=n+1:=by omega
        dsimp [l]
        rw [Nat.min_eq_right (by omega : n ≤ i.val),hilast]
        exact norm_right_le_stateNorm s.x n
    have henv : stateNorm s.x l≤C^n*stateNorm s.x 0 := by
      apply (s.stateNorm_le l (Nat.min_le_right _ _)).trans
      apply mul_le_mul_of_nonneg_right _ (stateNorm_nonneg _ _)
      exact pow_le_pow_right₀ hC (Nat.min_le_right _ _)
    rw [hg,←hp i]
    calc
      _≤(C^n*stateNorm s.x 0)^2:=
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (pow_nonneg hC0 n) (stateNorm_nonneg s.x 0))).mpr
          (hni.trans henv)
      _=(C^n)^2*stateNorm s.x 0^2:=mul_pow _ _ _
      _≤(C^n)^2:=by nlinarith [sq_nonneg (C^n)]
      _=C^(2*n):=by rw [←pow_mul]; congr 1; omega
  have hentry (i j : Fin (n+2)) : |Y.1 i j|≤C^(2*n):=by
    have he:=matrix_entry_le_half_diag hY.1 i j
    linarith [hdiag i,hdiag j]
  have hvalue (i : Fin n) : |Y.2 i|≤C^(2*n) := by
    have he:=s.abs_value_le (i.val+1) (by omega) (by omega)
    change |realizedValue Y.2 (i.val+1)|≤‖realizedPosition x (i.val+1)‖^2/2 at he
    rw [realizedValue_succ,show i.val+1=(i.castSucc.succ : ℕ) from rfl,realizedPosition_fin] at he
    have hd:=hdiag i.castSucc.succ
    rw [hg] at hd
    have hn : 0≤C^(2*n):=by positivity
    linarith
  rw [Prod.norm_def]
  apply max_le
  · apply (pi_norm_le_iff_of_nonneg (by positivity : (0 : ℝ)≤C^(2*n))).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg (by positivity : (0 : ℝ)≤C^(2*n))).mpr
    intro j
    exact hentry i j
  · apply (pi_norm_le_iff_of_nonneg (by positivity : (0 : ℝ)≤C^(2*n))).mpr
    intro i
    exact hvalue i

/-- The normalized global block set is genuinely compact, with memory-only pair constraints. -/
theorem normalized_block_isCompact (A B β : ℝ) (H n : ℕ) (hB : B≠0) (hHN : H≤n) :
    IsCompact {Y : WindowSpace n | Y∈blockCone A B β H n ∧ blockPrefixTrace H n hHN Y=1} := by
  have hclosed : IsClosed {Y : WindowSpace n | Y∈blockCone A B β H n ∧
      blockPrefixTrace H n hHN Y=1}:=
    (blockCone_isClosed A B β H n).inter
      (isClosed_eq (continuous_blockPrefixTrace H n hHN) continuous_const)
  apply (isCompact_closedBall (0 : WindowSpace n) ((1+|A|+|B|+|β|)^(2*n))).of_isClosed_subset hclosed
  intro Y hY
  rw [Metric.mem_closedBall,dist_zero_right]
  exact normalized_block_norm_le hB hHN hY.1 hY.2

end polyak.FiniteHorizon
