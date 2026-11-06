import nesterov.Stationary.Execution

/-!
Article: Lemma `lem:envelope`, finiteness and zero-state absorption.
Use: dimension-independent finite-horizon bounds for actual trajectories.
-/
namespace nesterov.StationaryMethod
noncomputable section
open scoped BigOperators
variable (M : nesterov.StationaryMethod)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def queryGain : ℝ := ∑ j, |M.queryCoeff j|
def recurrenceGain : ℝ := ∑ j : Fin M.memory, |M.recurrenceCoeff j.castSucc|
def outputGain (L : ℝ) : ℝ :=
  (|L| * M.queryGain + M.recurrenceGain) / |M.recurrenceCoeff (Fin.last M.memory)|
def stepBound (L : ℝ) : ℝ := M.memory * (1 + M.outputGain L)

theorem queryGain_nonneg : 0 ≤ M.queryGain := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
theorem recurrenceGain_nonneg : 0 ≤ M.recurrenceGain := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
theorem outputGain_nonneg (L : ℝ) : 0 ≤ M.outputGain L := by
  exact div_nonneg (add_nonneg (mul_nonneg (abs_nonneg _) M.queryGain_nonneg)
    M.recurrenceGain_nonneg) (abs_nonneg _)
theorem stepBound_pos (L : ℝ) : 0 < M.stepBound L := by
  exact mul_pos (Nat.cast_pos.mpr M.memory_pos) (by linarith [M.outputGain_nonneg L])

theorem norm_query_le (w : ℕ → E) (k : ℕ) :
    ‖M.query w k‖ ≤ M.queryGain * M.stateNorm w k := by
  calc
    _ ≤ ∑ j : Fin M.memory, ‖M.queryCoeff j • w (k+j)‖ := norm_sum_le _ _
    _ = ∑ j : Fin M.memory, |M.queryCoeff j| * ‖w (k+j)‖ := by
      simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ j : Fin M.memory, |M.queryCoeff j| * M.stateNorm w k := by
      exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left
        (M.norm_le_stateNorm w k j) (abs_nonneg _))
    _ = _ := by rw [← Finset.sum_mul]; rfl

theorem IsTrajectory.norm_next_le {g : E → E} {w : ℕ → E}
    (h : M.IsTrajectory g w) {L : ℝ} (hg : ∀ x, ‖g x‖ ≤ |L| * ‖x‖) (k : ℕ) :
    ‖w (k+M.memory)‖ ≤ M.outputGain L * M.stateNorm w k := by
  have hc : 0 < |M.recurrenceCoeff (Fin.last M.memory)| := abs_pos.mpr M.leading_ne
  rw [h.step, norm_smul, Real.norm_eq_abs, abs_inv]
  calc
    _ ≤ |M.recurrenceCoeff (Fin.last M.memory)|⁻¹ *
      (‖g (M.query w k)‖ + ‖∑ j : Fin M.memory, M.recurrenceCoeff j.castSucc • w (k+j)‖) := by
      exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (inv_nonneg.mpr hc.le)
    _ ≤ |M.recurrenceCoeff (Fin.last M.memory)|⁻¹ *
      ((|L| * M.queryGain)*M.stateNorm w k + M.recurrenceGain * M.stateNorm w k) := by
      gcongr
      · exact (hg _).trans (by
          calc
            |L| * ‖M.query w k‖ ≤ |L| * (M.queryGain * M.stateNorm w k) :=
              mul_le_mul_of_nonneg_left (M.norm_query_le w k) (abs_nonneg L)
            _ = _ := by ring)
      · calc
          _ ≤ ∑ j : Fin M.memory, ‖M.recurrenceCoeff j.castSucc • w (k+j)‖ := norm_sum_le _ _
          _ = ∑ j : Fin M.memory, |M.recurrenceCoeff j.castSucc| * ‖w (k+j)‖ := by
            simp only [norm_smul, Real.norm_eq_abs]
          _ ≤ ∑ j : Fin M.memory, |M.recurrenceCoeff j.castSucc| * M.stateNorm w k := by
            exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left
              (M.norm_le_stateNorm w k j) (abs_nonneg _))
          _ = _ := by rw [← Finset.sum_mul]; rfl
    _ = _ := by dsimp [outputGain]; ring

theorem IsTrajectory.stateNorm_succ_le {g : E → E} {w : ℕ → E}
    (h : M.IsTrajectory g w) {L : ℝ} (hg : ∀ x, ‖g x‖ ≤ |L| * ‖x‖) (k : ℕ) :
    M.stateNorm w (k+1) ≤ M.stepBound L * M.stateNorm w k := by
  let R := (1+M.outputGain L)*M.stateNorm w k
  have hR : 0 ≤ R := mul_nonneg (by linarith [M.outputGain_nonneg L]) (M.stateNorm_nonneg w k)
  have hpoint (j : Fin M.memory) : ‖w (k+1+j)‖ ≤ R := by
    by_cases hj : j.val+1<M.memory
    · have hp := M.norm_le_stateNorm w k ⟨j+1,hj⟩
      have he : k+1+j = k+(j.val+1) := by omega
      rw [he]
      change ‖w (k+(j.val+1))‖ ≤ _ at hp ⊢
      exact hp.trans (by dsimp [R]; nlinarith [M.outputGain_nonneg L,M.stateNorm_nonneg w k])
    · have he : k+1+j = k+M.memory := by omega
      rw [he]
      exact (h.norm_next_le M hg k).trans (by dsimp [R]; nlinarith [M.stateNorm_nonneg w k])
  have hs : M.stateNorm w (k+1)^2 ≤ M.memory * R^2 := by
    rw [M.stateNorm_sq]
    calc
      _ ≤ ∑ _j : Fin M.memory, R^2 := Finset.sum_le_sum (fun j _ =>
        (sq_le_sq₀ (norm_nonneg _) hR).mpr (hpoint j))
      _ = _ := by simp
  have hd : (1:ℝ)≤M.memory := by exact_mod_cast M.memory_pos
  have hstep : M.stepBound L * M.stateNorm w k = M.memory * R := by dsimp [stepBound,R]; ring
  rw [hstep]
  have hnonneg := M.stateNorm_nonneg w (k+1)
  have hd2 : (M.memory:ℝ) ≤ (M.memory:ℝ)^2 := by nlinarith
  have hs2 := hs.trans (mul_le_mul_of_nonneg_right hd2 (sq_nonneg R))
  have hs3 : M.stateNorm w (k+1)^2 ≤ ((M.memory:ℝ)*R)^2 := by nlinarith [hs2]
  exact (sq_le_sq₀ hnonneg (mul_nonneg (Nat.cast_nonneg _) hR)).mp hs3

theorem IsTrajectory.stateNorm_le {g : E → E} {w : ℕ → E}
    (h : M.IsTrajectory g w) {L : ℝ} (hg : ∀ x, ‖g x‖ ≤ |L| * ‖x‖) (n : ℕ) :
    M.stateNorm w n ≤ (M.stepBound L)^n * M.stateNorm w 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    exact (h.stateNorm_succ_le M hg n).trans (by
      calc
        _ ≤ M.stepBound L * ((M.stepBound L)^n*M.stateNorm w 0) :=
          mul_le_mul_of_nonneg_left ih (M.stepBound_pos L).le
        _ = _ := by rw [pow_succ]; ring)

theorem IsTrajectory.zero_state_absorbing {g : E → E} {w : ℕ → E}
    (h : M.IsTrajectory g w) {L : ℝ} (hg : ∀ x, ‖g x‖ ≤ |L| * ‖x‖)
    {k : ℕ} (hk : M.stateNorm w k = 0) (n : ℕ) : M.stateNorm w (k+n) = 0 := by
  have hb := (h.shift M k).stateNorm_le M hg n
  simp only [M.stateNorm_shift,Nat.add_zero,hk,mul_zero] at hb
  exact le_antisymm hb (M.stateNorm_nonneg w _)

end
end nesterov.StationaryMethod
