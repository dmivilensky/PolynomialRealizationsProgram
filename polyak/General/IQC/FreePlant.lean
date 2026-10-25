import polyak.General.IQC.StablePlant

/-! Appendix D: the genuine two-initial-state free response is an ℓ²
sequence, with a coefficient bound independent of dimension or objective. -/

namespace polyak.General.IQC
noncomputable section
open Finset
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem convolution_squareSummable {h : ℕ → ℝ}
    (hh : Summable (fun n => |h n|)) {x : ℕ → E} (hx : SquareSummable x) :
    SquareSummable (convolution h x) := by
  apply squareSummable_of_prefix_bound (C := (∑' n,|h n|)*sequenceNorm x)
  intro N
  exact (convolution_prefix_gain hh x N).trans
    (mul_le_mul_of_nonneg_left (prefixNorm_le_sequenceNorm hx N)
      (tsum_nonneg (fun _ => abs_nonneg _)))

theorem convolution_sequenceNorm {h : ℕ → ℝ}
    (hh : Summable (fun n => |h n|)) {x : ℕ → E} (hx : SquareSummable x) :
    sequenceNorm (convolution h x) ≤ (∑' n,|h n|)*sequenceNorm x := by
  apply sequenceNorm_le_of_prefix_bound
    (mul_nonneg (tsum_nonneg (fun _ => abs_nonneg _)) (sequenceNorm_nonneg x))
  intro N
  exact (convolution_prefix_gain hh x N).trans
    (mul_le_mul_of_nonneg_left (prefixNorm_le_sequenceNorm hx N)
      (tsum_nonneg (fun _ => abs_nonneg _)))

def initialInput (b : ℝ) (previous start : E) : ℕ → E
  | 0 => start
  | 1 => -b • previous
  | _+2 => 0

theorem initialInput_squareSummable (b : ℝ) (previous start : E) :
    SquareSummable (initialInput b previous start) := by
  apply summable_of_ne_finset_zero (s := range 2)
  intro n hn
  have hn2 : 2 ≤ n := by have := not_lt.mp (fun h => hn (mem_range.mpr h)); omega
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn2
  simp [initialInput,Nat.add_comm 2]

theorem initialInput_norm (b : ℝ) (previous start : E) :
    sequenceNorm (initialInput b previous start) ≤ ‖start‖+|b| *‖previous‖ := by
  have hsum : (∑' n,‖initialInput b previous start n‖^2) =
      ‖start‖^2 + (|b| *‖previous‖)^2 := by
    rw [tsum_eq_sum (s := range 2)]
    · simp [sum_range_succ,initialInput,norm_smul,Real.norm_eq_abs]
    · intro n hn
      have hn2 : 2 ≤ n := by have := not_lt.mp (fun h => hn (mem_range.mpr h)); omega
      obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn2
      simp [initialInput,Nat.add_comm 2]
  unfold sequenceNorm
  rw [hsum]
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · have hcross : 0 ≤ ‖start‖*(|b| *‖previous‖) :=
      mul_nonneg (norm_nonneg start) (mul_nonneg (abs_nonneg b) (norm_nonneg previous))
    nlinarith only [hcross]

def freeResponse (A beta r : ℝ) (previous start : E) : ℕ → E :=
  convolution (fundamental (A/r) (beta/r^2)) (initialInput (beta/r^2) previous start)

@[simp] theorem freeResponse_zero (A beta r : ℝ) (previous start : E) :
    freeResponse A beta r previous start 0 = start := by
  simp [freeResponse,initialInput,fundamental]

theorem freeResponse_one (A beta r : ℝ) (previous start : E) :
    freeResponse A beta r previous start 1 =
      (A/r) • start - (beta/r^2) • previous := by
  simp [freeResponse,convolution_one,initialInput,fundamental,sub_eq_add_neg,neg_smul]

theorem freeResponse_recurrence (A beta r : ℝ) (previous start : E) (n : ℕ) :
    freeResponse A beta r previous start (n+2) =
      (A/r) • freeResponse A beta r previous start (n+1) -
      (beta/r^2) • freeResponse A beta r previous start n := by
  have h := convolution_recurrence
    (fun k => show fundamental (A/r) (beta/r^2) (k+2) =
      (A/r)*fundamental (A/r) (beta/r^2) (k+1)-
        (beta/r^2)*fundamental (A/r) (beta/r^2) k from rfl)
    (initialInput (beta/r^2) previous start) n
  simpa only [freeResponse,initialInput,fundamental,mul_one,sub_self,zero_smul,smul_zero,add_zero] using h

theorem freeResponse_squareSummable {A beta r : ℝ} (hbeta : 0 ≤ beta)
    (hr : rootRadius A beta < r) (previous start : E) :
    SquareSummable (freeResponse A beta r previous start) :=
  convolution_squareSummable (fundamental_scaled_summable hbeta hr)
    (initialInput_squareSummable _ _ _)

theorem freeResponse_norm_bound {A beta r : ℝ} (hbeta : 0 ≤ beta)
    (hr : rootRadius A beta < r) (previous start : E) :
    sequenceNorm (freeResponse A beta r previous start) ≤
      ((∑' n,|fundamental (A/r) (beta/r^2) n|)*(1+|beta/r^2|)) * (‖start‖+‖previous‖) := by
  have hmass : 0 ≤ ∑' n,|fundamental (A/r) (beta/r^2) n| := tsum_nonneg (fun _ => abs_nonneg _)
  calc
    _ ≤ (∑' n,|fundamental (A/r) (beta/r^2) n|)*sequenceNorm (initialInput (beta/r^2) previous start) :=
      convolution_sequenceNorm (fundamental_scaled_summable hbeta hr) (initialInput_squareSummable _ _ _)
    _ ≤ (∑' n,|fundamental (A/r) (beta/r^2) n|)*(‖start‖+|beta/r^2| *‖previous‖) :=
      mul_le_mul_of_nonneg_left (initialInput_norm _ _ _) hmass
    _ ≤ _ := by
      have hi : ‖start‖+|beta/r^2| *‖previous‖ ≤
          (1+|beta/r^2|)*(‖start‖+‖previous‖) := by
        nlinarith [mul_nonneg (abs_nonneg (beta/r^2)) (norm_nonneg start),norm_nonneg previous]
      have hmul := mul_le_mul_of_nonneg_left hi hmass
      nlinarith only [hmul]

theorem forced_decomposition (A B beta r : ℝ) (previous start : E)
    (input trajectory : ℕ → E)
    (hzero : trajectory 0=start)
    (hone : trajectory 1=(A/r) • start-(beta/r^2) • previous+(B/r) • input 0)
    (hrec : ∀ n, trajectory (n+2)=(A/r) • trajectory (n+1)-
      (beta/r^2) • trajectory n+(B/r) • input (n+1)) :
    trajectory=stablePlant A B beta r input+freeResponse A beta r previous start := by
  funext n
  induction n using Nat.twoStepInduction with
  | zero => simpa only [Pi.add_apply,stablePlant_zero,freeResponse_zero,zero_add] using hzero
  | one =>
    simp only [Pi.add_apply,stablePlant_one,freeResponse_one]
    rw [hone]
    module
  | more n ih ih1 =>
    change trajectory (n+2)=stablePlant A B beta r input (n+2)+freeResponse A beta r previous start (n+2)
    rw [hrec,stablePlant_recurrence,freeResponse_recurrence]
    simp only [Pi.add_apply] at ih ih1
    rw [ih,ih1]
    module

def originalFreeResponse (A beta r : ℝ) (previous start : E) : ℕ → E :=
  freeResponse A beta r (r • previous) start

def freeGain (A beta r : ℝ) : ℝ :=
  1+(∑' n,|fundamental (A/r) (beta/r^2) n|)*(1+|beta/r^2|)*(1+|r|)

theorem freeGain_pos (A beta r : ℝ) : 0 < freeGain A beta r := by
  have hmass : 0 ≤ ∑' n,|fundamental (A/r) (beta/r^2) n| := tsum_nonneg (fun _ => abs_nonneg _)
  unfold freeGain
  positivity

theorem originalFreeResponse_squareSummable {A beta r : ℝ} (hbeta : 0 ≤ beta)
    (hr : rootRadius A beta < r) (previous start : E) :
    SquareSummable (originalFreeResponse A beta r previous start) :=
  freeResponse_squareSummable hbeta hr _ _

theorem originalFreeResponse_norm_bound {A beta r : ℝ} (hbeta : 0 ≤ beta)
    (hr : rootRadius A beta < r) (previous start : E) :
    sequenceNorm (originalFreeResponse A beta r previous start) ≤
      freeGain A beta r*(‖start‖+‖previous‖) := by
  have h := freeResponse_norm_bound hbeta hr (r • previous) start
  rw [norm_smul,Real.norm_eq_abs] at h
  have hmass : 0 ≤ ∑' n,|fundamental (A/r) (beta/r^2) n| := tsum_nonneg (fun _ => abs_nonneg _)
  have hc : 0 ≤ (∑' n,|fundamental (A/r) (beta/r^2) n|)*(1+|beta/r^2|) := by positivity
  have hinner : ‖start‖+|r| *‖previous‖ ≤ (1+|r|)*(‖start‖+‖previous‖) := by
    nlinarith [mul_nonneg (abs_nonneg r) (norm_nonneg start),norm_nonneg previous]
  have hm := mul_le_mul_of_nonneg_left hinner hc
  change _ ≤ (1+(∑' n,|fundamental (A/r) (beta/r^2) n|)*(1+|beta/r^2|)*(1+|r|))*(‖start‖+‖previous‖)
  exact h.trans (by nlinarith [norm_nonneg start,norm_nonneg previous])

end
end polyak.General.IQC
