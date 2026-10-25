import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
Article: Appendix A, Lemma plateau.
Use: exact nonnegative interval masses and the finite-window growth argument.
-/

namespace polyak.Growth
noncomputable section
open Finset

/-- Article: discounted energy sums. Use: half-open intervals simplify exact concatenation. -/
def mass (b : ℕ → ℝ) (i j : ℕ) : ℝ := ∑ k ∈ Ico i j, b k

/-- Article: endpoint energy window. Use: include both endpoints of the width-w window. -/
def energyWindow (b : ℕ → ℝ) (w k : ℕ) : ℝ := mass b (k-w) (k+w+1)

/-- Article: nonnegative masses. Use: every partial sum has its natural order. -/
theorem mass_nonneg {b : ℕ → ℝ} (hb : ∀ k, 0 ≤ b k) (i j : ℕ) : 0 ≤ mass b i j :=
  sum_nonneg (fun k _ => hb k)

/-- Article: exact interval concatenation. Use: no overlap or missing endpoint in a mass split. -/
theorem mass_add {b : ℕ → ℝ} {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    mass b i j + mass b j k = mass b i k := by
  exact sum_Ico_consecutive b hij hjk

/-- Article: monotonicity of nonnegative interval masses. -/
theorem mass_mono {b : ℕ → ℝ} (hb : ∀ k, 0 ≤ b k) {i j k l : ℕ}
    (hki : k ≤ i) (hjl : j ≤ l) : mass b i j ≤ mass b k l := by
  exact sum_le_sum_of_subset_of_nonneg (by intro x hx; simp only [mem_Ico] at hx ⊢; omega)
    (fun x _ _ => hb x)

/-- Article: a single energy belongs to every interval containing its index. -/
theorem le_mass {b : ℕ → ℝ} (hb : ∀ k, 0 ≤ b k) {i j k : ℕ}
    (hik : i ≤ k) (hkj : k < j) : b k ≤ mass b i j :=
  single_le_sum (fun n _ => hb n) (mem_Ico.2 ⟨hik,hkj⟩)

/-- Article: Lemma plateau, endpoint forcing.
Proof: once the accumulated mass exceeds twice its left-boundary budget,
the energy inequality forces a fixed proportional mass in the next window. -/
theorem mass_step_ge {b : ℕ → ℝ} (hb : ∀ k, 0 ≤ b k)
    {K : ℝ} (hK : 0 < K) (w i j : ℕ) (hij : i ≤ j)
    (henergy : ∀ l, i ≤ l →
      mass b i (l+1) ≤ K*(energyWindow b w i+energyWindow b w l))
    (hlarge : 2*K*energyWindow b w i < mass b i j) :
    (1+1/(2*K))*mass b i j ≤ mass b i (j+(2*w+1)) := by
  have he := henergy (j+w) (by omega)
  have hw : energyWindow b w (j+w) = mass b j (j+(2*w+1)) := by
    simp only [energyWindow, Nat.add_sub_cancel]
    congr 1; omega
  rw [hw] at he
  have hm := mass_mono hb (i := i) (j := j) (k := i) (l := j+w+1)
    le_rfl (by omega)
  have hs := mass_add (b := b) hij (show j ≤ j+(2*w+1) by omega)
  have hdiv : 1/(2*K)*mass b i j ≤ mass b j (j+(2*w+1)) := by
    have hh : mass b i j ≤ mass b j (j+(2*w+1)) * (2*K) := by nlinarith
    calc
      1/(2*K)*mass b i j = mass b i j/(2*K) := by ring
      _ ≤ _ := (div_le_iff₀ (show 0 < 2*K by positivity)).2 hh
  nlinarith

/-- Article: Lemma plateau, iterative endpoint forcing.
Proof: nonnegative masses retain the initial strict threshold at every step. -/
theorem mass_ge_geometric {b : ℕ → ℝ} (hb : ∀ k, 0 ≤ b k)
    {K : ℝ} (hK : 0 < K) (w i j : ℕ) (hij : i ≤ j)
    (henergy : ∀ l, i ≤ l →
      mass b i (l+1) ≤ K*(energyWindow b w i+energyWindow b w l))
    (hlarge : 2*K*energyWindow b w i < mass b i j) (p : ℕ) :
    (1+1/(2*K))^p*mass b i j ≤ mass b i (j+p*(2*w+1)) := by
  have hθ : 0 ≤ 1+1/(2*K) := by positivity
  induction p with
  | zero => simp
  | succ p ih =>
    have hmon := mass_mono hb (i := i) (j := j) (k := i)
      (l := j+p*(2*w+1)) le_rfl (by omega)
    have hstep := mass_step_ge hb hK w i (j+p*(2*w+1)) (by omega) henergy
      (hlarge.trans_le hmon)
    calc
      _ = (1+1/(2*K))*((1+1/(2*K))^p*mass b i j) := by rw [pow_succ]; ring
      _ ≤ (1+1/(2*K))*mass b i (j+p*(2*w+1)) :=
        mul_le_mul_of_nonneg_left ih hθ
      _ ≤ _ := by simpa only [Nat.succ_eq_add_one, Nat.add_mul, one_mul, Nat.add_assoc] using hstep

end
end polyak.Growth
