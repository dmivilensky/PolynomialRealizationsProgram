import polyak.Growth.Mass
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
Article: Appendix A, Lemma plateau.
Use: turn the finite-window energy inequality into a uniform left-boundary bound.
Proof: a failed bound forces geometric mass growth, contradicting subexponential growth.
-/

namespace polyak.Growth
noncomputable section
open Finset Filter
open scoped Topology

/-- Article: subexponential discounted energy. Use: retain every positive exponent margin. -/
def Subexponential (b : ℕ → ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, b k ≤ C*Real.exp (δ*k)

/-- Article: finite mass majorant. Use: compare forced mass growth with a scalar exponential. -/
theorem mass_le_exp {b : ℕ → ℝ} (hb : ∀ k, 0 ≤ b k) {C δ : ℝ}
    (hC : 0 ≤ C) (hδ : 0 ≤ δ) (h : ∀ k : ℕ, b k ≤ C*Real.exp (δ*k))
    (i j : ℕ) : mass b i j ≤ j*C*Real.exp (δ*j) := by
  calc
    mass b i j ≤ mass b 0 j := mass_mono hb (Nat.zero_le _) le_rfl
    _ ≤ ∑ _k ∈ Ico 0 j, C*Real.exp (δ*j) := by
      apply sum_le_sum
      intro k hk
      exact (h k).trans (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
          (Nat.cast_le.mpr (mem_Ico.mp hk).2.le) hδ)) hC)
    _ = _ := by simp [mul_assoc]

/-- Article: Lemma plateau, scalar boundary estimate.
Proof: a strict threshold violation implies a fixed geometric increase; the
subexponential upper bound, divided by that geometric factor, tends to zero. -/
theorem mass_le_boundary {b : ℕ → ℝ} (hb : ∀ k, 0 ≤ b k)
    (hsub : Subexponential b) {K : ℝ} (hK : 0 < K) (w i : ℕ)
    (henergy : ∀ l, i ≤ l →
      mass b i (l+1) ≤ K*(energyWindow b w i+energyWindow b w l))
    (j : ℕ) (hij : i ≤ j) : mass b i j ≤ 2*K*energyWindow b w i := by
  by_contra hfail
  have hlarge : 2*K*energyWindow b w i < mass b i j := lt_of_not_ge hfail
  let θ : ℝ := 1+1/(2*K)
  let a : ℕ := 2*w+1
  have hθ : 1 < θ := by
    dsimp [θ]
    linarith [one_div_pos.mpr (show 0 < 2*K by positivity)]
  have hθp : 0 < θ := zero_lt_one.trans hθ
  have ha : (0 : ℝ) < a := Nat.cast_pos.mpr (by dsimp [a]; omega)
  let δ : ℝ := Real.log θ/(2*a)
  have hl : 0 < Real.log θ := Real.log_pos hθ
  have hδ : 0 < δ := div_pos hl (by positivity)
  obtain ⟨C,hC,hbC⟩ := hsub δ hδ
  let q : ℝ := Real.exp (δ*a)/θ
  have hq0 : 0 ≤ q := (div_pos (Real.exp_pos _) hθp).le
  have hq1 : q < 1 := by
    apply (div_lt_one hθp).2
    rw [← Real.exp_log hθp, Real.exp_lt_exp]
    dsimp [δ]
    have he : Real.log θ/(2*(a : ℝ))*(a : ℝ) = Real.log θ/2 := by field_simp
    rw [he]
    linarith
  have hbound (p : ℕ) : mass b i j ≤
      ((j : ℝ)+(p : ℝ)*a)*C*Real.exp (δ*j)*q^p := by
    have hlo := mass_ge_geometric hb hK w i j hij henergy hlarge p
    have hhi := mass_le_exp hb hC.le hδ.le hbC i (j+p*a)
    have he : Real.exp (δ*(↑(j+p*a) : ℝ)) =
        Real.exp (δ*j)*(Real.exp (δ*a))^p := by
      rw [Nat.cast_add, Nat.cast_mul]
      have hx : δ*((j : ℝ)+(p : ℝ)*a) = δ*j+(p : ℝ)*(δ*a) := by ring
      rw [hx, Real.exp_add, Real.exp_nat_mul]
    rw [he] at hhi
    change θ^p*mass b i j ≤ _ at hlo
    have hh := hlo.trans hhi
    have hd : mass b i j ≤ ↑(j+p*a)*C*
        (Real.exp (δ*j)*Real.exp (δ*a)^p)/θ^p :=
      (le_div_iff₀ (pow_pos hθp p)).mpr (by simpa only [mul_comm] using hh)
    convert hd using 1
    simp only [Nat.cast_add, Nat.cast_mul, q, div_pow]
    ring
  have hlim : Tendsto (fun p : ℕ =>
      ((j : ℝ)+(p : ℝ)*a)*C*Real.exp (δ*j)*q^p) atTop (𝓝 0) := by
    have hg := tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
    have hng := tendsto_self_mul_const_pow_of_lt_one hq0 hq1
    convert ((hg.const_mul (j : ℝ)).add (hng.const_mul (a : ℝ))).mul_const
      (C*Real.exp (δ*j)) using 1
    · funext p
      ring
    · simp
  have hm0 : mass b i j ≤ 0 := ge_of_tendsto hlim (Eventually.of_forall hbound)
  have hw0 := mass_nonneg hb (i-w) (i+w+1)
  change 0 ≤ energyWindow b w i at hw0
  nlinarith

end
end polyak.Growth
