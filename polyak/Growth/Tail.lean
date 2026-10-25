import polyak.Growth.Subexponential

/-!
Article: Appendix A, Lemma plateau.
Use: finite energy bounds give a uniform strict contraction of discounted states.
Proof: split consecutive pairs from a finite tail and iterate the remaining fraction.
-/

namespace polyak.Growth
noncomputable section
open Finset

/-- Article: total energy bound. Use: a left boundary window controls every finite prefix. -/
theorem mass_zero_le_boundary {b : ℕ → ℝ} (hb : ∀ k, 0 ≤ b k)
    (hsub : Subexponential b) {K : ℝ} (hK : 0 < K) (w : ℕ)
    (henergy : ∀ l, w ≤ l →
      mass b w (l+1) ≤ K*(energyWindow b w w+energyWindow b w l)) (j : ℕ) :
    mass b 0 j ≤ (1+2*K)*mass b 0 (2*w+1) := by
  have hw : energyWindow b w w = mass b 0 (2*w+1) := by
    simp only [energyWindow, Nat.sub_self]
    congr 1; omega
  have hmass := mass_nonneg hb 0 (2*w+1)
  by_cases hj : w ≤ j
  · have hs := mass_add (b := b) (Nat.zero_le w) hj
    have hleft := mass_mono hb (i := 0) (j := w) (k := 0)
      (l := 2*w+1) le_rfl (by omega)
    have hright := mass_le_boundary hb hsub hK w w henergy j hj
    rw [hw] at hright
    nlinarith
  · have hm := mass_mono hb (i := 0) (j := j) (k := 0)
      (l := 2*w+1) le_rfl (by omega)
    nlinarith

/-- Article: two consecutive discounted positions. Use: exact pair mass. -/
theorem mass_pair (b : ℕ → ℝ) (i : ℕ) : mass b i (i+2) = b i+b (i+1) := by
  simp [mass, Finset.sum_Ico_succ_top]

/-- Article: finite-tail contraction. Use: no summability assumption is necessary. -/
theorem mass_tail_geometric {b : ℕ → ℝ} (_hb : ∀ k, 0 ≤ b k)
    {D : ℝ} (hD : 1 < D)
    (hbound : ∀ i j, i ≤ j → mass b i j ≤ D*(b i+b (i+1)))
    (p N : ℕ) (hpN : 2*p ≤ N) :
    mass b (2*p) N ≤ (1-1/D)^p*mass b 0 N := by
  have hDp : 0 < D := zero_lt_one.trans hD
  have hθ : 0 ≤ 1-1/D := by
    have hh := (div_le_one hDp).2 hD.le
    linarith
  induction p with
  | zero => simp
  | succ p ih =>
    have hp : 2*p ≤ N := by omega
    have hpp : 2*p+2 ≤ N := by omega
    have hs := mass_add (b := b) (show 2*p ≤ 2*p+2 by omega) hpp
    rw [mass_pair] at hs
    have he := hbound (2*p) N hp
    have hstep : mass b (2*p+2) N ≤ (1-1/D)*mass b (2*p) N := by
      apply (mul_le_mul_iff_right₀ hDp).mp
      have heq : D*((1-1/D)*mass b (2*p) N) = (D-1)*mass b (2*p) N := by
        field_simp
      rw [heq]
      nlinarith
    calc
      mass b (2*(p+1)) N = mass b (2*p+2) N := by congr 1
      _ ≤ (1-1/D)*mass b (2*p) N := hstep
      _ ≤ (1-1/D)*((1-1/D)^p*mass b 0 N) :=
        mul_le_mul_of_nonneg_left (ih hp) hθ
      _ = _ := by rw [pow_succ]; ring

/-- Article: state contraction from a uniform energy bound.
Use: one fixed pair horizon contracts every admissible trajectory. -/
theorem pair_le_geometric {b : ℕ → ℝ} (hb : ∀ k, 0 ≤ b k)
    {D : ℝ} (hD : 1 < D)
    (hbound : ∀ i j, i ≤ j → mass b i j ≤ D*(b i+b (i+1))) (p : ℕ) :
    b (2*p)+b (2*p+1) ≤ (1-1/D)^p*D*(b 0+b 1) := by
  have ht := mass_tail_geometric hb hD hbound p (2*p+2) (by omega)
  rw [mass_pair] at ht
  have hθ : 0 ≤ 1-1/D := by
    have hh := (div_le_one (zero_lt_one.trans hD)).2 hD.le
    linarith
  calc
    _ ≤ (1-1/D)^p*mass b 0 (2*p+2) := ht
    _ ≤ (1-1/D)^p*(D*(b 0+b (0+1))) :=
      mul_le_mul_of_nonneg_left (hbound 0 _ (by omega)) (pow_nonneg hθ p)
    _ = _ := by simp only [zero_add]; ring

end
end polyak.Growth
