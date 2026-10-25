import polyak.Realization.ExplicitSpiral.Ranges

/-!
Article: the small-condition-number part of the Y=2 initialization.
Use: close all positive-time exceptional pairs with one uniform rational
margin; no finite time truncation or numerical sampling enters this case.
Proof: the exact correction identity, complex norm inequalities, and the
uniform upper bound on the positive scalar response.
-/

namespace polyak.Realization.ExplicitSpiral
noncomputable section

/-- Article: the scalar response is exactly the printed even/odd single power. -/
theorem response_source (q : ℝ) (k : ℕ) :
    response 0 (q^2) k=(-q^2)^((k+1)/2) := by
  rcases Nat.mod_two_eq_zero_or_one k with hmod | hmod
  · have he : k=2*(k/2) := by omega
    rw [he,(response_polyak_even q (k/2)).1]
    congr 1
    omega
  · have he : k=2*(k/2)+1 := by omega
    rw [he,(response_polyak_even q (k/2)).2]
    congr 1
    omega

/-- Article: every positive power of -q² is at most q⁴. -/
theorem neg_square_pow_le_fourth {q : ℝ} (hq : 0≤q) (hq1 : q≤1) (n : ℕ) (hn : 1≤n) :
    (-q^2)^n≤q^4 := by
  by_cases he : n=1
  · subst n
    simp only [pow_one]
    nlinarith [sq_nonneg q,sq_nonneg (q^2)]
  · have hq2 : q^2≤1 := by nlinarith
    calc
      (-q^2)^n≤|(-q^2)^n| := le_abs_self _
      _ = (q^2)^n := by rw [abs_pow,abs_neg,abs_of_nonneg (sq_nonneg q)]
      _ ≤ (q^2)^2 := pow_le_pow_of_le_one (sq_nonneg q) hq2 (by omega)
      _ = q^4 := by ring

/-- Article: the actual τ=0 scalar response never exceeds q⁴ after time zero. -/
theorem response_le_fourth {q : ℝ} (hq : 0≤q) (hq1 : q≤1) (k : ℕ) (hk : 1≤k) :
    response 0 (q^2) k≤q^4 := by
  have hdiv := Nat.mod_add_div k 2
  rcases Nat.mod_two_eq_zero_or_one k with hmod | hmod
  · have he : k=2*(k/2) := by omega
    rw [he,(response_polyak_even q (k/2)).1]
    exact neg_square_pow_le_fourth hq hq1 _ (by omega)
  · have he : k=2*(k/2)+1 := by omega
    rw [he,(response_polyak_even q (k/2)).2]
    exact neg_square_pow_le_fourth hq hq1 _ (by omega)

/-- Article: one positive scalar reserve controls every exceptional index. -/
theorem response_reserve {q : ℝ} (hq : 0≤q) (hq1 : q≤1) (k : ℕ) (hk : 1≤k) :
    Source.reserve q≤(1-response 0 (q^2) k)^2 := by
  have hp := response_le_fourth hq hq1 k hk
  have hq4 : q^4≤1 := pow_le_one₀ hq hq1
  unfold Source.reserve
  nlinarith

/-- Article: q≤1/5 supplies strictly more than the planar deficit 99/100. -/
theorem reserve_gt_small_deficit {q : ℝ} (hq : 0≤q) (hq5 : q≤1/5) :
    (99/100 : ℝ)<Source.reserve q := by
  have hfour : q^4≤(1/5 : ℝ)^4 := by gcongr
  unfold Source.reserve
  norm_num at hfour
  nlinarith [sq_nonneg (q^4)]

/-- Article: all repaired initial pairs are positive in the small-q range. -/
theorem small_pair_positive {q : ℝ} (hq : 0≤q) (hq5 : q≤1/5)
    (s d Z : ℂ) (b δ : ℝ) (k : ℕ) (hk : 1≤k)
    (hs : ‖s‖≤1) (hd : ‖d‖≤3/5) (hZ : ‖Z‖≤1/2) (hδ : |δ|=1)
    (hbase : 0≤pairRadius s 0 Z+δ*pairDiscrepancy s 0 Z b) :
    0<pairRadius s d Z+δ*pairDiscrepancy s d Z b+(1-response 0 (q^2) k)^2 := by
  have hl := pair_correction_lower s d Z b δ hbase
  have hp : ‖d‖*(‖s‖+|δ|)*(‖Z‖+1)≤(3/5 : ℝ)*2*(3/2) := by
    rw [hδ]
    gcongr <;> linarith
  have hd2 : Complex.normSq d≤(9/25 : ℝ) := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg d]
  have hr := response_reserve hq (show q≤1 by linarith) k hk
  have hm := reserve_gt_small_deficit hq hq5
  nlinarith

/-- Article: the small-q minimizer pair has a uniform norm reserve as well. -/
theorem small_star_bound (s d : ℂ) {C : ℝ} (hs : ‖s‖≤1) (hd : ‖d‖≤3/5)
    (hC : |C|≤1/2) : |C/4-d.re/2|≤(5-Complex.normSq (s+d))/4 := by
  have hnorm : ‖s+d‖≤(8/5 : ℝ) := (norm_add_le s d).trans (by linarith)
  have hn2 : Complex.normSq (s+d)≤(64/25 : ℝ) := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg (s+d)]
  have hT : |C/4-d.re/2|≤|C|/4+‖d‖/2 := by
    have hre := Complex.abs_re_le_norm d
    calc
      |C/4-d.re/2|≤|C/4|+|d.re/2| := by
        simpa only [Real.norm_eq_abs] using norm_sub_le (C/4) (d.re/2)
      _ = |C|/4+|d.re|/2 := by rw [abs_div,abs_div]; norm_num
      _ ≤ |C|/4+‖d‖/2 := by gcongr
  linarith

end
end polyak.Realization.ExplicitSpiral
