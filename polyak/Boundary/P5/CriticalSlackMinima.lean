import polyak.Boundary.P5.CriticalSlacks
import polyak.Boundary.P5.CriticalDecimalsRoot

/-!
Article: Appendix B, Proposition p5divslack, the four smallest positive
critical first-order slacks and their displayed two-decimal approximations.
Use: exact rational Bernstein bounds are applied to the actual source slacks;
the other finite lags and the analytic tail prove the global ordering.
The source displays s₆⁺ as 11.49..., whereas its exact value is in
(11.488,11.489); 11.49 is its rounding to two decimals, not its prefix.
-/
noncomputable section
namespace polyak.Boundary.P5
open Polynomial Numerics Certificates.P5 LeanCert.Core LeanCert.Engine Spectral

private def qsub (p q : QPoly) : QPoly := p.add ((QPoly.constant (-1)).mul q)

private def tCode : ℕ → QPoly
  | 0 => QPoly.constant 1
  | 1 => QPoly.X
  | n+2 => qsub (((QPoly.constant 2).mul QPoly.X).mul (tCode (n+1))) (tCode n)

private def uCode : ℕ → QPoly
  | 0 => QPoly.constant 1
  | 1 => (QPoly.constant 2).mul QPoly.X
  | n+2 => qsub (((QPoly.constant 2).mul QPoly.X).mul (uCode (n+1))) (uCode n)

private theorem qsub_value (p q : QPoly) (y : ℝ) :
    aeval y (qsub p q).toPoly=aeval y p.toPoly-aeval y q.toPoly := by
  simp [qsub,QPoly.toPoly_add,QPoly.toPoly_mul,sub_eq_add_neg]

private theorem tCode_value (n : ℕ) (y : ℝ) :
    aeval y (tCode n).toPoly=chebT n y := by
  induction n using Nat.twoStepInduction with
  | zero => simp [tCode,chebT]
  | one => simp [tCode,chebT]
  | more n ih ih1 =>
    rw [tCode,qsub_value,Spiral.chebT_recurrence]
    simp only [QPoly.toPoly_mul,QPoly.toPoly_constant,QPoly.toPoly_X,
      map_mul,aeval_C,aeval_X,eq_ratCast,ih,ih1]
    norm_num

private theorem uCode_value (n : ℕ) (y : ℝ) :
    aeval y (uCode n).toPoly=chebU n y := by
  induction n using Nat.twoStepInduction with
  | zero => simp [uCode,chebU]
  | one => simp [uCode,QPoly.toPoly_mul,chebU]
  | more n ih ih1 =>
    rw [uCode,qsub_value,chebU_recurrence]
    simp only [QPoly.toPoly_mul,QPoly.toPoly_constant,QPoly.toPoly_X,
      map_mul,aeval_C,aeval_X,eq_ratCast,ih,ih1]
    norm_num

private def slackCode (n : ℕ) (σ : ℚ) : QPoly :=
  let x2 := QPoly.X.mul QPoly.X
  let Y := (qsub (QPoly.constant (3/4)) x2).mul
      (qsub (QPoly.constant 1) (tCode n)) |>.add
        (((QPoly.constant σ).mul (qsub (QPoly.constant 1) x2)).mul (uCode (n-1)))
  let head := if n%3=0 then
      (QPoly.constant ((n : ℚ)^2/2)).add
        ((QPoly.constant (-σ*n)).mul (BCode.code.add DCode.code))
    else (QPoly.constant ((n : ℚ)^2/2)).add
      (qsub BCode.code ((QPoly.constant 3).mul ACode.code)) |>.add
        ((QPoly.constant (σ*n)).mul (qsub BCode.code DCode.code))
  head.add (PCode.code.mul Y)

private theorem slackCode_value (n : ℕ) (σ : ℚ) :
    aeval y₀ (slackCode n σ).toPoly=firstSlack n σ := by
  unfold slackCode firstSlack criticalY
  split_ifs <;>
    simp only [QPoly.toPoly_add,QPoly.toPoly_mul,QPoly.toPoly_constant,
      QPoly.toPoly_X,map_add,map_mul,aeval_C,aeval_X,qsub_value,tCode_value,uCode_value,
      ACode.exact,BCode.exact,DCode.exact,PCode.exact,
      eq_ratCast,A₀,B₀,D₀,P₀]
  all_goals push_cast; ring

private theorem checked_lower (n : ℕ) (σ a : ℚ)
    (hc : QPoly.bernsteinCheck .strictLower (slackCode n σ) a criticalFineInterval 0=true) :
    (a : ℝ)<firstSlack n σ := by
  have h := QPoly.lt_aeval_of_bernsteinCheck hc y₀ y₀_fine_mem
  rwa [slackCode_value] at h

private theorem checked_upper (n : ℕ) (σ a : ℚ)
    (hc : QPoly.bernsteinCheck .strictUpper (slackCode n σ) a criticalFineInterval 0=true) :
    firstSlack n σ<(a : ℝ) := by
  have h := QPoly.aeval_lt_of_bernsteinCheck hc y₀ y₀_fine_mem
  rwa [slackCode_value] at h

/-- Article: exact enclosures of the four displayed decimal approximations.
The second enclosure records the true prefix 11.488 rather than rounding it. -/
theorem firstSlack_printed_bounds :
    (1122/100 : ℝ)<firstSlack 8 1 ∧ firstSlack 8 1<11225/1000 ∧
    (11488/1000 : ℝ)<firstSlack 6 1 ∧ firstSlack 6 1<11489/1000 ∧
    (1491/100 : ℝ)<firstSlack 3 (-1) ∧ firstSlack 3 (-1)<14915/1000 ∧
    (1840/100 : ℝ)<firstSlack 4 (-1) ∧ firstSlack 4 (-1)<18405/1000 := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · convert checked_lower 8 1 (1122/100) (by decide +kernel) using 1 <;> norm_num
  · convert checked_upper 8 1 (11225/1000) (by decide +kernel) using 1 <;> norm_num
  · convert checked_lower 6 1 (11488/1000) (by decide +kernel) using 1 <;> norm_num
  · convert checked_upper 6 1 (11489/1000) (by decide +kernel) using 1 <;> norm_num
  · convert checked_lower 3 (-1) (1491/100) (by decide +kernel) using 1 <;> norm_num
  · convert checked_upper 3 (-1) (14915/1000) (by decide +kernel) using 1 <;> norm_num
  · convert checked_lower 4 (-1) (1840/100) (by decide +kernel) using 1 <;> norm_num
  · convert checked_upper 4 (-1) (18405/1000) (by decide +kernel) using 1 <;> norm_num

/-- Article: all four displayed values are correct when rounded to two
decimal places, with a strict error below half of one unit in the last place. -/
theorem firstSlack_two_decimal_rounding :
    |firstSlack 8 1-1122/100|<(1/200 : ℝ) ∧
    |firstSlack 6 1-1149/100|<(1/200 : ℝ) ∧
    |firstSlack 3 (-1)-1491/100|<(1/200 : ℝ) ∧
    |firstSlack 4 (-1)-1840/100|<(1/200 : ℝ) := by
  rcases firstSlack_printed_bounds with ⟨h8l,h8u,h6l,h6u,h3l,h3u,h4l,h4u⟩
  refine ⟨abs_lt.mpr ⟨?_,?_⟩,abs_lt.mpr ⟨?_,?_⟩,
    abs_lt.mpr ⟨?_,?_⟩,abs_lt.mpr ⟨?_,?_⟩⟩ <;> linarith

/-- Article: the printed four positive values occur in strictly increasing order. -/
theorem firstSlack_printed_order :
    firstSlack 8 1<firstSlack 6 1 ∧ firstSlack 6 1<firstSlack 3 (-1) ∧
      firstSlack 3 (-1)<firstSlack 4 (-1) := by
  rcases firstSlack_printed_bounds with ⟨h8l,h8u,h6l,h6u,h3l,h3u,h4l,h4u⟩
  exact ⟨by linarith,by linarith,by linarith⟩

/-- Article: the four critical pairs named as the smallest positive first-order slacks. -/
def SmallestCriticalPair (n : ℕ) (σ : ℝ) : Prop :=
  (n=8 ∧ σ=1) ∨ (n=6 ∧ σ=1) ∨ (n=3 ∧ σ= -1) ∨ (n=4 ∧ σ= -1)

/-- Article: beyond the finite prefix, every first-order slack exceeds the
largest of the four printed values, uniformly in the sign and residue class. -/
theorem firstSlack_large_gt_printed {n : ℕ} (hn : 10≤n) {σ : ℝ}
    (hσ : σ= -1 ∨ σ=1) : (1841/100 : ℝ)<firstSlack n σ := by
  have hy := criticalY_lower n (by omega) σ hσ
  have hpy : -(129/100 : ℝ)<P₀*criticalY n σ y₀ := by
    have hp := mul_le_mul_of_nonneg_left hy P₀_bounds.1.le
    nlinarith [P₀_bounds.2]
  have hnR : (10 : ℝ)≤n := by exact_mod_cast hn
  have hn0 : (0 : ℝ)≤n := Nat.cast_nonneg n
  have hpoly : (1841/100 : ℝ)<(n : ℝ)^2/2-(237/100 : ℝ)*n-181/100-129/100 := by
    nlinarith [sq_nonneg ((n : ℝ)-10)]
  have hBD : -(237/100 : ℝ)<B₀+D₀ ∧ B₀+D₀<237/100 := by
    constructor <;> linarith [B₀_fine_bounds.1,B₀_fine_bounds.2,D₀_fine_bounds.1,D₀_fine_bounds.2]
  have hBD' : -(237/100 : ℝ)<B₀-D₀ ∧ B₀-D₀<237/100 := by
    constructor <;> linarith [B₀_fine_bounds.1,B₀_fine_bounds.2,D₀_fine_bounds.1,D₀_fine_bounds.2]
  have hBA : -(181/100 : ℝ)<B₀-3*A₀ := by
    linarith [B₀_fine_bounds.1,A₀_fine_bounds.2]
  have h₁ := mul_nonneg hn0 (show 0≤B₀+D₀+237/100 by linarith [hBD.1])
  have h₂ := mul_nonneg hn0 (show 0≤237/100-(B₀+D₀) by linarith [hBD.2])
  have h₃ := mul_nonneg hn0 (show 0≤B₀-D₀+237/100 by linarith [hBD'.1])
  have h₄ := mul_nonneg hn0 (show 0≤237/100-(B₀-D₀) by linarith [hBD'.2])
  unfold firstSlack
  split_ifs <;> rcases hσ with rfl | rfl <;> nlinarith

/-- Article: the finite critical pairs outside the four named ones also
exceed 18.41; each check is exact rational polynomial arithmetic. -/
theorem firstSlack_other_small_gt_printed {n : ℕ} (hn : 1≤n) (hN : n<10) {σ : ℝ}
    (hc : CriticalPair n σ) (ha : ¬ActivePair n σ) (hs : ¬SmallestCriticalPair n σ) :
    (1841/100 : ℝ)<firstSlack n σ := by
  rcases hc.1 with rfl | rfl
  · have hcases : n=6 ∨ n=7 ∨ n=9 := by
      norm_num [CriticalPair,ActivePair,SmallestCriticalPair] at hc ha hs
      omega
    rcases hcases with rfl | rfl | rfl
    · convert checked_lower 6 (-1) (1841/100) (by decide +kernel) using 1 <;> norm_num
    · convert checked_lower 7 (-1) (1841/100) (by decide +kernel) using 1 <;> norm_num
    · convert checked_lower 9 (-1) (1841/100) (by decide +kernel) using 1 <;> norm_num
  · have heq : n=9 := by
      norm_num [CriticalPair,ActivePair,SmallestCriticalPair] at hc ha hs
      omega
    subst n
    convert checked_lower 9 1 (1841/100) (by decide +kernel) using 1 <;> norm_num

/-- Article: these are the four smallest positive critical first-order values,
not merely four examples; every other nonactive critical pair is larger. -/
theorem firstSlack_other_gt_fourth {n : ℕ} (hn : 1≤n) {σ : ℝ}
    (hc : CriticalPair n σ) (ha : ¬ActivePair n σ) (hs : ¬SmallestCriticalPair n σ) :
    firstSlack 4 (-1)<firstSlack n σ := by
  have hu : firstSlack 4 (-1)<(1841/100 : ℝ) := by
    linarith [firstSlack_printed_bounds.2.2.2.2.2.2.2]
  apply hu.trans
  by_cases hN : n<10
  · exact firstSlack_other_small_gt_printed hn hN hc ha hs
  · exact firstSlack_large_gt_printed (by omega) hc.1

/-- Article: the positive critical values at or below the fourth one are
exactly the four named pairs; this also excludes all active zeros. -/
theorem firstSlack_smallest_four_iff {n : ℕ} (hn : 1≤n) {σ : ℝ}
    (hc : CriticalPair n σ) :
    (0<firstSlack n σ ∧ firstSlack n σ≤firstSlack 4 (-1)) ↔ SmallestCriticalPair n σ := by
  constructor
  · intro h
    by_contra hs
    have ha : ¬ActivePair n σ := by
      intro ha
      have hz := (firstSlack_eq_zero_iff hn hc).mpr ha
      exact (ne_of_gt h.1) hz
    exact (not_lt_of_ge h.2) (firstSlack_other_gt_fourth hn hc ha hs)
  · intro hs
    have h8 := firstSlack_printed_bounds.1
    have h6 := firstSlack_printed_bounds.2.2.1
    have h3 := firstSlack_printed_bounds.2.2.2.2.1
    have h4 := firstSlack_printed_bounds.2.2.2.2.2.2.1
    rcases firstSlack_printed_order with ⟨h86,h63,h34⟩
    rcases hs with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨by linarith,(h86.trans (h63.trans h34)).le⟩
    · exact ⟨by linarith,(h63.trans h34).le⟩
    · exact ⟨by linarith,h34.le⟩
    · exact ⟨by linarith,le_rfl⟩

end polyak.Boundary.P5
