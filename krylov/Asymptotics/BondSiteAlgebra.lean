import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
Article: main_krylov, upper bound in thm:limit, bond/site cancellation.
Use: sum the actual top-impedance decomposition without losing the unused
nonnegative initial term. The scalar pair estimate is `log x≤x−1` applied
to the two reciprocal coefficients; this is equivalent to the source's
AM--GM followed by `sqrt z≥1+log z/2`.
Source: elementary logarithmic concavity and finite summation.
-/
namespace krylov.Asymptotics
noncomputable section
open Real Finset
open scoped BigOperators

/-- Two positive reciprocal coefficients dominate their exact logarithmic
product, including when that logarithm is negative. -/
theorem reciprocal_pair_log {A I c : ℝ} (hA : 0 < A) (hI : 0 < I) (hc : 0 < c) :
    2 + log (A * I) ≤ A / c + I * c := by
  have h₁ := Real.log_le_sub_one_of_pos (div_pos hA hc)
  have h₂ := Real.log_le_sub_one_of_pos (mul_pos hI hc)
  have he : log (A / c) + log (I * c) = log (A * I) := by
    rw [log_div hA.ne' hc.ne', log_mul hI.ne' hc.ne', log_mul hA.ne' hI.ne']
    ring
  linarith

/-- Unequal weights may both be decreased before applying the pair estimate;
positivity of the original coefficients keeps this valid for negative logs. -/
theorem weighted_reciprocal_pair_log {A I c w z g : ℝ}
    (hA : 0 < A) (hI : 0 < I) (hc : 0 < c) (hg : 0 ≤ g)
    (hgw : g ≤ w) (hgz : g ≤ z) :
    g * (2 + log (A * I)) ≤ w * A / c + z * I * c := by
  have hlog := mul_le_mul_of_nonneg_left (reciprocal_pair_log hA hI hc) hg
  have h₁ := mul_nonneg (sub_nonneg.mpr hgw) (div_nonneg hA.le hc.le)
  have h₂ := mul_nonneg (sub_nonneg.mpr hgz) (mul_nonneg hI.le hc.le)
  ring_nf at hlog h₁ h₂ ⊢
  linarith

/-- Exact finite reindexing of top-impedance budget into an initial term,
all bonds, and all internal sites. -/
theorem bond_site_decomposition (n : ℕ) (x b y c : ℕ → ℝ) :
    (∑ j ∈ range (n + 1), (x j + b j + y j *
      (if j + 1 < n + 1 then c (j + 1) else 0))) =
      x 0 + (∑ j ∈ range (n + 1), b j) +
        ∑ j ∈ range n, (x (j + 1) + y j * c (j + 1)) := by
  rw [sum_add_distrib, sum_add_distrib]
  have hx : (∑ j ∈ range (n + 1), x j) = x 0 + ∑ j ∈ range n, x (j + 1) := by
    rw [sum_range_succ']
    ring
  have hy : (∑ j ∈ range (n + 1), y j * (if j + 1 < n + 1 then c (j + 1) else 0)) =
      ∑ j ∈ range n, y j * c (j + 1) := by
    rw [sum_range_succ]
    simp only [lt_self_iff_false, ite_false, mul_zero, add_zero]
    apply sum_congr rfl
    intro j hj
    rw [ite_eq_left (by have := mem_range.mp hj; omega)]
  rw [hx, hy, sum_add_distrib]
  ring

/-- The exact top-impedance pairing inequality, with no endpoint loss.
`mass j` denotes the next physical mass; its final inequality may be strict. -/
theorem bond_site_sum_lower (n : ℕ) {w g A I c d gap mass : ℕ → ℝ} {T : ℝ}
    (hA : ∀ j < n + 1, 0 < A j) (hI : ∀ j < n + 1, 0 < I j)
    (hc : ∀ j < n + 1, 0 < c j) (hd : ∀ j < n + 1, 0 < d j)
    (hg : ∀ j < n + 1, 0 ≤ g j) (hgw : ∀ j < n + 1, g j ≤ w j)
    (hdec : ∀ j < n, g (j + 1) ≤ g j)
    (hgap : ∀ j < n + 1, T * gap j = 1 / c j + 1 / d j)
    (hmass : ∀ j < n + 1,
      d j + (if j + 1 < n + 1 then c (j + 1) else 0) ≤ T * mass j) :
    (∑ j ∈ range (n + 1), g j * (2 + log (A j * I j))) +
      (∑ j ∈ range n, g (j + 1) * (2 + log (A (j + 1) * I j))) ≤
      T * ∑ j ∈ range (n + 1), (w j * A j * gap j + g j * I j * mass j) := by
  have hlocal (j : ℕ) (hj : j < n + 1) :
      w j * A j / c j + (w j * A j / d j + g j * I j * d j) +
        (g j * I j) * (if j + 1 < n + 1 then c (j + 1) else 0) ≤
      T * (w j * A j * gap j + g j * I j * mass j) := by
    have hl := congrArg (fun x : ℝ ↦ w j * A j * x) (hgap j hj)
    have hm := mul_le_mul_of_nonneg_left (hmass j hj) (mul_nonneg (hg j hj) (hI j hj).le)
    ring_nf at hl hm ⊢
    linarith only [hl, hm]
  have hbudget := sum_le_sum (fun j hj ↦ hlocal j (mem_range.mp hj))
  rw [← mul_sum] at hbudget
  have hdecomp := bond_site_decomposition n (fun j ↦ w j * A j / c j)
    (fun j ↦ w j * A j / d j + g j * I j * d j) (fun j ↦ g j * I j) c
  rw [hdecomp] at hbudget
  have hbond : (∑ j ∈ range (n + 1), g j * (2 + log (A j * I j))) ≤
      ∑ j ∈ range (n + 1), (w j * A j / d j + g j * I j * d j) := by
    apply sum_le_sum
    intro j hj
    have hj' := mem_range.mp hj
    exact weighted_reciprocal_pair_log (hA j hj') (hI j hj') (hd j hj')
      (hg j hj') (hgw j hj') le_rfl
  have hsite : (∑ j ∈ range n, g (j + 1) * (2 + log (A (j + 1) * I j))) ≤
      ∑ j ∈ range n, (w (j + 1) * A (j + 1) / c (j + 1) + g j * I j * c (j + 1)) := by
    apply sum_le_sum
    intro j hj
    have hj' := mem_range.mp hj
    exact weighted_reciprocal_pair_log (hA (j + 1) (by omega)) (hI j (by omega))
      (hc (j + 1) (by omega)) (hg (j + 1) (by omega)) (hgw (j + 1) (by omega))
      (hdec j hj')
  have hinit : 0 ≤ w 0 * A 0 / c 0 := by
    exact div_nonneg (mul_nonneg ((hg 0 (by omega)).trans (hgw 0 (by omega)))
      (hA 0 (by omega)).le) (hc 0 (by omega)).le
  linarith only [hbudget, hbond, hsite, hinit]

/-- Summing the logarithmic bond/site estimates gives exactly the printed
bracket; the omitted initial drift term has a nonnegative sign. -/
theorem log_pair_bracket (n : ℕ) {g δ k q A I : ℕ → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hg : ∀ j < n + 1, 0 ≤ g j) (hδ : 0 ≤ δ 0)
    (hbond : ∀ j < n + 1, -B * k j - (1 - B) * q j ≤ log (A j * I j))
    (hsite : ∀ j < n, -(1 + B) * δ (j + 1) ≤ log (A (j + 1) * I j)) :
    4 * (∑ j ∈ range (n + 1), g j) - 2 * g 0 -
      ((1 + B) * (∑ j ∈ range (n + 1), g j * δ j) +
        B * (∑ j ∈ range (n + 1), g j * k j) +
        (1 - B) * (∑ j ∈ range (n + 1), g j * q j)) ≤
    (∑ j ∈ range (n + 1), g j * (2 + log (A j * I j))) +
      ∑ j ∈ range n, g (j + 1) * (2 + log (A (j + 1) * I j)) := by
  have hb : 2 * (∑ j ∈ range (n + 1), g j) -
      B * (∑ j ∈ range (n + 1), g j * k j) -
      (1 - B) * (∑ j ∈ range (n + 1), g j * q j) ≤
      ∑ j ∈ range (n + 1), g j * (2 + log (A j * I j)) := by
    calc
      _ = ∑ j ∈ range (n + 1), g j * (2 + (-B * k j - (1 - B) * q j)) := by
        simp only [mul_sum]
        rw [← sum_sub_distrib, ← sum_sub_distrib]
        apply sum_congr rfl
        intro j _
        ring
      _ ≤ _ := by
        apply sum_le_sum
        intro j hj
        apply mul_le_mul_of_nonneg_left _ (hg j (mem_range.mp hj))
        linarith only [hbond j (mem_range.mp hj)]
  have hs : 2 * (∑ j ∈ range n, g (j + 1)) -
      (1 + B) * (∑ j ∈ range n, g (j + 1) * δ (j + 1)) ≤
      ∑ j ∈ range n, g (j + 1) * (2 + log (A (j + 1) * I j)) := by
    calc
      _ = ∑ j ∈ range n, g (j + 1) * (2 + (-(1 + B) * δ (j + 1))) := by
        simp only [mul_sum]
        rw [← sum_sub_distrib]
        apply sum_congr rfl
        intro j _
        ring
      _ ≤ _ := by
        apply sum_le_sum
        intro j hj
        apply mul_le_mul_of_nonneg_left _ (hg (j + 1) (by have := mem_range.mp hj; omega))
        linarith only [hsite j (mem_range.mp hj)]
  have hS := sum_range_succ' g n
  have hD := sum_range_succ' (fun j ↦ g j * δ j) n
  have hinit : 0 ≤ (1 + B) * g 0 * δ 0 :=
    mul_nonneg (mul_nonneg (by linarith) (hg 0 (by omega))) hδ
  rw [hS] at hb
  rw [hS, hD]
  nlinarith only [hb, hs, hinit]

end
end krylov.Asymptotics
