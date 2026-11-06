import nesterov.Quadratic.ScalarRoots
import nesterov.Rates.RootBounds
import polyak.Dynamics.QuadraticLimit

/-!
Article: Lemma `restquad`.
Use: a genuine scalar second-order recurrence has the exact root limsup
when its actual initial impulse cancels no nonzero characteristic root.
The determinant may have either sign and roots may coincide or vanish.
-/

noncomputable section

namespace nesterov.Quadratic

open Filter
open scoped Topology

def ScalarRecurrence (p q : ℝ) (x : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, x (n + 2) = p * x (n + 1) - q * x n

theorem ScalarRecurrence.exists_geometric_bound {p q : ℝ} {x : ℕ → ℝ}
    (hx : ScalarRecurrence p q x) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ n : ℕ, |x n| ≤ C * K ^ n := by
  let C := 1 + |x 0| + |x 1|
  let K := 1 + |p| + |q|
  have hC : 0 < C := by dsimp [C]; positivity
  have hK : 1 ≤ K := by dsimp [K]; linarith [abs_nonneg p, abs_nonneg q]
  have hcoef : |p| * K + |q| ≤ K ^ 2 := by
    dsimp [K]
    nlinarith [abs_nonneg p, abs_nonneg q, mul_nonneg (abs_nonneg p) (abs_nonneg q)]
  refine ⟨C, K, hC, by linarith, ?_⟩
  intro n
  induction n using Nat.twoStepInduction with
  | zero => simp only [pow_zero, mul_one]; dsimp [C]; linarith [abs_nonneg (x 1)]
  | one =>
    have hbase : |x 1| ≤ C := by dsimp [C]; linarith [abs_nonneg (x 0)]
    simpa only [pow_one] using hbase.trans (by nlinarith)
  | more n ih ih1 =>
    rw [hx n]
    calc
      _ ≤ |p * x (n + 1)| + |q * x n| := abs_sub _ _
      _ ≤ |p| * (C * K ^ (n + 1)) + |q| * (C * K ^ n) := by
        rw [abs_mul, abs_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left ih1 (abs_nonneg p))
          (mul_le_mul_of_nonneg_left ih (abs_nonneg q))
      _ = C * (|p| * K + |q|) * K ^ n := by rw [pow_succ]; ring
      _ ≤ C * K ^ 2 * K ^ n := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by linarith) n)
        exact mul_le_mul_of_nonneg_left hcoef hC.le
      _ = _ := by rw [pow_add]; ring

theorem ScalarRecurrence.roots_bounded {p q : ℝ} {x : ℕ → ℝ}
    (hx : ScalarRecurrence p q x) :
    IsBoundedUnder (· ≤ ·) atTop (fun n : ℕ => |x n| ^ ((n : ℝ)⁻¹)) := by
  obtain ⟨C, K, hC, hK, hbound⟩ := hx.exists_geometric_bound
  exact Rates.roots_bounded_of_mul_pow (fun n => abs_nonneg _) hC hK hbound

theorem ScalarRecurrence.scaled_tendsto {p q R : ℝ} {x : ℕ → ℝ}
    (hx : ScalarRecurrence p q x) (hR : polyak.General.rootRadius p q < R) :
    Tendsto (fun n => (x n : ℂ) / (R : ℂ) ^ n) atTop (𝓝 0) := by
  have hR0 : 0 < R := (polyak.General.rootRadius_nonneg p q).trans_lt hR
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hR0
  obtain ⟨r, s, hr, hs, hsum, hprod⟩ := root_pair p q
  have hsmall {z : ℂ} (hz : z ^ 2 - (p : ℂ) * z + (q : ℂ) = 0) : ‖z / (R : ℂ)‖ < 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR0, div_lt_one hR0]
    exact (scalarRoot_norm_le hz).trans_lt hR
  apply polyak.Dynamics.recurrence_tendsto_zero_of_roots _ (r / (R : ℂ)) (s / (R : ℂ))
    (hsmall hr) (hsmall hs)
  intro n
  have hcoef : (r / (R : ℂ)) * (s / (R : ℂ)) = (q : ℂ) / (R : ℂ) ^ 2 := by
    rw [div_mul_div_comm, hprod, pow_two]
  rw [← add_div, hsum, hcoef]
  have hrec : (x (n + 2) : ℂ) = (p : ℂ) * (x (n + 1) : ℂ) - (q : ℂ) * (x n : ℂ) := by
    exact_mod_cast hx n
  rw [pow_add, pow_add]
  norm_num only [pow_one]
  field_simp [hRc]
  linear_combination hrec

theorem ScalarRecurrence.root_limsup_le {p q : ℝ} {x : ℕ → ℝ}
    (hx : ScalarRecurrence p q x) :
    limsup (fun n : ℕ => |x n| ^ ((n : ℝ)⁻¹)) atTop ≤ polyak.General.rootRadius p q := by
  apply le_of_forall_gt_imp_ge_of_dense
  intro R hR
  have hRp : 0 < R := (polyak.General.rootRadius_nonneg p q).trans_lt hR
  have hlim := (hx.scaled_tendsto hR).norm
  simp only [norm_zero] at hlim
  have henv : ∀ᶠ n : ℕ in atTop, |x n| ≤ R ^ n := by
    filter_upwards [hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with n hn
    simp only [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hRp] at hn
    exact ((div_lt_one (pow_pos hRp n)).mp hn).le
  apply limsup_le_of_le (isCoboundedUnder_le_of_le atTop
    (fun n => Real.rpow_nonneg (abs_nonneg (x n)) ((n : ℝ)⁻¹)))
  filter_upwards [henv, eventually_gt_atTop (0 : ℕ)] with n hn hnpos
  exact (Real.rpow_le_rpow (abs_nonneg (x n)) hn (by positivity)).trans_eq
    (Real.pow_rpow_inv_natCast hRp.le (by omega))

theorem ScalarRecurrence.defect {p q b x₀ : ℝ} {x : ℕ → ℝ}
    (hx : ScalarRecurrence p q x) (hzero : x 0 = x₀) (hone : x 1 = (p - b) * x₀)
    {r s : ℂ} (hsum : r + s = (p : ℂ)) (hprod : r * s = (q : ℂ)) (n : ℕ) :
    (x (n + 1) : ℂ) - s * (x n : ℂ) = ((r - (b : ℂ)) * (x₀ : ℂ)) * r ^ n := by
  induction n with
  | zero =>
    rw [hzero, hone]
    push_cast
    simp only [pow_zero, mul_one]
    linear_combination -(x₀ : ℂ) * hsum
  | succ n ih =>
    rw [show n + 1 + 1 = n + 2 by omega, hx n,
      Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_mul]
    rw [hsum.symm, pow_succ]
    linear_combination r * ih + (x n : ℂ) * hprod

theorem ScalarRecurrence.root_limsup_eq {p q b x₀ : ℝ} {x : ℕ → ℝ}
    (hx : ScalarRecurrence p q x) (hzero : x 0 = x₀) (hone : x 1 = (p - b) * x₀)
    (hx₀ : x₀ ≠ 0)
    (hno : ∀ r : ℂ, r ^ 2 - (p : ℂ) * r + (q : ℂ) = 0 → r ≠ 0 → r ≠ (b : ℂ)) :
    limsup (fun n : ℕ => |x n| ^ ((n : ℝ)⁻¹)) atTop = polyak.General.rootRadius p q := by
  apply le_antisymm hx.root_limsup_le
  by_contra h
  have hlt : limsup (fun n : ℕ => |x n| ^ ((n : ℝ)⁻¹)) atTop < polyak.General.rootRadius p q := lt_of_not_ge h
  obtain ⟨R, hrate, hR⟩ := exists_between hlt
  have hRp : 0 < R := (Rates.root_limsup_nonneg (fun n => abs_nonneg _) hx.roots_bounded).trans_lt hrate
  obtain ⟨C, hC, henv⟩ := Rates.exists_mul_pow_of_limsup_root_lt
    (fun n => abs_nonneg (x n)) hx.roots_bounded hRp hrate
  obtain ⟨r, hr, hnorm⟩ := (scalarRootRadius_isGreatest p q).1
  have hrp : 0 < polyak.General.rootRadius p q := hRp.trans hR
  have hr0 : r ≠ 0 := norm_pos_iff.mp (by rwa [← hnorm])
  let s := (p : ℂ) - r
  have hsum : r + s = (p : ℂ) := by dsimp [s]; ring
  have hprod : r * s = (q : ℂ) := by dsimp [s]; linear_combination -hr
  have hA : 0 < ‖(r - (b : ℂ)) * (x₀ : ℂ)‖ := norm_pos_iff.mpr
    (mul_ne_zero (sub_ne_zero.mpr (hno r hr hr0)) (by exact_mod_cast hx₀))
  have hbound (n : ℕ) : ‖(r - (b : ℂ)) * (x₀ : ℂ)‖ * (polyak.General.rootRadius p q) ^ n ≤
      C * (R + ‖s‖) * R ^ n := by
    have hd := hx.defect hzero hone hsum hprod n
    have he : ‖(r - (b : ℂ)) * (x₀ : ℂ)‖ * (polyak.General.rootRadius p q) ^ n =
        ‖(x (n + 1) : ℂ) - s * (x n : ℂ)‖ := by
      rw [hd]
      simp only [norm_mul, norm_pow, ← hnorm]
    rw [he]
    calc
      _ ≤ ‖(x (n + 1) : ℂ)‖ + ‖s * (x n : ℂ)‖ := norm_sub_le _ _
      _ = |x (n + 1)| + ‖s‖ * |x n| := by simp [Complex.norm_real, Real.norm_eq_abs]
      _ ≤ C * R ^ (n + 1) + ‖s‖ * (C * R ^ n) := add_le_add (henv (n + 1))
          (mul_le_mul_of_nonneg_left (henv n) (norm_nonneg s))
      _ = _ := by rw [pow_succ]; ring
  have hlim : Tendsto (fun n : ℕ => C * (R + ‖s‖) * (R / polyak.General.rootRadius p q) ^ n)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (div_nonneg hRp.le hrp.le) ((div_lt_one hrp).mpr hR)).const_mul (C * (R + ‖s‖))
  have hcmp : ∀ᶠ n : ℕ in atTop, ‖(r - (b : ℂ)) * (x₀ : ℂ)‖ ≤
      C * (R + ‖s‖) * (R / polyak.General.rootRadius p q) ^ n := by
    exact Eventually.of_forall fun n => by
      have hh := (le_div_iff₀ (pow_pos hrp n)).mpr (hbound n)
      simpa only [div_pow, mul_div_assoc] using hh
  have hz : ‖(r - (b : ℂ)) * (x₀ : ℂ)‖ ≤ 0 := ge_of_tendsto hlim hcmp
  linarith

end nesterov.Quadratic
