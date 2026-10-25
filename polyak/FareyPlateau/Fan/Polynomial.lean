import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.Topology.Order.Compact

/-! The universal trigonometric fan polynomial, for every integer period.
Its sign is an analytic theorem, with no finite-period computation. -/
noncomputable section
namespace polyak.FareyPlateau.Fan
open Set Filter
open scoped Topology

def objective (m : ℕ) (x : ℝ) : ℝ := (m : ℝ) * Real.cos x - Real.cos ((m : ℝ) * x)

theorem objective_deriv (m : ℕ) (x : ℝ) :
    HasDerivAt (objective m) ((m : ℝ) * (Real.sin ((m : ℝ) * x) - Real.sin x)) x := by
  convert ((Real.hasDerivAt_cos x).const_mul (m : ℝ)).sub
    (((hasDerivAt_id x).const_mul (m : ℝ)).cos) using 1 <;> first | rfl | (simp only [id_eq]; ring)

theorem objective_period (m : ℕ) (x : ℝ) (l : ℤ) :
    objective m (x + l * (2 * Real.pi)) = objective m x := by
  unfold objective
  rw [Real.cos_add_int_mul_two_pi]
  have he : (m : ℝ) * (x + l * (2 * Real.pi)) =
      (m : ℝ) * x + ((m : ℤ) * l : ℤ) * (2 * Real.pi) := by push_cast; ring
  rw [he, Real.cos_add_int_mul_two_pi]

theorem base_gap {m : ℕ} (hm : 2 ≤ m) :
    (m : ℝ) - 1 < ((m : ℝ) + 1) * Real.cos (Real.pi / ((m : ℝ) + 1)) := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hl := Real.one_sub_sq_div_two_le_cos (x := Real.pi / ((m : ℝ) + 1))
  have hmul := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ (m : ℝ) + 1)
  have hπ : Real.pi^2 < 12 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hden : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hsmall : Real.pi^2 < 4 * ((m : ℝ) + 1) := by linarith
  have hid : ((m : ℝ) + 1) * (1 - (Real.pi / ((m : ℝ) + 1))^2 / 2) =
      ((m : ℝ) + 1) - Real.pi^2 / (2 * ((m : ℝ) + 1)) := by field_simp
  rw [hid] at hmul
  have hquot : Real.pi^2 / (2 * ((m : ℝ) + 1)) < 2 :=
    (div_lt_iff₀ (by positivity)).mpr (by nlinarith)
  linarith

theorem stationary_bound {m : ℕ} (hm : 2 ≤ m) {x : ℝ}
    (hx : x ∈ Icc (-Real.pi) Real.pi)
    (hstat : Real.sin ((m : ℝ) * x) = Real.sin x) :
    objective m x ≤ ((m : ℝ) + 1) * Real.cos (Real.pi / ((m : ℝ) + 1)) := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  obtain ⟨l, he | he⟩ := Real.sin_eq_sin_iff.mp hstat
  · have hcos : Real.cos ((m : ℝ) * x) = Real.cos x := by
      have he' : (m : ℝ) * x = x + (-l : ℤ) * (2 * Real.pi) := by push_cast; linarith
      rw [he', Real.cos_add_int_mul_two_pi]
    unfold objective
    rw [hcos]
    have hupper := mul_le_mul_of_nonneg_left (Real.cos_le_one x)
      (show (0 : ℝ) ≤ (m : ℝ) - 1 by linarith)
    have hgap := base_gap hm
    nlinarith only [hupper, hgap]
  · have he' : (m : ℝ) * x = (l : ℝ) * (2 * Real.pi) + (Real.pi - x) := by linarith
    have hcos : Real.cos ((m : ℝ) * x) = -Real.cos x := by
      rw [he', add_comm, Real.cos_add_int_mul_two_pi, Real.cos_pi_sub]
    have habs : Real.pi / ((m : ℝ) + 1) ≤ |x| := by
      have hl : l ≤ -1 ∨ 0 ≤ l := by omega
      rcases hl with hl | hl
      · have hlR : (l : ℝ) ≤ -1 := by exact_mod_cast hl
        have hneg : x ≤ -Real.pi / ((m : ℝ) + 1) := by
          apply (le_div_iff₀ (by positivity)).mpr
          have hp := mul_le_mul_of_nonneg_right hlR Real.pi_pos.le
          linarith
        have hxa : -x ≤ |x| := neg_le_abs x
        simp only [neg_div] at hneg
        linarith
      · have hlR : (0 : ℝ) ≤ l := by exact_mod_cast hl
        have hpos : Real.pi / ((m : ℝ) + 1) ≤ x := by
          apply (div_le_iff₀ (by positivity)).mpr
          have hp := mul_nonneg hlR Real.pi_pos.le
          linarith
        exact hpos.trans (le_abs_self x)
    have habspi : |x| ≤ Real.pi := abs_le.mpr hx
    have hcc := Real.cos_le_cos_of_nonneg_of_le_pi
      (show 0 ≤ Real.pi / ((m : ℝ) + 1) by positivity) habspi habs
    rw [Real.cos_abs] at hcc
    unfold objective
    rw [hcos]
    nlinarith only [mul_le_mul_of_nonneg_left hcc (show (0 : ℝ) ≤ (m : ℝ) + 1 by positivity)]

theorem objective_bound_interval {m : ℕ} (hm : 2 ≤ m) {x : ℝ}
    (hx : x ∈ Icc (-Real.pi) Real.pi) :
    objective m x ≤ ((m : ℝ) + 1) * Real.cos (Real.pi / ((m : ℝ) + 1)) := by
  have hc : Continuous (objective m) := by unfold objective; fun_prop
  obtain ⟨y, hy, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (-Real.pi) Real.pi).Nonempty from ⟨0, by constructor <;> linarith [Real.pi_pos]⟩)
    hc.continuousOn
  apply (hmax hx).trans
  by_cases hleft : y = -Real.pi
  · unfold objective
    rw [hleft, Real.cos_neg, Real.cos_pi]
    have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
    have hl := Real.neg_one_le_cos ((m : ℝ) * -Real.pi)
    have hg := base_gap hm
    nlinarith only [hl, hg, hmR]
  by_cases hright : y = Real.pi
  · unfold objective
    rw [hright, Real.cos_pi]
    have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
    have hl := Real.neg_one_le_cos ((m : ℝ) * Real.pi)
    have hg := base_gap hm
    nlinarith only [hl, hg, hmR]
  have hi : y ∈ Ioo (-Real.pi) Real.pi := ⟨lt_of_le_of_ne hy.1 (Ne.symm hleft),
    lt_of_le_of_ne hy.2 hright⟩
  have hder := (hmax.isLocalMax (Icc_mem_nhds hi.1 hi.2)).deriv_eq_zero
  rw [(objective_deriv m y).deriv] at hder
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hstat : Real.sin ((m : ℝ) * y) = Real.sin y := by
    have := (mul_eq_zero.mp hder).resolve_left hmpos.ne'
    linarith
  exact stationary_bound hm hy hstat

theorem objective_bound {m : ℕ} (hm : 2 ≤ m) (x : ℝ) :
    objective m x ≤ ((m : ℝ) + 1) * Real.cos (Real.pi / ((m : ℝ) + 1)) := by
  let y := toIcoMod (by positivity : 0 < 2 * Real.pi) (-Real.pi) x
  have hy := toIcoMod_mem_Ico (by positivity : 0 < 2 * Real.pi) (-Real.pi) x
  have hxy := toIcoMod_add_toIcoDiv_zsmul (by positivity : 0 < 2 * Real.pi) (-Real.pi) x
  have he : x = y + (toIcoDiv (by positivity : 0 < 2 * Real.pi) (-Real.pi) x : ℤ) * (2 * Real.pi) := by
    simpa only [zsmul_eq_mul] using hxy.symm
  rw [he, objective_period]
  exact objective_bound_interval hm ⟨hy.1, by linarith [hy.2]⟩

theorem objective_at_root {m : ℕ} (hm : 2 ≤ m) :
    objective m (Real.pi / ((m : ℝ) + 1)) =
      ((m : ℝ) + 1) * Real.cos (Real.pi / ((m : ℝ) + 1)) := by
  have he : (m : ℝ) * (Real.pi / ((m : ℝ) + 1)) =
      Real.pi - Real.pi / ((m : ℝ) + 1) := by field_simp; ring
  unfold objective
  rw [he, Real.cos_pi_sub]
  ring

theorem objective_even (m : ℕ) (x : ℝ) : objective m (-x) = objective m x := by
  simp only [objective, mul_neg, Real.cos_neg]

theorem objective_eq_iff {m : ℕ} (hm : 2 ≤ m) (x : ℝ) :
    objective m x = ((m : ℝ) + 1) * Real.cos (Real.pi / ((m : ℝ) + 1)) ↔
      ∃ l : ℤ, x = Real.pi / ((m : ℝ) + 1) + l * (2 * Real.pi) ∨
        x = -(Real.pi / ((m : ℝ) + 1)) + l * (2 * Real.pi) := by
  constructor
  · intro heq
    have hmax : IsMaxOn (objective m) univ x := by
      intro y _
      rw [heq]
      exact objective_bound hm y
    have hd := (hmax.isLocalMax (by simp)).deriv_eq_zero
    rw [(objective_deriv m x).deriv] at hd
    have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
    have hs : Real.sin ((m : ℝ) * x) = Real.sin x := by
      have hh := (mul_eq_zero.mp hd).resolve_left (by positivity : (m : ℝ) ≠ 0)
      linarith
    have hcos : Real.cos x = Real.cos (Real.pi / ((m : ℝ) + 1)) := by
      obtain ⟨l, he | he⟩ := Real.sin_eq_sin_iff.mp hs
      · have he' : (m : ℝ) * x = x + (-l : ℤ) * (2 * Real.pi) := by push_cast; linarith
        unfold objective at heq
        rw [he', Real.cos_add_int_mul_two_pi] at heq
        have hupper := mul_le_mul_of_nonneg_left (Real.cos_le_one x)
          (show (0 : ℝ) ≤ (m : ℝ) - 1 by linarith)
        have hgap := base_gap hm
        nlinarith only [hupper, hgap, heq]
      · have he' : (m : ℝ) * x = (Real.pi - x) + (l : ℝ) * (2 * Real.pi) := by linarith
        unfold objective at heq
        rw [he', Real.cos_add_int_mul_two_pi, Real.cos_pi_sub] at heq
        nlinarith only [heq, hmR]
    obtain ⟨l, he | he⟩ := Real.cos_eq_cos_iff.mp hcos
    · refine ⟨-l, Or.inl ?_⟩
      push_cast
      linarith
    · refine ⟨l, Or.inr ?_⟩
      linarith
  · rintro ⟨l, he | he⟩
    · rw [he, objective_period]
      exact objective_at_root hm
    · rw [he, objective_period, objective_even]
      exact objective_at_root hm

def polynomial (k : ℕ) (θ : ℝ) : ℝ :=
  (k : ℝ) * Real.cos (Real.pi / k) - ((k : ℝ) - 1) * Real.cos (θ - Real.pi / k) -
    Real.cos (((k : ℝ) - 1) * θ + Real.pi / k)

theorem polynomial_nonneg {k : ℕ} (hk : 3 ≤ k) (θ : ℝ) : 0 ≤ polynomial k θ := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hm : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hc : ((k : ℝ) - 1) * θ + Real.pi / k =
      ((k : ℝ) - 1) * (θ - Real.pi / k) + Real.pi := by field_simp; ring
  have hh := objective_bound (show 2 ≤ k - 1 by omega) (θ - Real.pi / k)
  simp only [objective, hm, sub_add_cancel] at hh
  unfold polynomial
  rw [hc, Real.cos_add_pi]
  linarith

theorem polynomial_eq_zero_iff {k : ℕ} (hk : 3 ≤ k) (θ : ℝ) :
    polynomial k θ = 0 ↔ ∃ l : ℤ,
      θ = l * (2 * Real.pi) ∨ θ = 2 * Real.pi / k + l * (2 * Real.pi) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hm : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hc : ((k : ℝ) - 1) * θ + Real.pi / k =
      ((k : ℝ) - 1) * (θ - Real.pi / k) + Real.pi := by field_simp; ring
  have he : polynomial k θ = (k : ℝ) * Real.cos (Real.pi / k) -
      objective (k - 1) (θ - Real.pi / k) := by
    unfold polynomial objective
    rw [hm, hc, Real.cos_add_pi]
    ring
  rw [he, sub_eq_zero, eq_comm]
  have hh := objective_eq_iff (show 2 ≤ k - 1 by omega) (θ - Real.pi / k)
  simp only [hm, sub_add_cancel] at hh
  rw [hh]
  constructor
  · rintro ⟨l, hl | hl⟩
    · exact ⟨l, Or.inr (by linear_combination hl)⟩
    · exact ⟨l, Or.inl (by linarith)⟩
  · rintro ⟨l, hl | hl⟩
    · exact ⟨l, Or.inr (by linarith)⟩
    · exact ⟨l, Or.inl (by linear_combination hl)⟩

end polyak.FareyPlateau.Fan
