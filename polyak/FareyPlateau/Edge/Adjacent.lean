import polyak.FareyPlateau.Edge.Persistence
import polyak.FareyPlateau.Edge.Jets
import polyak.ModeLocking.TwoLag.Extension
import polyak.ModeLocking.Regular.Endpoints

/-! The actual adjacent-lag edge symbol of Definition edgesymbol and its
complete sufficient regularity criterion. -/
noncomputable section
namespace polyak.FareyPlateau.Edge
open General Levels ModeLocking Set
open scoped BigOperators

structure AdjacentData (q : Tuning) (j k : ℕ) where
  period_ge : 3 ≤ k
  numerator_pos : 1 ≤ j
  numerator_lt : 2 * j < k
  inverse : ℤ
  inverse_pos : 0 < inverse
  inverse_lt : inverse < k
  inverse_mod : inverse * (j : ℤ) ≡ 1 [ZMOD (k : ℤ)]
  lower : ℤ
  lower_class : lower % (k : ℤ) = inverse
  mix : ℝ
  mix_pos : 0 < mix
  mix_lt : mix < 1
  slope : 2 * deriv (TwoLag.phase q (shift q k (atom j k (by omega) numerator_lt.le)))
    (atom j k (by omega) numerator_lt.le : ℝ) = (lower : ℝ) + mix * k

namespace AdjacentData
variable {q : Tuning} {j k : ℕ} (A : AdjacentData q j k)

def frequency : Frequency := atom j k (by have := A.period_ge; omega) A.numerator_lt.le
def edgeShift : ℝ := shift q k A.frequency
def upper : ℤ := A.lower + k
def function : ℝ → ℝ := symbol (TwoLag.phase q A.edgeShift) A.lower A.upper A.mix
def lags : Finset ℤ := {A.lower, A.upper}
def weight (n : ℤ) : ℝ := if n = A.lower then 1 - A.mix else A.mix

theorem lower_ne_upper : A.lower ≠ A.upper := by
  unfold upper
  have := A.period_ge
  omega

theorem lower_nonzero : A.lower ≠ 0 := by
  intro h
  have hh := A.lower_class
  rw [h, Int.zero_emod] at hh
  have := A.inverse_pos
  omega

theorem upper_class : A.upper % (k : ℤ) = A.inverse := by
  unfold upper
  rw [Int.add_emod_right, A.lower_class]

theorem upper_nonzero : A.upper ≠ 0 := by
  intro h
  have hh := A.upper_class
  rw [h, Int.zero_emod] at hh
  have := A.inverse_pos
  omega

theorem phase_value : TwoLag.phase q A.edgeShift A.frequency = Real.pi / k := by
  rw [TwoLag.phase, Geometry.jointAngle_actual q A.edgeShift A.frequency.property]
  exact phase_at_shift q A.period_ge
    ⟨atom_pos A.numerator_pos (by have := A.period_ge; omega) A.numerator_lt.le,
      atom_lt_pi (by have := A.period_ge; omega) A.numerator_lt⟩

theorem residue (n : ℤ) (hn : n ∈ A.lags) : (n * j) % k = 1 := by
  have hclass : n % (k : ℤ) = A.inverse := by
    simp only [lags, Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl
    · exact A.lower_class
    · exact A.upper_class
  have he : (n * j) % k = (A.inverse * j) % k := by
    conv_lhs => rw [Int.mul_emod, hclass]
    conv_rhs => rw [Int.mul_emod, Int.emod_eq_of_lt A.inverse_pos.le A.inverse_lt]
  rw [he]
  simpa only [Int.ModEq, Int.emod_eq_of_lt
    (by have := A.period_ge; omega : (0 : ℤ) ≤ 1)
    (by have := A.period_ge; omega : (1 : ℤ) < k)] using A.inverse_mod

theorem lag_trig (n : ℤ) (hn : n ∈ A.lags) :
    Real.sin ((n : ℝ) * (A.frequency : ℝ) - TwoLag.phase q A.edgeShift A.frequency) = Real.sin (Real.pi / k) ∧
    Real.cos ((n : ℝ) * (A.frequency : ℝ) - TwoLag.phase q A.edgeShift A.frequency) = Real.cos (Real.pi / k) := by
  rw [A.phase_value]
  have ht := lag_trig_reduce (by have := A.period_ge; omega) A.numerator_lt.le n (Real.pi / k)
  have he : 2 * Real.pi * (((n * j) % k : ℤ) : ℝ) / k - Real.pi / k = Real.pi / k := by
    rw [A.residue n hn]
    push_cast
    ring
  exact ⟨ht.2.trans (congrArg Real.sin he), ht.1.trans (congrArg Real.cos he)⟩

theorem second : deriv^[2] A.function A.frequency =
    Real.sin (Real.pi / k) * deriv^[2] (TwoLag.phase q A.edgeShift) A.frequency -
      (1 / 2 : ℝ) * Real.cos (Real.pi / k) * (k : ℝ)^2 * A.mix * (1 - A.mix) := by
  apply symbol_second (TwoLag.analyticAt_phase q A.edgeShift A.frequency.property) A.phase_value
    (by simp only [upper, Int.cast_add, Int.cast_natCast]) A.slope
  · exact fun n hn => (A.lag_trig n hn).1
  · exact fun n hn => (A.lag_trig n hn).2

theorem value_zero : A.function A.frequency = 0 := by
  change -(1 / 2 : ℝ) * ((1 - A.mix) *
    (Real.cos (TwoLag.phase q A.edgeShift A.frequency) -
      Real.cos ((A.lower : ℝ) * (A.frequency : ℝ) - TwoLag.phase q A.edgeShift A.frequency)) +
    A.mix * (Real.cos (TwoLag.phase q A.edgeShift A.frequency) -
      Real.cos ((A.upper : ℝ) * (A.frequency : ℝ) - TwoLag.phase q A.edgeShift A.frequency))) = 0
  rw [(A.lag_trig A.lower (by simp [lags])).2,
    (A.lag_trig A.upper (by simp [lags])).2, A.phase_value]
  ring

theorem first : deriv A.function A.frequency = 0 := by
  apply symbol_first (TwoLag.analyticAt_phase q A.edgeShift A.frequency.property) A.phase_value
    (by simp only [upper, Int.cast_add, Int.cast_natCast]) A.slope
  exact fun n hn => (A.lag_trig n hn).1

theorem endpoint_zero : A.function 0 = 0 := by
  have hp : TwoLag.phase q A.edgeShift 0 = Real.pi := by
    rw [TwoLag.phase, Geometry.jointAngle_actual q A.edgeShift ⟨le_rfl, Real.pi_pos.le⟩,
      Geometry.shiftedAngle_zero]
  simp only [function, symbol, Geometry.extendedLag, hp, mul_zero, zero_sub,
    Real.cos_neg, sub_self, mul_zero, add_zero]

theorem finiteSymbol_eq : finiteSymbol q A.edgeShift A.lags A.weight = fun x => -2 * A.function x := by
  funext x
  simp only [finiteSymbol, lags, Finset.sum_pair A.lower_ne_upper, weight,
    ite_true, ite_eq_right A.lower_ne_upper.symm]
  unfold function symbol lagExtension TwoLag.phase
  ring

theorem finiteSymbol_second (x : ℝ) :
    deriv^[2] (finiteSymbol q A.edgeShift A.lags A.weight) x = -2 * deriv^[2] A.function x := by
  rw [A.finiteSymbol_eq, ← iteratedDeriv_eq_iterate, iteratedDeriv_const_mul_field,
    iteratedDeriv_eq_iterate]

theorem endpoint_first : deriv A.function 0 = 0 := by
  have he := finiteSymbol_deriv_zero q A.edgeShift A.lags A.weight
  rw [A.finiteSymbol_eq, deriv_const_mul_field] at he
  linarith

theorem endpoint_second : deriv^[2] A.function 0 = (1 / 2 : ℝ) *
    ((1 - A.mix) * (A.lower : ℝ) * ((A.lower : ℝ) + 2 * Geometry.tau q) +
      A.mix * (A.upper : ℝ) * ((A.upper : ℝ) + 2 * Geometry.tau q)) := by
  have he := A.finiteSymbol_second 0
  rw [finiteSymbol_second_zero] at he
  simp only [lags, Finset.sum_pair A.lower_ne_upper, weight, ite_true,
    ite_eq_right A.lower_ne_upper.symm] at he
  linarith

def certificate (hstrict : ∀ x : ℝ, 0 < x → x ≤ Real.pi → x ≠ (A.frequency : ℝ) → 0 < A.function x)
    (hcurv : 0 < deriv^[2] A.function A.frequency)
    (hend : 0 < deriv^[2] A.function 0) : Certificate q A.edgeShift j k where
  period_ge := A.period_ge
  numerator_pos := A.numerator_pos
  numerator_lt := A.numerator_lt
  inverse := A.inverse
  inverse_pos := A.inverse_pos
  inverse_lt := A.inverse_lt
  inverse_mod := A.inverse_mod
  phase := by
    change Geometry.shiftedAngle q A.edgeShift A.frequency = _
    exact phase_at_shift q A.period_ge
      ⟨atom_pos A.numerator_pos (by have := A.period_ge; omega) A.numerator_lt.le,
        atom_lt_pi (by have := A.period_ge; omega) A.numerator_lt⟩
  lags := A.lags
  nonzero := by
    intro n hn
    simp only [lags, Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl
    · exact A.lower_nonzero
    · exact A.upper_nonzero
  classes := by
    intro n hn
    right
    simp only [lags, Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl
    · exact A.lower_class
    · exact A.upper_class
  weight := A.weight
  weight_pos := by
    intro n hn
    simp only [lags, Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl
    · simp only [weight, ite_true]; linarith [A.mix_lt]
    · simpa only [weight, ite_eq_right A.lower_ne_upper.symm] using A.mix_pos
  weight_sum := by
    simp only [lags, Finset.sum_pair A.lower_ne_upper, weight, ite_true,
      ite_eq_right A.lower_ne_upper.symm]
    ring
  pair := ⟨A.lower, by simp [lags], A.upper, by simp [lags], A.lower_ne_upper,
    A.lower_class, A.upper_class⟩
  strict := by
    intro x hx hxpi hne
    rw [A.finiteSymbol_eq]
    exact mul_neg_of_neg_of_pos (by norm_num) (hstrict x hx hxpi hne)
  curvature := by
    change deriv^[2] (finiteSymbol q A.edgeShift A.lags A.weight) A.frequency < 0
    rw [A.finiteSymbol_second]
    linarith
  endpoint := by
    have he := finiteSymbol_second_zero q A.edgeShift A.lags A.weight
    rw [A.finiteSymbol_second] at he
    linarith

end AdjacentData
end polyak.FareyPlateau.Edge
