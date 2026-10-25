import polyak.FareyPlateau.Edge.Adjacent
import polyak.FareyPlateau.Edge.LatticeCurvature

/-! The edge curvature obstruction on the actual tuning phase. It ranges
over arbitrary finite sets of signed lags in both tight classes. -/
noncomputable section
namespace polyak.FareyPlateau.Edge
open General Levels ModeLocking
open scoped BigOperators

namespace AdjacentData
variable {q : Tuning} {j k : ℕ} (A : AdjacentData q j k)

theorem class_one_trig {n : ℤ} (hn : n % (k : ℤ) = A.inverse) :
    Real.sin ((n : ℝ) * (A.frequency : ℝ) - TwoLag.phase q A.edgeShift A.frequency) = Real.sin (Real.pi / k) ∧
    Real.cos ((n : ℝ) * (A.frequency : ℝ) - TwoLag.phase q A.edgeShift A.frequency) = Real.cos (Real.pi / k) := by
  have he : (n * j) % k = 1 := by
    have hh : (n * j) % k = (A.inverse * j) % k := by
      conv_lhs => rw [Int.mul_emod, hn]
      conv_rhs => rw [Int.mul_emod, Int.emod_eq_of_lt A.inverse_pos.le A.inverse_lt]
    rw [hh]
    simpa only [Int.ModEq, Int.emod_eq_of_lt
      (by have := A.period_ge; omega : (0 : ℤ) ≤ 1)
      (by have := A.period_ge; omega : (1 : ℤ) < k)] using A.inverse_mod
  rw [A.phase_value]
  have ht := lag_trig_reduce (by have := A.period_ge; omega) A.numerator_lt.le n (Real.pi / k)
  simp only [he, Int.cast_one, mul_one] at ht
  have hh : 2 * Real.pi / (k : ℝ) - Real.pi / k = Real.pi / k := by ring
  rw [hh] at ht
  exact ⟨ht.2, ht.1⟩

theorem class_zero_trig {n : ℤ} (hn : n % (k : ℤ) = 0) :
    Real.sin ((n : ℝ) * (A.frequency : ℝ) - TwoLag.phase q A.edgeShift A.frequency) = -Real.sin (Real.pi / k) ∧
    Real.cos ((n : ℝ) * (A.frequency : ℝ) - TwoLag.phase q A.edgeShift A.frequency) = Real.cos (Real.pi / k) := by
  have he : (n * j) % k = 0 := by rw [Int.mul_emod, hn]; simp
  rw [A.phase_value]
  have ht := lag_trig_reduce (by have := A.period_ge; omega) A.numerator_lt.le n (Real.pi / k)
  simp only [he, Int.cast_zero, mul_zero, zero_div, zero_sub, Real.cos_neg, Real.sin_neg] at ht
  exact ⟨ht.2, ht.1⟩

theorem finite_first (N : Finset ℤ) (w : ℤ → ℝ) :
    deriv (finiteSymbol q A.edgeShift N w) A.frequency =
      ∑ n ∈ N, w n * deriv (lagExtension q A.edgeShift n) A.frequency := by
  unfold finiteSymbol
  rw [deriv_fun_sum (fun n _ =>
    (ModeLocking.analyticAt_lagExtension q A.edgeShift n A.frequency.property).differentiableAt.const_mul (w n))]
  simp only [deriv_const_mul_field]

theorem finite_second (N : Finset ℤ) (w : ℤ → ℝ) :
    deriv^[2] (finiteSymbol q A.edgeShift N w) A.frequency =
      ∑ n ∈ N, w n * deriv^[2] (lagExtension q A.edgeShift n) A.frequency := by
  have he : iteratedDeriv 2 (fun x => ∑ n ∈ N, w n * lagExtension q A.edgeShift n x) A.frequency =
      ∑ n ∈ N, iteratedDeriv 2 (fun x => w n * lagExtension q A.edgeShift n x) A.frequency :=
    iteratedDeriv_fun_sum (fun n _ =>
      ((analyticAt_const.mul (ModeLocking.analyticAt_lagExtension q A.edgeShift n A.frequency.property)).contDiffAt :
        ContDiffAt ℝ 2 (fun x => w n * lagExtension q A.edgeShift n x) A.frequency))
  change deriv^[2] (fun x => ∑ n ∈ N, w n * lagExtension q A.edgeShift n x) A.frequency = _
  simpa only [iteratedDeriv_const_mul_field, iteratedDeriv_eq_iterate] using he

theorem obstruction (hcurv : deriv^[2] A.function A.frequency ≤ 0)
    (N : Finset ℤ) (w : ℤ → ℝ) (hw : ∀ n ∈ N, 0 ≤ w n)
    (hne : ∀ n ∈ N, n ≠ 0)
    (hclass : ∀ n ∈ N, n % (k : ℤ) = 0 ∨ n % (k : ℤ) = A.inverse)
    (htangent : deriv (finiteSymbol q A.edgeShift N w) A.frequency = 0) :
    0 ≤ deriv^[2] (finiteSymbol q A.edgeShift N w) A.frequency := by
  let θ := TwoLag.phase q A.edgeShift
  have hθ : AnalyticAt ℝ θ A.frequency := TwoLag.analyticAt_phase q A.edgeShift A.frequency.property
  have hslope : 2 * deriv θ A.frequency = (A.lower : ℝ) + A.mix * k := A.slope
  have hkr : (3 : ℝ) ≤ k := by exact_mod_cast A.period_ge
  have hS : 0 < Real.sin (Real.pi / k) := Real.sin_pos_of_pos_of_lt_pi (by positivity)
    ((div_lt_iff₀ (by positivity : (0 : ℝ) < k)).mpr (by nlinarith [Real.pi_pos]))
  have hC : 0 ≤ Real.cos (Real.pi / k) :=
    (Real.cos_pos_of_mem_Ioo ⟨by
        have hp : 0 < Real.pi / k := by positivity
        linarith [Real.pi_pos],
      (div_lt_iff₀ (by positivity : (0 : ℝ) < k)).mpr (by nlinarith [Real.pi_pos])⟩).le
  have hbound : 2 * Real.sin (Real.pi / k) * deriv^[2] θ A.frequency ≤
      Real.cos (Real.pi / k) * (k : ℝ)^2 * A.mix * (1 - A.mix) := by
    rw [A.second] at hcurv
    linarith
  rw [A.finite_second]
  apply curvature_obstruction (n₁ := (A.lower : ℝ)) (k := (k : ℝ))
    (t := A.mix) (S := Real.sin (Real.pi / k)) (C := Real.cos (Real.pi / k))
    (d := deriv^[2] θ A.frequency) N w
    (fun n => deriv (lagExtension q A.edgeShift n) A.frequency)
    (fun n => deriv^[2] (lagExtension q A.edgeShift n) A.frequency)
    (by positivity) A.mix_pos A.mix_lt hS hC hbound hw
  · intro n hn
    rcases hclass n hn with hz | ho
    · right
      have hem := Int.emod_add_ediv_mul n (k : ℤ)
      rw [hz, zero_add] at hem
      have he : n = (n / k) * k := hem.symm
      refine ⟨n / k, ?_, ?_, ?_⟩
      · intro hm
        rw [hm, zero_mul] at he
        exact hne n hn he
      · change deriv (Geometry.extendedLag θ n) A.frequency = _
        rw [lag_first_position_zero hθ A.phase_value n (A.class_zero_trig hz).1]
        exact congrArg (fun z : ℝ => -Real.sin (Real.pi / k) * z) (by exact_mod_cast he)
      · change deriv^[2] (Geometry.extendedLag θ n) A.frequency = _
        rw [lag_second_position_zero hθ A.phase_value n (A.class_zero_trig hz).1 (A.class_zero_trig hz).2]
        have hen : (n : ℝ) = (n / k : ℤ) * (k : ℝ) := by exact_mod_cast he
        rw [hslope, hen]
    · left
      have hem := Int.emod_add_ediv_mul n (k : ℤ)
      have hel := Int.emod_add_ediv_mul A.lower (k : ℤ)
      rw [ho] at hem
      rw [A.lower_class] at hel
      have he : n = A.lower + (n / k - A.lower / k) * k := by nlinarith only [hem, hel]
      refine ⟨n / k - A.lower / k, ?_, ?_⟩
      · change deriv (Geometry.extendedLag θ n) A.frequency = _
        rw [lag_first_position_one hθ A.phase_value n (A.class_one_trig ho).1, hslope]
        have hen : (n : ℝ) = (A.lower : ℝ) + (n / k - A.lower / k : ℤ) * (k : ℝ) := by exact_mod_cast he
        rw [hen]
      · change deriv^[2] (Geometry.extendedLag θ n) A.frequency = _
        rw [lag_second_position_one hθ A.phase_value n (A.class_one_trig ho).1 (A.class_one_trig ho).2, hslope]
        have hen : (n : ℝ) = (A.lower : ℝ) + (n / k - A.lower / k : ℤ) * (k : ℝ) := by exact_mod_cast he
        rw [hen]
  · rwa [← A.finite_first]

theorem tight_classes (n : ℤ)
    (ht : (Geometry.shiftedCurve q A.edgeShift).lag n A.frequency = 0) :
    n % (k : ℤ) = 0 ∨ n % (k : ℤ) = A.inverse := by
  have hp : Geometry.shiftedCurve q A.edgeShift A.frequency = Real.pi / k := by
    change Geometry.shiftedAngle q A.edgeShift A.frequency = _
    exact phase_at_shift q A.period_ge
      ⟨atom_pos A.numerator_pos (by have := A.period_ge; omega) A.numerator_lt.le,
        atom_lt_pi (by have := A.period_ge; omega) A.numerator_lt⟩
  have hlag := lag_position_one (by have := A.period_ge; omega) A.numerator_lt.le _ hp n
  change (Geometry.shiftedCurve q A.edgeShift).lag n (atom j k (by have := A.period_ge; omega) A.numerator_lt.le) = 0 at ht
  rw [hlag] at ht
  have he := Farey.residue_transport_of_inverse (i := 1) A.inverse_mod n
  simp only [mul_one, one_mul] at he
  by_cases hz : (n * j) % k = 0
  · left
    simpa only [hz, mul_zero, Int.zero_emod] using he
  · right
    have hkZ : (0 : ℤ) < k := by have := A.period_ge; omega
    have hpos : 0 < (n * j) % k := by
      have := Int.emod_nonneg (n * j) hkZ.ne'
      omega
    have hρ : (((n * j) % k : ℤ) : ℝ) = 1 :=
      (Farey.positionValue_eq_zero_iff hkZ (by norm_num)
        (by exact_mod_cast (show 1 ≤ k by have := A.period_ge; omega))
        (by exact_mod_cast hpos) (by exact_mod_cast Int.emod_lt_of_pos (n * j) hkZ)).mp ht
    have hρZ : (n * j) % k = 1 := by exact_mod_cast hρ
    simpa only [hρZ, mul_one, Int.emod_eq_of_lt A.inverse_pos.le A.inverse_lt] using he

/-- The obstruction excludes regular singleton support for every period L. -/
theorem not_regular_singleton (hcurv : deriv^[2] A.function A.frequency ≤ 0)
    {L : ℕ} (D : RegularData q A.edgeShift L)
    (hS : Set.range D.atoms = {A.frequency}) : False := by
  have hatom (i : Fin D.d) : D.atoms i = A.frequency := by
    have hi : D.atoms i ∈ ({A.frequency} : Set Frequency) := by rw [← hS]; exact ⟨i, rfl⟩
    exact Set.mem_singleton_iff.mp hi
  have hsum : ∑ i, (D.primal i : ℝ) = 1 := by exact_mod_cast D.primal_sum
  have hc (n : ℤ) (hn : n ∈ D.lags) : n % (k : ℤ) = 0 ∨ n % (k : ℤ) = A.inverse := by
    apply A.tight_classes
    have hh := D.lag_tight n hn
    simpa only [hatom, ← Finset.sum_mul, hsum, one_mul] using hh
  let i : Fin D.d := ⟨0, D.d_pos⟩
  have ht : deriv (finiteSymbol q A.edgeShift D.lags D.dual) A.frequency = 0 := by
    simpa only [hatom] using D.symbol_slope_support i
  have hsecond := A.obstruction hcurv D.lags D.dual (fun n hn => (D.dual_pos n hn).le)
    D.lags_nonzero hc ht
  have hneg := D.support_curvature i
  rw [hatom] at hneg
  linarith

end AdjacentData
end polyak.FareyPlateau.Edge
