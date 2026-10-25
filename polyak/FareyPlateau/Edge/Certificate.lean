import polyak.FareyPlateau.Edge.Basic

/-! Lemma certjk, as a constructor of the actual primary regularity data.
Only the three scalar sign/curvature assumptions of the article are supplied;
all primal, rank, pinning and residue conditions are proved here. -/
noncomputable section
namespace polyak.FareyPlateau.Edge
open General Levels ModeLocking
open scoped BigOperators

structure Certificate (q : Tuning) (s : ℝ) (j k : ℕ) where
  period_ge : 3 ≤ k
  numerator_pos : 1 ≤ j
  numerator_lt : 2 * j < k
  inverse : ℤ
  inverse_pos : 0 < inverse
  inverse_lt : inverse < k
  inverse_mod : inverse * (j : ℤ) ≡ 1 [ZMOD (k : ℤ)]
  phase : Geometry.shiftedCurve q s (atom j k (by omega) numerator_lt.le) = Real.pi / k
  lags : Finset ℤ
  nonzero : ∀ n ∈ lags, n ≠ 0
  classes : ∀ n ∈ lags, n % (k : ℤ) = 0 ∨ n % (k : ℤ) = inverse
  weight : ℤ → ℝ
  weight_pos : ∀ n ∈ lags, 0 < weight n
  weight_sum : ∑ n ∈ lags, weight n = 1
  pair : ∃ n₁ ∈ lags, ∃ n₂ ∈ lags, n₁ ≠ n₂ ∧
    n₁ % (k : ℤ) = inverse ∧ n₂ % (k : ℤ) = inverse
  strict : ∀ x : ℝ, 0 < x → x ≤ Real.pi →
    x ≠ (atom j k (by omega) numerator_lt.le : ℝ) → finiteSymbol q s lags weight x < 0
  curvature : deriv^[2] (finiteSymbol q s lags weight)
    (atom j k (by omega) numerator_lt.le : ℝ) < 0
  endpoint : 0 < ∑ n ∈ lags, weight n * (n : ℝ) * ((n : ℝ) + 2 * Geometry.tau q)

namespace Certificate
variable {q : Tuning} {s : ℝ} {j k : ℕ} (C : Certificate q s j k)

def frequency : Frequency := atom j k (by have := C.period_ge; omega) C.numerator_lt.le

theorem grid_phase : Farey.gridPhase (Geometry.shiftedCurve q s) k j
    (by exact_mod_cast (show 0 < k by have := C.period_ge; omega)) (by positivity)
    (by exact_mod_cast C.numerator_lt.le) = 1 :=
  phase_index_one (by have := C.period_ge; omega) C.numerator_lt.le _ C.phase

theorem lag (n : ℤ) : (Geometry.shiftedCurve q s).lag n C.frequency =
    Farey.positionValue k 1 (((n * j) % k : ℤ) : ℝ) :=
  lag_position_one (by have := C.period_ge; omega) C.numerator_lt.le _ C.phase n

theorem tight : (Geometry.shiftedCurve q s).lag C.inverse C.frequency = 0 := by
  rw [C.lag]
  have hi : (C.inverse * j) % k = 1 := by
    simpa only [Int.ModEq, Int.emod_eq_of_lt (by have := C.period_ge; omega : (0 : ℤ) ≤ 1)
      (by have := C.period_ge; omega : (1 : ℤ) < k)] using C.inverse_mod
  simp only [hi, Int.cast_one, Farey.positionValue_self]

theorem inactive (r : ℤ) (hr : 0 < r) (hrk : r < k) (hne : r ≠ C.inverse) :
    0 < (Geometry.shiftedCurve q s).lag r C.frequency := by
  rw [C.lag]
  have hk : (0 : ℤ) < k := by omega
  have hz : (r * j) % k ≠ 0 := by
    intro hz
    have he := Farey.residue_transport_of_inverse (i := 1) C.inverse_mod r
    simp only [mul_one, one_mul, hz, mul_zero, Int.zero_emod,
      Int.emod_eq_of_lt hr.le hrk] at he
    omega
  have ho : (r * j) % k ≠ 1 := by
    intro ho
    exact hne ((residue_one_iff (by have := C.period_ge; omega) C.inverse_mod C.inverse_pos C.inverse_lt hr.le hrk).mp ho)
  have hp : (1 : ℤ) < (r * j) % k := by
    have := Int.emod_nonneg (r * j) hk.ne'
    omega
  exact (Farey.positionValue_pos_iff hk (by norm_num) (by exact_mod_cast (show 1 ≤ k by omega))
    (by exact_mod_cast (show 0 < (r * j) % k by omega))
    (by exact_mod_cast Int.emod_lt_of_pos (r * j) hk)).mpr (by exact_mod_cast hp)

theorem pinning_positive : 0 < pinningPolynomial C.lags C.weight C.frequency := by
  obtain ⟨n₁, hn₁, n₂, _hn₂, _hne, hclass, _hclass₂⟩ := C.pair
  have hi : (n₁ * j) % k = 1 := by
    have he : (n₁ * j) % k = (C.inverse * j) % k := by
      conv_lhs => rw [Int.mul_emod, hclass]
      conv_rhs => rw [Int.mul_emod, Int.emod_eq_of_lt C.inverse_pos.le C.inverse_lt]
    rw [he]
    simpa only [Int.ModEq, Int.emod_eq_of_lt (by have := C.period_ge; omega : (0 : ℤ) ≤ 1)
      (by have := C.period_ge; omega : (1 : ℤ) < k)] using C.inverse_mod
  have hcos := (lag_trig_reduce (by have := C.period_ge; omega) C.numerator_lt.le n₁ 0).1
  simp only [sub_zero, hi, Int.cast_one, mul_one] at hcos
  have hphase : 0 < 2 * Real.pi / k ∧ 2 * Real.pi / k < 2 * Real.pi := by
    have hkr : (3 : ℝ) ≤ k := by exact_mod_cast C.period_ge
    exact ⟨by positivity, (div_lt_iff₀ (by positivity : (0 : ℝ) < k)).mpr
      (by nlinarith [Real.pi_pos])⟩
  have hct : Real.cos ((n₁ : ℝ) * (C.frequency : ℝ)) < 1 := by
    rw [show (C.frequency : ℝ) = (atom j k (by have := C.period_ge; omega) C.numerator_lt.le : ℝ) from rfl, hcos]
    apply lt_of_le_of_ne (Real.cos_le_one _)
    intro he
    have hz := (Real.cos_eq_one_iff_of_lt_of_lt (by linarith [Real.pi_pos]) hphase.2).mp he
    linarith [hphase.1]
  unfold pinningPolynomial
  exact Finset.sum_pos' (fun n hn => mul_nonneg (C.weight_pos n hn).le
    (sub_nonneg.mpr (Real.cos_le_one _))) ⟨n₁, hn₁,
      mul_pos (C.weight_pos n₁ hn₁) (sub_pos.mpr hct)⟩

theorem pinning_sine : Real.sin ((C.inverse : ℝ) * (C.frequency : ℝ) -
    Geometry.shiftedCurve q s C.frequency) = Real.sin (Real.pi / k) := by
  have hi : (C.inverse * j) % k = 1 := by
    simpa only [Int.ModEq, Int.emod_eq_of_lt (by have := C.period_ge; omega : (0 : ℤ) ≤ 1)
      (by have := C.period_ge; omega : (1 : ℤ) < k)] using C.inverse_mod
  rw [show Geometry.shiftedCurve q s C.frequency = Real.pi / k from C.phase]
  change Real.sin ((C.inverse : ℝ) * (atom j k (by have := C.period_ge; omega) C.numerator_lt.le : ℝ) - _) = _
  rw [(lag_trig_reduce (by have := C.period_ge; omega) C.numerator_lt.le C.inverse (Real.pi / k)).2, hi]
  congr 1
  push_cast
  ring

def regularData : RegularData q s k where
  period_ge := C.period_ge
  d := 1
  atoms := fun _ => C.frequency
  atoms_injective := fun _ _ _ => Subsingleton.elim _ _
  atoms_grid := fun _ => atom_grid C.numerator_pos (by have := C.period_ge; omega) C.numerator_lt.le
  atoms_lt_pi := fun _ => atom_lt_pi (by have := C.period_ge; omega) C.numerator_lt
  reps := fun _ => C.inverse
  reps_pos := fun _ => C.inverse_pos
  reps_lt := fun _ => C.inverse_lt
  reps_injective := fun _ _ _ => Subsingleton.elim _ _
  lags := C.lags
  lags_nonzero := C.nonzero
  classes := by
    intro n hn
    rcases C.classes n hn with h | h
    · exact Or.inl h
    · exact Or.inr ⟨0, h⟩
  primal := fun _ => 1
  primal_pos := by intro _; norm_num
  primal_sum := by simp
  dual := C.weight
  dual_pos := C.weight_pos
  dual_sum := C.weight_sum
  tight := by intro _; simpa using C.tight
  inactive := by
    intro r hr hrk hne
    simpa using C.inactive r hr hrk (hne 0)
  minimizer_strict := by
    simp only [NNReal.coe_one, one_mul, Fin.sum_univ_one]
    change 0 < Real.cos (Geometry.shiftedCurve q s C.frequency)
    rw [show Geometry.shiftedCurve q s C.frequency = Real.pi / k from C.phase]
    have hkr : (3 : ℝ) ≤ k := by exact_mod_cast C.period_ge
    exact Real.cos_pos_of_mem_Ioo ⟨by
        have hp : 0 < Real.pi / k := by positivity
        linarith [Real.pi_pos],
      (div_lt_iff₀ (by positivity : (0 : ℝ) < k)).mpr (by nlinarith [Real.pi_pos])⟩
  rank := by
    change Matrix.rank (Matrix.of (fun _ _ : Fin 1 =>
      (Geometry.shiftedCurve q s).lag C.inverse C.frequency)) = 0
    have he : Matrix.of (fun _ _ : Fin 1 => (Geometry.shiftedCurve q s).lag C.inverse C.frequency) =
        (0 : Matrix (Fin 1) (Fin 1) ℝ) := by
      ext r i
      exact C.tight
    rw [he, Matrix.rank_zero]
  dual_strict := by intro x hx hxpi hne; exact C.strict x hx hxpi (hne 0)
  support_curvature := fun _ => C.curvature
  endpoint_curvature := C.endpoint
  pinning_pos := fun _ => C.pinning_positive
  class_pair := fun _ => C.pair
  pinning_det := by
    change Matrix.det (Matrix.of (fun _ _ : Fin 1 =>
      Real.sin ((C.inverse : ℝ) * (C.frequency : ℝ) - Geometry.shiftedCurve q s C.frequency))) ≠ 0
    rw [Matrix.det_fin_one]
    rw [C.pinning_sine]
    have hkr : (3 : ℝ) ≤ k := by exact_mod_cast C.period_ge
    exact (Real.sin_pos_of_pos_of_lt_pi (by positivity)
      ((div_lt_iff₀ (by positivity : (0 : ℝ) < k)).mpr (by nlinarith [Real.pi_pos]))).ne'

include C in
theorem regular : RegularPoint q s k := ⟨C.regularData⟩

include C in
theorem sigma_eq : Threshold.sigma q = s := C.regularData.sigma_eq

include C in
theorem sigmaPeriodic_eq : Threshold.sigmaPeriodic q k = s := C.regularData.sigmaPeriodic_eq

end Certificate
end polyak.FareyPlateau.Edge
