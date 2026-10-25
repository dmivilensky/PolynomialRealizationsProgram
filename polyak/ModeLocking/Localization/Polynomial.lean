import polyak.ModeLocking.Localization.Defect
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! The exact closed interval equivalence for polynomial certificates,
including the forced positive minimizer coefficient. -/
noncomputable section
namespace polyak.ModeLocking.Localization
open Levels Set Farey.Certificates
open Spectral (chebT chebU)
open scoped BigOperators
variable {I : Type*} [Fintype I]

theorem indexedPolynomial_one (q : General.Tuning) (n : I → ℤ) (a : I → ℝ) (γ : ℝ) :
    indexedPolynomial q n a γ 1 = γ*q.Xi 1 := by
  simp [indexedPolynomial, signedLagPolynomial, chebT]

theorem indexedPolynomial_neg_one (q : General.Tuning) (n : I → ℤ) (a : I → ℝ) (γ : ℝ) :
    indexedPolynomial q n a γ (-1) =
      q.Xi (-1) * ((∑ i, a i*(1-(-1:ℝ)^((n i).natAbs)))+γ) := by
  simp only [indexedPolynomial, signedLagPolynomial, neg_one_sq, sub_self, mul_zero,
    zero_mul, sub_zero]
  have he (m : ℕ) : chebT m (-1) = (-1:ℝ)^m := by simp [chebT]
  simp_rw [he]
  rw [mul_add, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    ring
  · ring

theorem strict_polynomial_iff (q : General.Tuning) (n : I → ℤ) (a : I → ℝ) (γ : ℝ)
    (hn : ∀ i, n i ≠ 0) (ha : ∀ i, 0 ≤ a i) (_hγ : 0 ≤ γ) :
    (∀ ω : Frequency, (∑ i, a i*(tuningCurve q).lag (n i) ω) +
      γ*(tuningCurve q).minimizer ω < 0) ↔
      ∀ c ∈ Icc (-1:ℝ) 1, indexedPolynomial q n a γ c < 0 := by
  constructor
  · intro h c hc
    have hg : 0 < γ := by
      have he := h frequencyZero
      simpa only [Curve.lag_at_zero, mul_zero, Finset.sum_const_zero,
        Curve.minimizer_at_zero, mul_neg, mul_one, zero_add, neg_lt_zero] using he
    by_cases hp : c=1
    · subst c
      rw [indexedPolynomial_one]
      exact mul_neg_of_pos_of_neg hg q.Xi_one_neg
    by_cases hm : c= -1
    · subst c
      rw [indexedPolynomial_neg_one]
      apply mul_neg_of_neg_of_pos q.Xi_neg_one_neg
      have hs : 0 ≤ ∑ i, a i*(1-(-1:ℝ)^((n i).natAbs)) := by
        apply Finset.sum_nonneg
        intro i _
        apply mul_nonneg (ha i)
        have he := neg_one_pow_eq_or ((n i).natAbs) (R := ℝ)
        rcases he with he | he <;> rw [he] <;> norm_num
      linarith
    have hc' : -1<c ∧ c<1 :=
      ⟨lt_of_le_of_ne hc.1 (Ne.symm hm), lt_of_le_of_ne hc.2 hp⟩
    let ω : Frequency := ⟨Real.arccos c, Real.arccos_nonneg c, Real.arccos_le_pi c⟩
    have hω : 0<(ω:ℝ) ∧ (ω:ℝ)<Real.pi :=
      ⟨Real.arccos_pos.mpr hc'.2, Real.arccos_lt_pi.mpr hc'.1⟩
    have he := h ω
    rw [indexed_polynomial_factor q n a γ hn ω hω] at he
    have hs : 0 < Real.sin (q.angle ω)/Real.sin (ω:ℝ) :=
      div_pos (Real.sin_pos_of_pos_of_lt_pi (q.angle_mem hω).1 (q.angle_mem hω).2)
        (Real.sin_pos_of_pos_of_lt_pi hω.1 hω.2)
    have ht : indexedPolynomial q n a γ (Real.cos (ω:ℝ)) < 0 :=
      (mul_neg_iff.mp he).resolve_right (fun h => (not_lt_of_ge hs.le) h.1) |>.2
    simpa only [ω, Real.cos_arccos hc.1 hc.2] using ht
  · intro hP
    have hg : 0 < γ := by
      have he := hP 1 ⟨by norm_num, le_rfl⟩
      rw [indexedPolynomial_one] at he
      nlinarith [q.Xi_one_neg]
    exact indexed_polynomial_negative q n a hn ha hg hP

theorem polynomial_gamma_zero_impossible (q : General.Tuning) (n : I → ℤ) (a : I → ℝ) :
    ¬ (∀ c ∈ Icc (-1:ℝ) 1, indexedPolynomial q n a 0 c < 0) := by
  intro h
  have he := h 1 ⟨by norm_num, le_rfl⟩
  simp only [indexedPolynomial_one, zero_mul, lt_self_iff_false] at he

theorem indexedPolynomial_grouped (q : General.Tuning) (n : I → ℤ) (a : I → ℝ) (γ c : ℝ) :
    indexedPolynomial q n a γ c =
      q.Xi c*((∑ i, a i*(1-chebT (n i).natAbs c))+γ) -
        (1-c^2)*(∑ i, (n i).sign*a i*chebU ((n i).natAbs-1) c) := by
  unfold indexedPolynomial signedLagPolynomial
  have he : (∑ i, a i*(q.Xi c*(1-chebT (n i).natAbs c)-
      ((n i).sign:ℝ)*(1-c^2)*chebU ((n i).natAbs-1) c)) =
      (∑ i, q.Xi c*(a i*(1-chebT (n i).natAbs c))) -
        ∑ i, (1-c^2)*(((n i).sign:ℝ)*a i*chebU ((n i).natAbs-1) c) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he,← Finset.mul_sum,← Finset.mul_sum]
  ring

theorem polynomial_certificates (q : General.Tuning) (n : I → ℤ) (a : I → ℝ) (γ : ℝ)
    (hn : ∀ i, n i ≠ 0) (ha : ∀ i, 0 ≤ a i) (hγ : 0 ≤ γ) :
    (∀ ω : Frequency, (∑ i, a i*(tuningCurve q).lag (n i) ω) +
      γ*(tuningCurve q).minimizer ω < 0) ↔
    ∀ c ∈ Icc (-1:ℝ) 1,
      q.Xi c*((∑ i, a i*(1-chebT (n i).natAbs c))+γ) <
        (1-c^2)*(∑ i, ((n i).sign:ℝ)*a i*chebU ((n i).natAbs-1) c) := by
  rw [strict_polynomial_iff q n a γ hn ha hγ]
  simp only [indexedPolynomial_grouped, sub_lt_zero]

theorem strict_symbol_polynomial_iff (q : General.Tuning) (n : I → ℤ) (a : I → ℝ) (γ : ℝ)
    (hn : ∀ i, n i ≠ 0) (ha : ∀ i, 0 ≤ a i) (hγ : 0 ≤ γ) :
    (∃ ε > 0, ∀ ω : Frequency, (∑ i, a i*(tuningCurve q).lag (n i) ω) +
      γ*(tuningCurve q).minimizer ω ≤ -ε) ↔
      ∀ c ∈ Icc (-1:ℝ) 1, indexedPolynomial q n a γ c < 0 := by
  rw [← strict_polynomial_iff q n a γ hn ha hγ]
  constructor
  · rintro ⟨ε,hε,h⟩ ω
    exact lt_of_le_of_lt (h ω) (neg_neg_of_pos hε)
  · intro h
    let f : Frequency → ℝ := fun ω => (∑ i,a i*(tuningCurve q).lag (n i) ω) +
      γ*(tuningCurve q).minimizer ω
    have hf : Continuous f := by
      have hh := continuous_symbol q 0 n a γ
      change Continuous (fun ω => symbol q 0 n a γ ω) at hh
      simpa only [symbol,Geometry.shiftedCurve_zero] using hh
    obtain ⟨ω,_hω,hmax⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hf.continuousOn
    refine ⟨-f ω,neg_pos.mpr (h ω),?_⟩
    intro x
    simpa only [neg_neg] using (show f x ≤ f ω from hmax (mem_univ x))

end polyak.ModeLocking.Localization
