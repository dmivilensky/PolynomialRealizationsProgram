import nesterov.Closure.SpectralSet
import nesterov.Attainment.StrictMinimizer

/-! Root exclusion above the actual quadratic rate excludes simultaneous
zero gap/skew and gives a strictly negative gap at both real endpoints. -/
noncomputable section
open scoped BigOperators NNReal
namespace nesterov.Attainment
open Spectral

/-- The elementary planar alternative, including a zero query amplitude. -/
theorem real_mul_of_gap_nonneg_skew_zero (u p : ℂ)
    (hg : 0 ≤ Complex.normSq u-Complex.normSq p) (hs : (p*star u).im = 0) :
    ∃ d : ℝ, |d| ≤ 1 ∧ p = (d : ℂ)*u := by
  by_cases hu : u = 0
  · subst u
    have hp : p = 0 := by
      apply Complex.normSq_eq_zero.mp
      simp only [Complex.normSq_zero, zero_sub] at hg
      exact le_antisymm (by linarith) (Complex.normSq_nonneg p)
    exact ⟨0, by norm_num, by simp [hp]⟩
  have him : (p/u).im = 0 := by
    rw [Complex.div_im]
    have he : p.im*u.re-p.re*u.im=0 := by
      simpa only [Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im,
        mul_neg, sub_eq_add_neg, add_comm] using hs
    rw [← sub_div, he, zero_div]
  let d := (p/u).re
  have hd : p/u = (d : ℂ) := Complex.ext rfl him
  have hp : p = (d : ℂ)*u := (div_eq_iff hu).mp hd
  have hn : ‖p‖ ≤ ‖u‖ := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hg
    nlinarith [norm_nonneg p, norm_nonneg u]
  refine ⟨d, ?_, hp⟩
  have hh : ‖p/u‖ ≤ 1 := by
    rw [norm_div]
    exact (div_le_one (norm_pos_iff.mpr hu)).mpr hn
  simpa only [hd, Complex.norm_real, Real.norm_eq_abs] using hh

theorem characteristic_zero_of_normalized_real_mul (M : StationaryMethod)
    {μ L : ℝ} (hμL : μ < L) (z : ℂ) (d : ℝ)
    (hp : ((M.normalizedPolynomial μ L).map Complex.ofRealHom).eval z =
      (d : ℂ)*(M.queryPolynomial.map Complex.ofRealHom).eval z) :
    M.characteristic ((L+μ-(L-μ)*d)/2) z = 0 := by
  rw [M.normalizedPolynomial_complex_eval] at hp
  rw [M.characteristic_eq_polynomial_eval]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
  have hd : ((L-μ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr hμL.ne')
  have he := congrArg (fun w : ℂ => ((L-μ : ℝ) : ℂ)*w) hp
  push_cast at he ⊢
  push_cast at hd
  field_simp [hd] at he
  linear_combination -he/2

theorem norm_le_quadraticRate_of_gap_nonneg_skew_zero (M : StationaryMethod)
    {μ L : ℝ} (hμ : 0 < μ) (hμL : μ < L) (z : ℂ)
    (hg : 0 ≤ Complex.normSq ((M.queryPolynomial.map Complex.ofRealHom).eval z)-
      Complex.normSq (((M.normalizedPolynomial μ L).map Complex.ofRealHom).eval z))
    (hs : (((M.normalizedPolynomial μ L).map Complex.ofRealHom).eval z *
      star ((M.queryPolynomial.map Complex.ofRealHom).eval z)).im = 0) :
    ‖z‖ ≤ Rates.quadraticRate M μ L := by
  obtain ⟨d, hd, hp⟩ := real_mul_of_gap_nonneg_skew_zero _ _ hg hs
  have hlam : (L+μ-(L-μ)*d)/2 ∈ Set.Icc μ L := by
    have hd' := abs_le.mp hd
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left hd'.1 (sub_pos.mpr hμL).le,
      mul_le_mul_of_nonneg_left hd'.2 (sub_pos.mpr hμL).le]
  exact (Rates.quadraticRate_isGreatest M hμ hμL).2
    ⟨_, hlam, z, characteristic_zero_of_normalized_real_mul M hμL z d hp, rfl⟩

/-- Above the quadratic rate, no frequency has simultaneously zero gap and skew. -/
theorem gap_skew_ne_zero_above_quadratic (M : StationaryMethod) {μ L t : ℝ}
    (hμ : 0 < μ) (hμL : μ < L) (ht : Real.log (Rates.quadraticRate M μ L) < t)
    (c : Frequency) : g (M.symbolPair μ L t) c ≠ 0 ∨ skew (M.symbolPair μ L t) c ≠ 0 := by
  by_contra hn
  push Not at hn
  have hz := norm_le_quadraticRate_of_gap_nonneg_skew_zero M hμ hμL
    (polyak.Waves.z t (Real.arccos c)) (by exact hn.1.ge) hn.2
  have hnorm : ‖polyak.Waves.z t (Real.arccos c)‖ = Real.exp t := by
    simpa using polyak.Waves.norm_z_pow t (Real.arccos c) 1
  rw [hnorm] at hz
  have hlt := Real.exp_lt_exp.mpr ht
  rw [Real.exp_log (Rates.quadraticRate_pos M hμ hμL)] at hlt
  exact (not_le_of_gt hlt) hz

/-- Lemma strict, for every finite interior spectrum above the quadratic rate. -/
theorem finite_strict_above_quadratic (M : StationaryMethod) {μ L t C : ℝ}
    (hμ : 0 < μ) (hμL : μ < L) (htq : Real.log (Rates.quadraticRate M μ L) < t)
    (ht : t ≠ 0) {J : Type*} [Fintype J] (w : J → ℝ≥0) (c : J → Frequency)
    (hw : ∑ j, w j = 1) (hci : Function.Injective c)
    (hc : ∀ j, -1 < (c j : ℝ) ∧ (c j : ℝ) < 1)
    (h : Feasible (M.symbolPair μ L t) t (finiteSpectrum w c hw) C) :
    |C| < meanG (finiteSpectrum w c hw) (M.symbolPair μ L t) :=
  finite_strict_minimizer w c hw hci hc
    (fun j => gap_skew_ne_zero_above_quadratic M hμ hμL htq (c j)) ht h

theorem gap_neg_of_skew_zero_above_quadratic (M : StationaryMethod) {μ L t : ℝ}
    (hμ : 0 < μ) (hμL : μ < L) (ht : Real.log (Rates.quadraticRate M μ L) < t)
    (c : Frequency) (hsk : skew (M.symbolPair μ L t) c=0) :
    g (M.symbolPair μ L t) c < 0 := by
  by_contra hn
  have hz := norm_le_quadraticRate_of_gap_nonneg_skew_zero M hμ hμL
    (polyak.Waves.z t (Real.arccos c)) (le_of_not_gt hn) hsk
  have hnorm : ‖polyak.Waves.z t (Real.arccos c)‖ = Real.exp t := by
    simpa using polyak.Waves.norm_z_pow t (Real.arccos c) 1
  rw [hnorm] at hz
  have hlt := Real.exp_lt_exp.mpr ht
  rw [Real.exp_log (Rates.quadraticRate_pos M hμ hμL)] at hlt
  exact (not_le_of_gt hlt) hz

theorem skew_endpoint_zero (M : StationaryMethod) (μ L t : ℝ) (c : Frequency)
    (hc : (c : ℝ)=1 ∨ (c : ℝ)= -1) : skew (M.symbolPair μ L t) c=0 := by
  have hsin : Real.sin (Real.arccos c)=0 := by rcases hc with hc | hc <;> simp [hc]
  let x := Real.exp t * Real.cos (Real.arccos c)
  have hz : polyak.Waves.z t (Real.arccos c) = (x : ℂ) := by
    apply Complex.ext
    · simpa only [pow_one,Nat.cast_one,one_mul,Complex.ofReal_re,x] using polyak.Waves.z_pow_re t (Real.arccos c) 1
    · simpa only [pow_one,Nat.cast_one,one_mul,hsin,mul_zero,Complex.ofReal_im] using
        polyak.Waves.z_pow_im t (Real.arccos c) 1
  have hu : (M.symbolPair μ L t).u c = ((M.queryPolynomial.eval x : ℝ) : ℂ) := by
    rw [M.symbolPair_u,hz]
    exact Polynomial.eval_map_apply Complex.ofRealHom x
  have hp : (M.symbolPair μ L t).p c = (((M.normalizedPolynomial μ L).eval x : ℝ) : ℂ) := by
    rw [M.symbolPair_p,hz]
    exact Polynomial.eval_map_apply Complex.ofRealHom x
  simp only [skew,hu,hp,Complex.star_def,Complex.conj_ofReal,Complex.mul_im,
    Complex.ofReal_im,mul_zero,zero_mul,add_zero]

theorem gap_endpoint_neg (M : StationaryMethod) {μ L t : ℝ}
    (hμ : 0 < μ) (hμL : μ < L) (ht : Real.log (Rates.quadraticRate M μ L) < t)
    (c : Frequency) (hc : (c : ℝ)=1 ∨ (c : ℝ)= -1) :
    g (M.symbolPair μ L t) c < 0 :=
  gap_neg_of_skew_zero_above_quadratic M hμ hμL ht c (skew_endpoint_zero M μ L t c hc)

end nesterov.Attainment
