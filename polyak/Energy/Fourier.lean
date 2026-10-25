import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Tactic

/-!
Article: Appendix A, Parseval's step in Lemma energy.
Use: finite Hilbert-valued Fourier sums over normalized Haar measure. Working
with real and imaginary parts avoids any completeness or complexification
assumption on the original real Hilbert space.
Source: mathlib's orthonormality of the characters of the additive circle.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace polyak.Energy

local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- Article: the frequency circle for the finite Parseval computation. -/
abbrev FrequencyCircle := AddCircle (2 * Real.pi)

/-- Article: the normalized Fourier character with an integer frequency. -/
abbrev character (k : ℤ) : C(FrequencyCircle, ℂ) := fourier k

/-- Article: orthogonality of the zero and k-th characters, in integral form. -/
theorem integral_character (k : ℤ) :
    (∫ θ : FrequencyCircle, character k θ ∂AddCircle.haarAddCircle) =
      if k = 0 then 1 else 0 := by
  have h := orthonormal_iff_ite.mp
    (orthonormal_fourier (T := 2 * Real.pi)) 0 k
  rw [ContinuousMap.inner_toLp] at h
  simpa only [character, fourier_zero, map_one, one_mul, mul_one,
    eq_comm (a := (0 : ℤ))] using h

/-- Article: real orthogonality of integer Fourier characters. -/
theorem integral_character_re (k : ℤ) :
    (∫ θ : FrequencyCircle, (character k θ).re ∂AddCircle.haarAddCircle) =
      if k = 0 then 1 else 0 := by
  change (∫ θ : FrequencyCircle, RCLike.re (character k θ) ∂AddCircle.haarAddCircle) = _
  rw [integral_re ((character k).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)), integral_character]
  split_ifs <;> simp

/-- Article: the real part of the difference character is a Euclidean dot product. -/
theorem character_sub_re (i j : ℤ) (θ : FrequencyCircle) :
    (character (j - i) θ).re =
      (character i θ).re * (character j θ).re +
      (character i θ).im * (character j θ).im := by
  rw [sub_eq_add_neg, fourier_add, fourier_neg]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- Article: product-to-sum identity for real Fourier characters. -/
theorem character_re_mul_re (i j : ℤ) (θ : FrequencyCircle) :
    (character i θ).re * (character j θ).re =
      ((character (i+j) θ).re + (character (i-j) θ).re) / 2 := by
  rw [sub_eq_add_neg, fourier_add, fourier_add, fourier_neg]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- Article: real Fourier orthogonality, including the two possible signs of the frequency. -/
theorem integral_character_re_mul_re (i j : ℤ) :
    (∫ θ : FrequencyCircle, (character i θ).re * (character j θ).re
      ∂AddCircle.haarAddCircle) =
      ((if i+j = 0 then 1 else 0) + (if i-j = 0 then 1 else 0)) / 2 := by
  simp_rw [character_re_mul_re]
  rw [integral_div, integral_add]
  · rw [integral_character_re, integral_character_re]
  · exact (Complex.continuous_re.comp (character (i+j)).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact (Complex.continuous_re.comp (character (i-j)).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype I]

/-- Article: squared size of a finite Hilbert Fourier sum, written as a Gram polynomial. -/
def fourierGram (d : I → ℤ) (u : I → E) (θ : FrequencyCircle) : ℝ :=
  ∑ i, ∑ j, inner ℝ (u i) (u j) * (character (d j - d i) θ).re

/-- Article: finite autocorrelation at an integer lag, without an ambient infinite sum. -/
def integerCorrelation (d : I → ℤ) (u : I → E) (n : ℤ) : ℝ :=
  ∑ i, ∑ j, if d j - d i = n then inner ℝ (u i) (u j) else 0

/-- Article: symmetry of real Hilbert autocorrelations. Proof: interchange the two finite indices. -/
theorem integerCorrelation_neg (d : I → ℤ) (u : I → E) (n : ℤ) :
    integerCorrelation d u (-n) = integerCorrelation d u n := by
  classical
  unfold integerCorrelation
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [show d i - d j = -n ↔ d j - d i = n by omega]
  rw [real_inner_comm (u j) (u i)]

/-- Article: the Gram polynomial is the sum of the squared cosine and sine transforms.
Use: pointwise positivity before integrating a nonpositive symbol.
Proof: bilinearity of the real Hilbert inner product and the difference-character identity. -/
theorem fourierGram_eq_sq (d : I → ℤ) (u : I → E) (θ : FrequencyCircle) :
    fourierGram d u θ =
      ‖∑ i, (character (d i) θ).re • u i‖ ^ 2 +
      ‖∑ i, (character (d i) θ).im • u i‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
  rw [← Finset.sum_add_distrib]
  unfold fourierGram
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [character_sub_re]
  rw [real_inner_comm (u j) (u i)]
  ring

/-- Article: the nonnegative integrand in the Hilbert Parseval inequality. -/
theorem fourierGram_nonneg (d : I → ℤ) (u : I → E) (θ : FrequencyCircle) :
    0 ≤ fourierGram d u θ := by
  rw [fourierGram_eq_sq]
  positivity

/-- Article: all finite Hilbert Fourier Gram polynomials are continuous. -/
@[fun_prop] theorem continuous_fourierGram (d : I → ℤ) (u : I → E) :
    Continuous (fourierGram d u) := by
  unfold fourierGram
  fun_prop

/-- Article: finite Hilbert Parseval, with possible repeated frequencies retained.
Proof: integrate the finite Gram expansion and use character orthogonality. -/
theorem integral_fourierGram (d : I → ℤ) (u : I → E) :
    (∫ θ : FrequencyCircle, fourierGram d u θ ∂AddCircle.haarAddCircle) =
      ∑ i, ∑ j, if d i = d j then inner ℝ (u i) (u j) else 0 := by
  unfold fourierGram
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j _
      rw [integral_const_mul, integral_character_re]
      by_cases h : d i = d j
      · simp [h]
      · simp [sub_ne_zero.mpr (Ne.symm h), h]
    · intro j _
      exact (continuous_const.mul (Complex.continuous_re.comp (character (d j - d i)).continuous)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  · intro i _
    exact (by fun_prop : Continuous (fun θ : FrequencyCircle =>
      ∑ j, inner ℝ (u i) (u j) * (character (d j - d i) θ).re)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

/-- Article: Parseval for a finite sequence with distinct integer indices. -/
theorem integral_fourierGram_of_injective (d : I → ℤ) (hd : Function.Injective d)
    (u : I → E) :
    (∫ θ : FrequencyCircle, fourierGram d u θ ∂AddCircle.haarAddCircle) =
      ∑ i, ‖u i‖ ^ 2 := by
  classical
  rw [integral_fourierGram]
  apply Finset.sum_congr rfl
  intro i _
  simp [hd.eq_iff]

/-- Article: Fourier multiplication extracts precisely a finite autocorrelation.
Use: the exact quadratic-symbol identity for arbitrary Hilbert-valued finite sequences.
Proof: real-character orthogonality and symmetry of the Gram coefficients. -/
theorem integral_character_mul_fourierGram (d : I → ℤ) (u : I → E) (n : ℤ) :
    (∫ θ : FrequencyCircle, (character n θ).re * fourierGram d u θ
      ∂AddCircle.haarAddCircle) = integerCorrelation d u n := by
  classical
  have hexpand : (∫ θ : FrequencyCircle, (character n θ).re * fourierGram d u θ
      ∂AddCircle.haarAddCircle) =
      ∑ i, ∑ j, inner ℝ (u i) (u j) *
        (((if n + (d j - d i) = 0 then 1 else 0) +
          (if n - (d j - d i) = 0 then 1 else 0)) / 2) := by
    unfold fourierGram
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro j _
        simp_rw [show ∀ θ : FrequencyCircle,
            (character n θ).re * (inner ℝ (u i) (u j) *
              (character (d j - d i) θ).re) =
            inner ℝ (u i) (u j) * ((character n θ).re *
              (character (d j - d i) θ).re) by intro θ; ring]
        rw [integral_const_mul, integral_character_re_mul_re]
      · intro j _
        exact (by fun_prop : Continuous (fun θ : FrequencyCircle =>
          (character n θ).re * (inner ℝ (u i) (u j) *
            (character (d j-d i) θ).re))).integrable_of_hasCompactSupport
              (HasCompactSupport.of_compactSpace _)
    · intro i _
      exact (by fun_prop : Continuous (fun θ : FrequencyCircle =>
        ∑ j, (character n θ).re * (inner ℝ (u i) (u j) *
          (character (d j-d i) θ).re))).integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _)
  rw [hexpand]
  have hpoint (i j : I) : inner ℝ (u i) (u j) *
      (((if n + (d j - d i) = 0 then 1 else 0) +
        (if n - (d j - d i) = 0 then 1 else 0)) / 2) =
      ((if d j-d i = -n then inner ℝ (u i) (u j) else 0) +
       (if d j-d i = n then inner ℝ (u i) (u j) else 0)) / 2 := by
    simp only [show n + (d j-d i) = 0 ↔ d j-d i = -n by omega,
      show n - (d j-d i) = 0 ↔ d j-d i = n by omega]
    split_ifs <;> ring
  simp only [hpoint, ← Finset.sum_div, Finset.sum_add_distrib]
  change (integerCorrelation d u (-n) + integerCorrelation d u n) / 2 = _
  rw [integerCorrelation_neg]
  ring

/-- Article: symbol of a finite real matrix of shift coefficients. -/
def quadraticSymbol {J : Type*} [Fintype J] (r : J → ℤ) (q : J → J → ℝ)
    (θ : FrequencyCircle) : ℝ :=
  ∑ a, ∑ b, q a b * (character (r b-r a) θ).re

/-- Article: finite Hilbert Parseval for a complete finite quadratic symbol.
Proof: integrate each coefficient against the Gram polynomial and extract its autocorrelation. -/
theorem integral_quadraticSymbol_mul_fourierGram {J : Type*} [Fintype J]
    (r : J → ℤ) (q : J → J → ℝ) (d : I → ℤ) (u : I → E) :
    (∫ θ : FrequencyCircle, quadraticSymbol r q θ * fourierGram d u θ
      ∂AddCircle.haarAddCircle) =
      ∑ a, ∑ b, q a b * integerCorrelation d u (r b-r a) := by
  unfold quadraticSymbol
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro a _
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro b _
      simp_rw [mul_assoc]
      rw [integral_const_mul, integral_character_mul_fourierGram]
    · intro b _
      exact ((continuous_const.mul (Complex.continuous_re.comp
        (character (r b-r a)).continuous)).mul
        (continuous_fourierGram d u)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
  · intro a _
    exact (continuous_finsetSum _ (fun b _ =>
      (continuous_const.mul (Complex.continuous_re.comp
        (character (r b-r a)).continuous)).mul
        (continuous_fourierGram d u))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

/-- Article: multiplication by a strictly negative scalar symbol.
Use: exact strict gap for every finite Hilbert Fourier sum.
Proof: pointwise nonnegativity and finite Hilbert Parseval. -/
theorem integral_symbol_mul_fourierGram_le (d : I → ℤ) (hd : Function.Injective d)
    (u : I → E) {φ : FrequencyCircle → ℝ} (hφ : Continuous φ) {ε : ℝ}
    (hneg : ∀ θ, φ θ ≤ -ε) :
    (∫ θ : FrequencyCircle, φ θ * fourierGram d u θ ∂AddCircle.haarAddCircle) ≤
      -ε * ∑ i, ‖u i‖ ^ 2 := by
  have hG := continuous_fourierGram d u
  have h := integral_mono (μ := AddCircle.haarAddCircle)
    ((hφ.mul hG).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    ((continuous_const.mul hG).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (fun θ => mul_le_mul_of_nonneg_right (hneg θ) (fourierGram_nonneg d u θ))
  change (∫ θ, φ θ * fourierGram d u θ ∂AddCircle.haarAddCircle) ≤
    ∫ θ, -ε * fourierGram d u θ ∂AddCircle.haarAddCircle at h
  rwa [integral_const_mul, integral_fourierGram_of_injective d hd u] at h

/-- Article: Parseval's negative quadratic estimate for every finite Hilbert sequence.
Use: this is the finite-frequency inequality before cutting off an actual segment.
Proof: identify the entire quadratic integral, then apply the strict symbol gap. -/
theorem quadraticCorrelation_le_of_symbol {J : Type*} [Fintype J]
    (r : J → ℤ) (q : J → J → ℝ) (d : I → ℤ) (hd : Function.Injective d)
    (u : I → E) {ε : ℝ} (hneg : ∀ θ, quadraticSymbol r q θ ≤ -ε) :
    (∑ a, ∑ b, q a b * integerCorrelation d u (r b-r a)) ≤
      -ε * ∑ i, ‖u i‖ ^ 2 := by
  rw [← integral_quadraticSymbol_mul_fourierGram r q d u]
  apply integral_symbol_mul_fourierGram_le d hd u _ hneg
  unfold quadraticSymbol
  exact continuous_finsetSum _ (fun a _ => continuous_finsetSum _ (fun b _ =>
    continuous_const.mul (Complex.continuous_re.comp (character (r b-r a)).continuous)))

end polyak.Energy
