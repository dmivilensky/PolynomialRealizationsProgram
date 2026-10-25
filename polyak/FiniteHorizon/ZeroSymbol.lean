import polyak.FiniteHorizon.Telescoping
import polyak.Energy.Fourier

/-!
Article: Appendix C, zero-symbol diagonal rows in Lemma telescoping.
Use: Fourier orthogonality forces every finite cosine coefficient to vanish,
so the explicitly constructed row primitive applies to every Hilbert sequence.
-/
noncomputable section
namespace polyak.FiniteHorizon
open Energy MeasureTheory
open scoped BigOperators
local instance : Fact (0<2*Real.pi) := ⟨Real.two_pi_pos⟩

/-- Every coefficient of an identically zero finite cosine polynomial is zero. -/
theorem cosine_coefficients_zero {N : ℕ} (m : Fin N → ℝ)
    (hz : ∀ θ : FrequencyCircle, ∑ i, m i*(character (i : ℤ) θ).re=0) :
    ∀ k, m k=0 := by
  classical
  intro k
  have hi : (∫ θ : FrequencyCircle,
      (∑ i, m i*(character (i : ℤ) θ).re)*(character (k : ℤ) θ).re
      ∂AddCircle.haarAddCircle)=0 := by
    simp_rw [hz,zero_mul]
    simp
  simp_rw [Finset.sum_mul,mul_assoc] at hi
  rw [integral_finsetSum] at hi
  · simp_rw [integral_const_mul,integral_character_re_mul_re] at hi
    rw [Finset.sum_eq_single k] at hi
    · by_cases hk : (k : ℤ)=0
      · simpa [hk] using hi
      · have hs : (k : ℤ)+(k : ℤ)≠0 := by omega
        simp only [hs,ite_false,sub_self,ite_true,zero_add] at hi
        linarith
    · intro i _ hik
      have hd : (i : ℤ)-(k : ℤ)≠0 := by
        intro h
        apply hik
        apply Fin.ext
        have he := sub_eq_zero.mp h
        exact_mod_cast he
      have hs : (i : ℤ)+(k : ℤ)≠0 := by
        intro h
        have he : i.val=k.val := by omega
        exact hik (Fin.ext he)
      simp only [hs,hd,ite_false,zero_add,zero_div,mul_zero]
    · intro hk
      exact (hk (Finset.mem_univ k)).elim
  · intro i _
    exact (((Complex.continuous_re.comp (character (i : ℤ)).continuous).mul
      (Complex.continuous_re.comp (character (k : ℤ)).continuous)).const_mul (m i)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The exact cosine symbol of triangular coefficient rows. -/
def rowSymbol (D : ℕ) (μ : ℕ → ℕ → ℝ) (θ : FrequencyCircle) : ℝ :=
  ∑ e : Fin (D+1), (∑ a ∈ Finset.range (D-e.val+1), μ e.val a)*
    (character (e : ℤ) θ).re

/-- A zero symbol has a zero sum on every diagonal row. -/
theorem row_sums_zero_of_symbol (D : ℕ) (μ : ℕ → ℕ → ℝ)
    (hz : ∀ θ, rowSymbol D μ θ=0) :
    ∀ e≤D, ∑ a ∈ Finset.range (D-e+1), μ e a=0 := by
  intro e he
  exact cosine_coefficients_zero (fun i : Fin (D+1) =>
    ∑ a ∈ Finset.range (D-i.val+1), μ i.val a) hz ⟨e,by omega⟩

/-- An identically zero symbol and zero value charge yield an exact local primitive. -/
theorem zero_symbol_telescoping {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (D : ℕ) (μ : ℕ → ℕ → ℝ) (d : ℕ → ℝ)
    (hz : ∀ θ, rowSymbol D μ θ=0) (hd : ∑ a ∈ Finset.range (D+1), d a=0)
    (f : ℤ → E) (h : ℤ → ℝ) (j : ℤ) :
    rowFunctional D μ d f h j=rowPrimitive D μ d f h (j+1)-rowPrimitive D μ d f h j :=
  rowFunctional_telescoping D μ d (row_sums_zero_of_symbol D μ hz) hd f h j

end polyak.FiniteHorizon
