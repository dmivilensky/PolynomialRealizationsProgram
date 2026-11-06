import nesterov.Spectral.Finite

/-!
Article: Lemma D.2 (`lem:split`), exact per-atom splitting before any limit.
Use: one common value charge converts all lags to the continuous flow kernels.
-/
namespace nesterov.Slow
noncomputable section
open Spectral
open scoped BigOperators NNReal
variable {J : Type*} [Fintype J]

def splitCharge (w : J→ℝ≥0) (c : J→Frequency) (a : SymbolPair) (t : ℝ) : ℝ :=
  (∑ j,(w j:ℝ)*(2*skew a (c j)*Real.arccos (c j)))/t

theorem meanG_finite (w : J→ℝ≥0) (c : J→Frequency) (hw : ∑ j,w j=1) (a : SymbolPair) :
    meanG (finiteSpectrum w c hw) a=∑ j,(w j:ℝ)*g a (c j) := by
  simp only [meanG,polyak.Waves.finiteSpectrum_integral]

theorem meanA_finite (w : J→ℝ≥0) (c : J→Frequency) (hw : ∑ j,w j=1)
    (a : SymbolPair) (t : ℝ) (n : ℕ) :
    meanA (finiteSpectrum w c hw) a t n=∑ j,(w j:ℝ)*lagA a t n (c j) := by
  simp only [meanA,polyak.Waves.finiteSpectrum_integral]

theorem meanB_finite (w : J→ℝ≥0) (c : J→Frequency) (hw : ∑ j,w j=1)
    (a : SymbolPair) (n : ℕ) :
    meanB (finiteSpectrum w c hw) a n=∑ j,(w j:ℝ)*lagB a n (c j) := by
  simp only [meanB,polyak.Waves.finiteSpectrum_integral]

theorem split_slacks (w : J→ℝ≥0) (c : J→Frequency) (hw : ∑ j,w j=1)
    (a : SymbolPair) {t : ℝ} (ht : t<0) (n : ℕ) :
    meanA (finiteSpectrum w c hw) a t n-meanB (finiteSpectrum w c hw) a n+
      splitCharge w c a t*Real.sinh (n*t)=
        ∑ j,(w j:ℝ)*(g a (c j)*(Real.cosh (n*t)-Real.cos (n*Real.arccos (c j)))+
          2*skew a (c j)*(Real.arccos (c j)*Real.sinh (n*|t|)/|t|-Real.sin (n*Real.arccos (c j)))) ∧
    meanA (finiteSpectrum w c hw) a t n+meanB (finiteSpectrum w c hw) a n-
      splitCharge w c a t*Real.sinh (n*t)=
        ∑ j,(w j:ℝ)*(g a (c j)*(Real.cosh (n*t)-Real.cos (n*Real.arccos (c j)))-
          2*skew a (c j)*(Real.arccos (c j)*Real.sinh (n*|t|)/|t|-Real.sin (n*Real.arccos (c j)))) := by
  rw [meanA_finite,meanB_finite]
  unfold splitCharge
  rw [Finset.sum_div,Finset.sum_mul]
  simp only [abs_of_neg ht,mul_neg,Real.sinh_neg,neg_div_neg_eq]
  simp only [←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
  constructor
  · apply Finset.sum_congr rfl
    intro j _
    dsimp [lagA,lagB]
    ring
  · apply Finset.sum_congr rfl
    intro j _
    dsimp [lagA,lagB]
    ring

theorem split_minimizer_iff (w : J→ℝ≥0) (c : J→Frequency) (hw : ∑ j,w j=1)
    (a : SymbolPair) {t : ℝ} (ht : t<0) :
    |splitCharge w c a t|≤meanG (finiteSpectrum w c hw) a ↔
      |∑ j,(w j:ℝ)*(skew a (c j)*Real.arccos (c j))|≤
        |t|/2*meanG (finiteSpectrum w c hw) a := by
  have ht0 : 0 < |t| := abs_pos.mpr (ne_of_lt ht)
  have he : (∑ j,(w j:ℝ)*(2*skew a (c j)*Real.arccos (c j)))=
      2*∑ j,(w j:ℝ)*(skew a (c j)*Real.arccos (c j)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  unfold splitCharge
  rw [he,abs_div,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2),div_le_iff₀ ht0]
  constructor <;> intro h <;> nlinarith

end
end nesterov.Slow
