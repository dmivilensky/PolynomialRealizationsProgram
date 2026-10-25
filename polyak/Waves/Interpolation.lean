import polyak.Waves.Mixture
import polyak.Interpolation.Extension

/-!
Article: Lemma spectralinterp, its full interpolation equivalence.
Use: general probability spectra, including nonatomic spectra, define one actual
normalized potential on their real L² Hilbert space for the entire infinite wave.
Proof: all ordered interpolation pairs reduce to the exact positive-factor lag
and minimizer identities; arbitrary-set Hilbert interpolation supplies the function.
-/

noncomputable section

namespace polyak.Waves

open Interpolation Spectral

/-- Article: (feasible), for an arbitrary continuous planar multiplier.
Use: spectral feasibility with all infinitely many lags and the minimizer pair. -/
def MixtureFeasible (ν : Spectrum) (m : C(Frequency, ℂ)) (C t : ℝ) : Prop :=
  |C| ≤ spectrumG ν m ∧ ∀ n : ℕ, 1 ≤ n →
    0 ≤ spectrumA ν m t n - spectrumB ν m n + C * Real.sinh (n * t) ∧
    0 ≤ spectrumA ν m t n + spectrumB ν m n - C * Real.sinh (n * t)

/-- Article: the datum of the minimizer. Proof: lift the zero continuous position. -/
@[simp] theorem mixturePosition_none (ν : Spectrum) (t : ℝ) :
    mixturePosition ν t none = 0 := by
  have he : positionMap t none = 0 := by ext c; rfl
  simp [mixturePosition, he]

/-- Article: the minimizer's gradient datum. Proof: lift the zero continuous gradient. -/
@[simp] theorem mixtureGradient_none (ν : Spectrum) (m : C(Frequency, ℂ)) (t : ℝ) :
    mixtureGradient ν m t none = 0 := by
  have he : gradientMap m t none = 0 := by ext c; simp [gradientMap, positionMap, position]
  simp [mixtureGradient, he]

/-- Article: the minimizer's value datum. Proof: integrate its zero value. -/
@[simp] theorem mixtureValue_none (ν : Spectrum) (m : C(Frequency, ℂ)) (C t : ℝ) :
    mixtureValue ν m C t none = 0 := by
  simp [mixtureValue, valueMap, value]

/-- Article: the two signs in (waveslacks). Proof: the standard absolute-value inequality. -/
theorem abs_le_iff_signed_slacks (T R : ℝ) : |T| ≤ R ↔ 0 ≤ R + T ∧ 0 ≤ R - T := by
  rw [abs_le]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

/-- Article: reversal of interpolation endpoints. Proof: R is symmetric and T antisymmetric. -/
theorem pair_bound_reverse {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x σ : I → E) (values : I → ℝ) (i j : I) :
    |datumT x σ values i j| ≤ datumR x σ i j ↔
      |datumT x σ values j i| ≤ datumR x σ j i := by
  rw [datumT_antisymm x σ values i j, datumR_symm x σ j i, abs_neg]

/-- Article: necessity of all spectral slacks. Proof: apply interpolation to the
minimizer pair and to lag n starting at zero, then cancel positive exponential factors. -/
theorem mixtureFeasible_of_tableFeasible (ν : Spectrum) (m : C(Frequency, ℂ)) (C t : ℝ)
    (h : TableFeasible (mixturePosition ν t) (mixtureGradient ν m t) (mixtureValue ν m C t)) :
    MixtureFeasible ν m C t := by
  have hstar := (abs_le_iff_signed_slacks _ _).mp (h none (some 0))
  have hspos := mixture_star_slack ν m C t 1 0
  have hsneg := mixture_star_slack ν m C t (-1) 0
  norm_num at hspos hsneg
  refine ⟨abs_le.mpr ⟨by linarith [hstar.1, hstar.2], by linarith [hstar.1, hstar.2]⟩, ?_⟩
  intro n _
  have hlag := (abs_le_iff_signed_slacks _ _).mp (h (some 0) (some n))
  have hlpos := mixture_slack ν m C t 1 0 n
  have hlneg := mixture_slack ν m C t (-1) 0 n
  simp only [Nat.cast_zero, mul_zero, zero_add, one_mul, neg_one_mul, sub_neg_eq_add] at hlpos hlneg
  have hpos : 0 < (1 / 2 : ℝ) * Real.exp (n * t) := by positivity
  constructor
  · apply (mul_nonneg_iff_of_pos_left hpos).mp
    linarith [hlag.1]
  · apply (mul_nonneg_iff_of_pos_left hpos).mp
    linarith [hlag.2]

/-- Article: sufficiency of the minimizer spectral constraint. Proof: both signed
slacks are a strictly positive multiple of ḡ±C. -/
theorem MixtureFeasible.star_bound {ν : Spectrum} {m : C(Frequency, ℂ)} {C t : ℝ}
    (h : MixtureFeasible ν m C t) (j : ℕ) :
    |datumT (mixturePosition ν t) (mixtureGradient ν m t) (mixtureValue ν m C t)
      none (some j)| ≤ datumR (mixturePosition ν t) (mixtureGradient ν m t) none (some j) := by
  rw [abs_le_iff_signed_slacks]
  have hC := abs_le.mp h.1
  have hpos := mixture_star_slack ν m C t 1 j
  have hneg := mixture_star_slack ν m C t (-1) j
  simp only [one_mul, neg_one_mul] at hpos hneg
  constructor
  · rw [hpos]
    exact mul_nonneg (by positivity) (by linarith)
  · have he : datumR (mixturePosition ν t) (mixtureGradient ν m t) none (some j) -
        datumT (mixturePosition ν t) (mixtureGradient ν m t) (mixtureValue ν m C t)
          none (some j) = (1 / 4 : ℝ) * Real.exp (2 * j * t) * (spectrumG ν m - C) := by
      linarith [hneg]
    rw [he]
    exact mul_nonneg (by positivity) (by linarith)

/-- Article: sufficiency of each lag constraint. Proof: use the exact signed lag
formula for positive lag, and the identical-endpoint identity for zero lag. -/
theorem MixtureFeasible.lag_bound {ν : Spectrum} {m : C(Frequency, ℂ)} {C t : ℝ}
    (h : MixtureFeasible ν m C t) (j n : ℕ) :
    |datumT (mixturePosition ν t) (mixtureGradient ν m t) (mixtureValue ν m C t)
      (some j) (some (j + n))| ≤
      datumR (mixturePosition ν t) (mixtureGradient ν m t) (some j) (some (j + n)) := by
  by_cases hn : n = 0
  · subst n
    simp [datumT, datumR]
  · have hn' : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    obtain ⟨hl, hu⟩ := h.2 n hn'
    rw [abs_le_iff_signed_slacks]
    have hpos := mixture_slack ν m C t 1 j n
    have hneg := mixture_slack ν m C t (-1) j n
    simp only [one_mul, neg_one_mul, sub_neg_eq_add] at hpos hneg
    constructor
    · rw [hpos]
      exact mul_nonneg (by positivity) hl
    · have he : datumR (mixturePosition ν t) (mixtureGradient ν m t)
          (some j) (some (j + n)) - datumT (mixturePosition ν t) (mixtureGradient ν m t)
            (mixtureValue ν m C t) (some j) (some (j + n)) =
          (1 / 2 : ℝ) * Real.exp ((2 * j + n) * t) *
            (spectrumA ν m t n + spectrumB ν m n - C * Real.sinh (n * t)) := by
        linarith [hneg]
      rw [he]
      exact mul_nonneg (by positivity) hu

/-- Article: Lemma spectralinterp, all interpolation pairs.
Use: exact equivalence with infinite spectral feasibility, including reversed pairs.
Proof: order any two time indices and reduce to a nonnegative lag. -/
theorem mixture_tableFeasible_iff (ν : Spectrum) (m : C(Frequency, ℂ)) (C t : ℝ) :
    TableFeasible (mixturePosition ν t) (mixtureGradient ν m t) (mixtureValue ν m C t) ↔
      MixtureFeasible ν m C t := by
  constructor
  · exact mixtureFeasible_of_tableFeasible ν m C t
  · intro h i k
    cases i with
    | none =>
      cases k with
      | none => simp [datumT, datumR]
      | some k => exact h.star_bound k
    | some j =>
      cases k with
      | none =>
        apply (pair_bound_reverse _ _ _ (some j) none).mpr
        exact h.star_bound j
      | some k =>
        rcases le_total j k with hjk | hkj
        · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hjk
          exact h.lag_bound j n
        · apply (pair_bound_reverse _ _ _ (some j) (some k)).mpr
          obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hkj
          exact h.lag_bound k n

/-- Article: Lemma spectralinterp, actual function realization.
Use: one genuine function realizes the entire wave table for an arbitrary probability measure.
Proof: the origin datum and arbitrary-set interpolation, followed by the exact slack equivalence. -/
theorem mixture_interpolation_iff (ν : Spectrum) (m : C(Frequency, ℂ)) (C t : ℝ) :
    (∃ ψ : WaveSpace ν → ℝ, polyak.NormalizedSmooth ψ ∧ ∀ i,
      ψ (mixturePosition ν t i) = mixtureValue ν m C t i ∧
        _root_.gradient ψ (mixturePosition ν t i) = mixtureGradient ν m t i) ↔
      MixtureFeasible ν m C t := by
  exact (interpolation_iff none (mixturePosition_none ν t) (mixtureGradient_none ν m t)
    (mixtureValue_none ν m C t)).trans (mixture_tableFeasible_iff ν m C t)

end polyak.Waves
