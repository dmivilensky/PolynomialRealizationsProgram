import polyak.Duality.Separation
import nesterov.Duality.FiniteMemory

/-!
Article: spectralgeneral(a), the complete finite strict certificate alternative.
Use: general continuous multipliers, including the genuine arbitrary-tuning multiplier.
Proof: compactness supplies finite lag memory and finite-dimensional separation
supplies nonnegative weights whose unrestricted value coefficient cancels exactly.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace nesterov.Duality

open Spectral

abbrev ConstraintIndex := polyak.Duality.ConstraintIndex

/-- Article: the C-free part of each finite interpolation constraint. -/
def constraintMap (m : SymbolPair) (t : ℝ) (lags : Finset ℕ) :
    ConstraintIndex lags → C(Frequency, ℝ)
  | .inl _ => ⟨g m, by unfold g; fun_prop⟩
  | .inr (n, false) => ⟨fun c => lagA m t n c - lagB m n c, by unfold lagA lagB g skew; fun_prop⟩
  | .inr (n, true) => ⟨fun c => lagA m t n c + lagB m n c, by unfold lagA lagB g skew; fun_prop⟩

abbrev constraintCharge := polyak.Duality.constraintCharge
abbrev lagWeight := polyak.Duality.lagWeight
abbrev lagWeight_mem := polyak.Duality.lagWeight_mem

/-- Article: finite splitting of the C-free certificate symbol.
Proof: sum over the two minimizer signs and then over the two signs of each lag. -/
theorem sum_constraintMap (m : SymbolPair) (t : ℝ) (lags : Finset ℕ)
    (w : ConstraintIndex lags → ℝ) (c : Frequency) :
    (∑ i, w i * constraintMap m t lags i c) =
      symbol m t lags (lagWeight lags w false) (lagWeight lags w true)
        (w (.inl false)) (w (.inl true)) c := by
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, constraintMap, ContinuousMap.coe_mk]
  unfold symbol
  rw [← Finset.sum_coe_sort lags]
  have hw (n : {n // n ∈ lags}) (sign : Bool) :
      lagWeight lags w sign n = w (.inr (n, sign)) :=
    lagWeight_mem _ _ _ _ n.property
  simp only [hw]
  have heq : (∑ n : {n // n ∈ lags},
      (w (.inr (n, true)) * (lagA m t n c + lagB m n c) +
        w (.inr (n, false)) * (lagA m t n c - lagB m n c))) =
      ∑ n : {n // n ∈ lags},
        (w (.inr (n, false)) * (lagA m t n c - lagB m n c) +
          w (.inr (n, true)) * (lagA m t n c + lagB m n c)) := by
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [heq]
  ring

abbrev sum_constraintCharge := polyak.Duality.sum_constraintCharge

/-- Article: a finite primal system is exactly the indicated signed interpolation inequalities. -/
theorem finite_constraints_iff (m : SymbolPair) (t : ℝ) (M : ℕ)
    (ν : Spectrum) (C : ℝ) :
    (∀ i : ConstraintIndex (Finset.Icc 1 M),
      0 ≤ (∫ c, constraintMap m t (Finset.Icc 1 M) i c ∂ν) +
        constraintCharge t (Finset.Icc 1 M) i * C) ↔ FiniteFeasible m t M ν C := by
  constructor
  · intro h
    have hp := h (.inl false)
    have hm := h (.inl true)
    change 0 ≤ meanG ν m + 1 * C at hp
    change 0 ≤ meanG ν m + (-1) * C at hm
    refine ⟨abs_le.mpr ⟨by linarith, by linarith⟩, fun n hn hM => ?_⟩
    have hmem : n ∈ Finset.Icc 1 M := Finset.mem_Icc.mpr ⟨hn, hM⟩
    have hl := h (.inr (⟨n, hmem⟩, false))
    have hu := h (.inr (⟨n, hmem⟩, true))
    have ha : Integrable (lagA m t n) (ν : Measure Frequency) :=
      polyak.Spectral.integrable_continuous ν (by unfold lagA g; fun_prop)
    have hb : Integrable (lagB m n) (ν : Measure Frequency) :=
      polyak.Spectral.integrable_continuous ν (by unfold lagB skew; fun_prop)
    change 0 ≤ (∫ c, lagA m t n c - lagB m n c ∂ν) + Real.sinh (n * t) * C at hl
    change 0 ≤ (∫ c, lagA m t n c + lagB m n c ∂ν) + (-Real.sinh (n * t)) * C at hu
    rw [integral_sub ha hb] at hl
    rw [integral_add ha hb] at hu
    constructor
    · simpa [lagA, lagB, g, meanA, meanB, mul_comm] using hl
    · simpa [lagA, lagB, g, meanA, meanB, sub_eq_add_neg, mul_comm] using hu
  · intro h i
    rcases i with sign | ⟨n, sign⟩
    · cases sign <;> change 0 ≤ meanG ν m + _ * C <;>
        simp only [constraintCharge, polyak.Duality.constraintCharge, one_mul, neg_one_mul] <;>
        nlinarith [abs_le.mp h.1 |>.1, abs_le.mp h.1 |>.2]
    · have hn := Finset.mem_Icc.mp n.property
      have hl := h.2 n hn.1 hn.2
      have ha : Integrable (lagA m t n) (ν : Measure Frequency) :=
        polyak.Spectral.integrable_continuous ν (by unfold lagA g; fun_prop)
      have hb : Integrable (lagB m n) (ν : Measure Frequency) :=
        polyak.Spectral.integrable_continuous ν (by unfold lagB skew; fun_prop)
      cases sign
      · change 0 ≤ (∫ c, lagA m t n c - lagB m n c ∂ν) + Real.sinh (n.val * t) * C
        rw [integral_sub ha hb]
        simpa [lagA, lagB, g, meanA, meanB, mul_comm] using hl.1
      · change 0 ≤ (∫ c, lagA m t n c + lagB m n c ∂ν) + (-Real.sinh (n.val * t)) * C
        rw [integral_add ha hb]
        simpa [lagA, lagB, g, meanA, meanB, sub_eq_add_neg, mul_comm] using hl.2

/-- Article: infeasibility of finite memory produces a concrete finite strict certificate.
Proof: apply the proved finite strict alternative and split its recovered multipliers. -/
theorem strictCertificate_of_finite_infeasible (m : SymbolPair) (t : ℝ) (M : ℕ)
    (h : ¬ ∃ (ν : Spectrum) (C : ℝ), FiniteFeasible m t M ν C) :
    Nonempty (StrictCertificate m t) := by
  have hi : ¬ ∃ (ν : Spectrum) (C : ℝ),
      ∀ i : ConstraintIndex (Finset.Icc 1 M),
        0 ≤ (∫ c, constraintMap m t (Finset.Icc 1 M) i c ∂ν) +
          constraintCharge t (Finset.Icc 1 M) i * C := by
    rintro ⟨ν, C, hp⟩
    exact h ⟨ν, C, (finite_constraints_iff m t M ν C).mp hp⟩
  obtain ⟨w, ε, hw, hε, hcancel, hstrict⟩ := polyak.Duality.finite_strict_alternative
    (constraintMap m t (Finset.Icc 1 M)) (constraintCharge t (Finset.Icc 1 M))
    (.inl false) (by norm_num [constraintCharge, polyak.Duality.constraintCharge]) hi
  refine ⟨{
    lags := Finset.Icc 1 M
    positive_lag := fun n hn => (Finset.mem_Icc.mp hn).1
    α := lagWeight (Finset.Icc 1 M) w false
    β := lagWeight (Finset.Icc 1 M) w true
    α_nonneg := ?_
    β_nonneg := ?_
    γplus := w (.inl false)
    γminus := w (.inl true)
    γplus_nonneg := hw _
    γminus_nonneg := hw _
    ε := ε
    ε_pos := hε
    cancel := ?_
    strict := ?_ }⟩
  · intro n hn
    change 0 ≤ polyak.Duality.lagWeight _ _ _ _
    rw [polyak.Duality.lagWeight_mem _ _ _ _ hn]
    exact hw _
  · intro n hn
    change 0 ≤ polyak.Duality.lagWeight _ _ _ _
    rw [polyak.Duality.lagWeight_mem _ _ _ _ hn]
    exact hw _
  · rw [← sum_constraintCharge]
    exact hcancel
  · intro c
    rw [← sum_constraintMap]
    exact hstrict c

/-- Article: spectralgeneral(a), for every continuous multiplier and every real exponent.
Proof: compact finite-lag reduction followed by actual strict separation; integration proves converse. -/
theorem infeasible_iff_strictCertificate (m : SymbolPair) (t : ℝ) :
    (¬ ∃ (ν : Spectrum) (C : ℝ), Feasible m t ν C) ↔
      Nonempty (StrictCertificate m t) := by
  constructor
  · intro h
    obtain ⟨M, hM⟩ := exists_infeasible_finite m t h
    exact strictCertificate_of_finite_infeasible m t M hM
  · rintro ⟨cert⟩ ⟨ν, C, h⟩
    exact cert.not_feasible ν C h

/-- Article: the finite-memory strict alternative with a kernel equality.
Use: Appendix C, separation inside the zero set of a linear stationary functional.
Proof: the proved equality alternative, with the actual signed interpolation constraints. -/
theorem finiteMemory_equality_alternative (m : SymbolPair) (t : ℝ) (M : ℕ)
    (e : C(Frequency, ℝ))
    (h : ¬ ∃ (ν : Spectrum) (C : ℝ),
      FiniteFeasible m t M ν C ∧ (∫ c, e c ∂ν) = 0) :
    ∃ (w : ConstraintIndex (Finset.Icc 1 M) → ℝ) (θ ε : ℝ),
      (∀ i, 0 ≤ w i) ∧ 0 < ε ∧
      ((∑ n ∈ Finset.Icc 1 M,
        (lagWeight (Finset.Icc 1 M) w false n - lagWeight (Finset.Icc 1 M) w true n) *
          Real.sinh (n * t)) + w (.inl false) - w (.inl true) = 0) ∧
      ∀ c, symbol m t (Finset.Icc 1 M)
        (lagWeight (Finset.Icc 1 M) w false) (lagWeight (Finset.Icc 1 M) w true)
          (w (.inl false)) (w (.inl true)) c + θ * e c ≤ -ε := by
  have hi : ¬ ∃ (ν : Spectrum) (C : ℝ),
      (∀ i : ConstraintIndex (Finset.Icc 1 M),
        0 ≤ (∫ c, constraintMap m t (Finset.Icc 1 M) i c ∂ν) +
          constraintCharge t (Finset.Icc 1 M) i * C) ∧ (∫ c, e c ∂ν) = 0 := by
    rintro ⟨ν, C, hp, he⟩
    exact h ⟨ν, C, (finite_constraints_iff m t M ν C).mp hp, he⟩
  obtain ⟨w, θ, ε, hw, hε, hc, hs⟩ := polyak.Duality.finite_strict_alternative_equality
    (constraintMap m t (Finset.Icc 1 M)) (constraintCharge t (Finset.Icc 1 M))
    (.inl false) (by norm_num [constraintCharge, polyak.Duality.constraintCharge]) e hi
  refine ⟨w, θ, ε, hw, hε, ?_, ?_⟩
  · rw [← sum_constraintCharge]
    exact hc
  · intro c
    rw [← sum_constraintMap]
    exact hs c

end nesterov.Duality
