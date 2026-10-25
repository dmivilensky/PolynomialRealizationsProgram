import polyak.ModeLocking.Localization.Shift

/-! A finite relaxation has a normalized finite nonpositive symbol at its
actual attained threshold. No limiting or omitted coefficients are assumptions. -/
noncomputable section
namespace polyak.ModeLocking.Localization
open Levels MeasureTheory Set
open scoped BigOperators

theorem finite_threshold_symbol (q : General.Tuning) (N : Finset ℤ)
    (hN : (N : Set ℤ) ⊆ nonzeroLags) :
    ∃ a : {n // n ∈ N} → ℝ, ∃ γ : ℝ,
      (∀ i, 0 ≤ a i) ∧ 0 ≤ γ ∧ (∑ i, a i) + γ = 1 ∧
      ∀ ω, symbol q (Threshold.sigmaOn q N) (fun i => i.val) a γ ω ≤ 0 := by
  classical
  obtain ⟨S⟩ := Global.Symbols.limit_symbol_at_sigmaOn q (N : Set ℤ) hN
  have hout (n : ℤ) (hn : n ∉ N) : S.weights.weight n = 0 := S.weights.outside n hn
  have hsum : (∑' n, S.weights.weight n) = ∑ n ∈ N, S.weights.weight n :=
    tsum_eq_sum hout
  refine ⟨fun i => S.weights.weight i, S.weights.gamma,
    fun i => S.weights.nonneg i, S.weights.gamma_nonneg, ?_, ?_⟩
  · rw [Finset.sum_coe_sort N, ← hsum]
    exact S.weights.normalized
  · intro ω
    have heval : S.weights.eval (Geometry.shiftedCurve q (Threshold.sigmaOn q N)) ω =
        symbol q (Threshold.sigmaOn q N) (fun i : {n // n ∈ N} => i.val)
          (fun i => S.weights.weight i) S.weights.gamma ω := by
      unfold Global.Symbols.Weights.eval Global.Symbols.Weights.series symbol
      rw [tsum_eq_sum (s := N) (fun n hn => by rw [hout n hn, zero_mul])]
      congr 1
      exact (Finset.sum_coe_sort N (fun n : ℤ => S.weights.weight n *
        (Geometry.shiftedCurve q (Threshold.sigmaOn q N)).lag n ω)).symm
    rw [← heval]
    exact S.nonpos ω

end polyak.ModeLocking.Localization
