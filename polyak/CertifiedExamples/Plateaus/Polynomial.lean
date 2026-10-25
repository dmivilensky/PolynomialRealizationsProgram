import polyak.ModeLocking.TwoLag.ContactExtension
import polyak.Farey.Certificates.Polynomial

/-! An independent polynomial semantics for the selected plateau certificates.
The exporter supplies rational boxes and finite covers.  It does not supply
the lag functions, their polynomial interpretation, or their sign semantics. -/
noncomputable section
namespace polyak.CertifiedExamples.Plateaus
open General Levels Set Filter
open scoped BigOperators Topology

def dividedLag (q : Tuning) (n : ℤ) (c : ℝ) : ℝ :=
  q.Xi c * ModeLocking.TwoLag.W n.natAbs c -
    (n.sign : ℝ) * (1+c) * Spectral.chebU (n.natAbs-1) c

def polynomialSymbol (q : Tuning) (N : Finset ℤ) (a : ℤ → ℝ) (c : ℝ) : ℝ :=
  ∑ n ∈ N, a n * dividedLag q n c

theorem signedLag_divided (q : Tuning) (n : ℤ) (c : ℝ) :
    Farey.Certificates.signedLagPolynomial q n c = (1-c)*dividedLag q n c := by
  have h := ModeLocking.TwoLag.W_identity n.natAbs c
  unfold Farey.Certificates.signedLagPolynomial dividedLag
  rw [← h]
  ring

theorem polynomial_factor (q : Tuning) (N : Finset ℤ) (a : ℤ → ℝ)
    (hn : ∀ n ∈ N, n ≠ 0) (ω : Frequency)
    (hω : 0 < (ω : ℝ) ∧ (ω : ℝ) < Real.pi) :
    ModeLocking.finiteSymbol q 0 N a ω =
      (Real.sin (q.angle ω) / Real.sin (ω : ℝ) * (1-Real.cos (ω : ℝ))) *
        polynomialSymbol q N a (Real.cos (ω : ℝ)) := by
  rw [ModeLocking.finiteSymbol_actual, Geometry.shiftedCurve_zero]
  unfold polynomialSymbol
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Farey.Certificates.lag_polynomial_factor q n (‹∀ n ∈ N, n ≠ 0› n hn) ω hω,
    signedLag_divided]
  ring

theorem factor_positive (q : Tuning) (ω : Frequency)
    (hω : 0 < (ω : ℝ) ∧ (ω : ℝ) < Real.pi) :
    0 < Real.sin (q.angle ω) / Real.sin (ω : ℝ) * (1-Real.cos (ω : ℝ)) := by
  apply mul_pos
  · exact div_pos
      (Real.sin_pos_of_pos_of_lt_pi (q.angle_mem hω).1 (q.angle_mem hω).2)
      (Real.sin_pos_of_pos_of_lt_pi hω.1 hω.2)
  · apply sub_pos.mpr
    simpa using Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num : (0:ℝ) ≤ 0)
      hω.2.le hω.1

theorem polynomial_strict (q : Tuning) (N : Finset ℤ) (a : ℤ → ℝ)
    (hn : ∀ n ∈ N, n ≠ 0) (ω : Frequency)
    (hω : 0 < (ω : ℝ) ∧ (ω : ℝ) < Real.pi)
    (h : polynomialSymbol q N a (Real.cos (ω : ℝ)) < 0) :
    ModeLocking.finiteSymbol q 0 N a ω < 0 := by
  rw [polynomial_factor q N a hn ω hω]
  exact mul_neg_of_pos_of_neg (factor_positive q ω hω) h

theorem polynomial_zero (q : Tuning) (N : Finset ℤ) (a : ℤ → ℝ)
    (hn : ∀ n ∈ N, n ≠ 0) (ω : Frequency)
    (hω : 0 < (ω : ℝ) ∧ (ω : ℝ) < Real.pi) :
    ModeLocking.finiteSymbol q 0 N a ω = 0 ↔
      polynomialSymbol q N a (Real.cos (ω : ℝ)) = 0 := by
  rw [polynomial_factor q N a hn ω hω, mul_eq_zero]
  simp only [(factor_positive q ω hω).ne', false_or]

theorem polynomialSymbol_analytic (q : Tuning) (N : Finset ℤ) (a : ℤ → ℝ) (c : ℝ) :
    AnalyticAt ℝ (polynomialSymbol q N a) c := by
  unfold polynomialSymbol
  have he : (fun x => ∑ n ∈ N, a n * dividedLag q n x) =
      ∑ n ∈ N, fun x => a n * dividedLag q n x := by
    funext x
    simp only [Finset.sum_apply]
  rw [he]
  exact (N.analyticAt_sum fun n _ =>
    (show AnalyticAt ℝ (fun x => a n * dividedLag q n x) c from by
      unfold dividedLag
      exact analyticAt_const.mul
        (((ModeLocking.TwoLag.analyticAt_Xi q c).mul
          (ModeLocking.TwoLag.analyticAt_W n.natAbs c)).sub
            ((analyticAt_const.mul (analyticAt_const.add analyticAt_id)).mul
              ((AnalyticOnNhd.eval_polynomial
                (Polynomial.Chebyshev.U ℝ ((n.natAbs-1 : ℕ) : ℤ))) c (mem_univ c))))))

end polyak.CertifiedExamples.Plateaus
