import bezout.Lower.ChebyshevCorners

/-!
Article: bezout, Equations `eq:corners`, `eq:physical-four-corners`, and
the lower bound in Theorem 4.1.
Use: the normalized Bezoutian inequalities are transported to the actual
oracle-error kernels. The exact factors `4 epsilon / Delta` are retained,
including for symmetric Hilbert--Schmidt perturbations.
-/

namespace bezout.Lower

noncomputable section
open Polynomial
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- Scaling both response endpoint profiles scales the symmetric energy quadratically. -/
theorem symmetricCornerEnergy_scale (c : ℝ) (fp fm qp qm : ι → ℝ) :
    symmetricCornerEnergy (fun i => c * fp i) (fun i => c * fm i) qp qm =
      c ^ 2 * symmetricCornerEnergy fp fm qp qm := by
  have hd (i : ι) : ((c * fp i) * qp i) ^ 2 + ((c * fm i) * qm i) ^ 2 =
      c ^ 2 * ((fp i * qp i) ^ 2 + (fm i * qm i) ^ 2) := by ring
  have hx (i : ι) : ((c * fp i) * qm i + (c * fm i) * qp i) ^ 2 =
      c ^ 2 * (fp i * qm i + fm i * qp i) ^ 2 := by ring
  unfold symmetricCornerEnergy
  simp_rw [hd, hx]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- The ordinary weighted energy has the same exact scaling. -/
theorem fourCornerEnergy_scale (c : ℝ) (fp fm qp qm : ι → ℝ) :
    fourCornerEnergy (fun i => c * fp i) (fun i => c * fm i) qp qm =
      c ^ 2 * fourCornerEnergy fp fm qp qm := by
  have hd (i : ι) : ((c * fp i) * qp i) ^ 2 + ((c * fm i) * qm i) ^ 2 =
      c ^ 2 * ((fp i * qp i) ^ 2 + (fm i * qm i) ^ 2) := by ring
  have hx (i : ι) : ((c * fp i) * qm i) ^ 2 + ((c * fm i) * qp i) ^ 2 =
      c ^ 2 * ((fp i * qm i) ^ 2 + (fm i * qp i) ^ 2) := by ring
  unfold fourCornerEnergy
  simp_rw [hd, hx]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- The inverse spectral coordinate sends the right Chebyshev endpoint to mu. -/
theorem chart_eval_one (I : chebyshev1.SpectralInterval) :
    (GradedFamily.chart I).eval 1 = I.mu := by
  simp only [GradedFamily.chart, eval_sub, eval_C, eval_mul, eval_X]
  unfold chebyshev1.SpectralInterval.delta
  ring

/-- The inverse spectral coordinate sends the left Chebyshev endpoint to L. -/
theorem chart_eval_neg_one (I : chebyshev1.SpectralInterval) :
    (GradedFamily.chart I).eval (-1) = I.L := by
  simp only [GradedFamily.chart, eval_sub, eval_C, eval_mul, eval_X]
  unfold chebyshev1.SpectralInterval.delta
  ring

/-- The additive endpoint scale used in the article. -/
def additiveScale (I : chebyshev1.SpectralInterval) (N : ℕ) : ℝ :=
  (1 - I.epsilon N) / I.mu

/-- The diagonal derivative scale used in the linear lower bound. -/
def derivativeScale (I : chebyshev1.SpectralInterval) (N : ℕ) : ℝ :=
  2 * I.epsilon N * (N : ℝ) ^ 2 / I.delta

/-- The exact physical oracle-error insertion kernel. -/
def physicalKernel {N : ℕ} (h : bezout.History N) (s : Fin N) (x y : ℝ) : ℝ :=
  (h.response s).eval x * (h.query s).eval y

/-- Its temporal squared energy at a fixed spectral pair. -/
def physicalKernelSq {N : ℕ} (h : bezout.History N) (x y : ℝ) : ℝ :=
  ∑ s, (physicalKernel h s x y) ^ 2

/-- The first endpoint identity holds for every actual Chebyshev-exact history. -/
theorem response_sum_mu {N : ℕ} (h : bezout.History N)
    (I : chebyshev1.SpectralInterval) (he : h.ChebyshevExact I) :
    (∑ s, (h.response s).eval I.mu) = -additiveScale I N := by
  have hd := h.physical_bezout I.mu 0 (ne_of_gt I.mu_pos)
  simp only [h.query_eval_zero, mul_one, h.terminal_eval_zero, sub_zero] at hd
  change h.terminal = I.residual N at he
  rw [he, I.residual_eval_mu N] at hd
  rw [hd]
  unfold additiveScale
  ring

/-- The diagonal corner is exactly the derivative of the prescribed terminal. -/
theorem kernel_sum_mu {N : ℕ} (h : bezout.History N)
    (I : chebyshev1.SpectralInterval) (he : h.ChebyshevExact I) :
    (∑ s, physicalKernel h s I.mu I.mu) = -derivativeScale I N := by
  unfold physicalKernel
  rw [h.physical_bezout_diagonal]
  change h.terminal = I.residual N at he
  rw [he, I.residual_derivative_eval_mu N]
  unfold derivativeScale
  ring

/-- The physical symmetric four-corner lower bound, with its exact scale. -/
theorem history_physical_symmetric_four_corner_lower {N : ℕ} (h : bezout.History N)
    (I : chebyshev1.SpectralInterval) (he : h.ChebyshevExact I)
    (hN : 3 ≤ N) (hodd : Odd N) :
    (4 * I.epsilon N / I.delta) ^ 2 * oddEnergy N ≤ symmetricCornerEnergy
      (fun s => (h.response s).eval I.mu) (fun s => (h.response s).eval I.L)
      (fun s => (h.query s).eval I.mu) (fun s => (h.query s).eval I.L) := by
  have hep : I.epsilon N ≠ 0 := one_div_ne_zero (I.den_ne N)
  have hD : I.delta ≠ 0 := ne_of_gt I.delta_pos
  have hc := history_chart_symmetric_four_corner_lower h I he hN hodd
  simp only [History.chartFactor, History.chartQuery, eval_mul, eval_C, eval_comp,
    chart_eval_one, chart_eval_neg_one] at hc
  rw [symmetricCornerEnergy_scale] at hc
  have hm := mul_le_mul_of_nonneg_left hc (sq_nonneg (4 * I.epsilon N / I.delta))
  convert hm using 1
  field_simp

/-- The ordinary physical four-corner lower bound follows without an extra loss. -/
theorem history_physical_four_corner_lower {N : ℕ} (h : bezout.History N)
    (I : chebyshev1.SpectralInterval) (he : h.ChebyshevExact I)
    (hN : 3 ≤ N) (hodd : Odd N) :
    (4 * I.epsilon N / I.delta) ^ 2 * oddEnergy N ≤ fourCornerEnergy
      (fun s => (h.response s).eval I.mu) (fun s => (h.response s).eval I.L)
      (fun s => (h.query s).eval I.mu) (fun s => (h.query s).eval I.L) :=
  (history_physical_symmetric_four_corner_lower h I he hN hodd).trans
    (symmetricCornerEnergy_le_fourCornerEnergy _ _ _ _)

end
end bezout.Lower
