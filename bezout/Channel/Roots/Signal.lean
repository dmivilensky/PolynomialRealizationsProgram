import bezout.Channel.Roots.Chart
import bezout.Channel.SignalAlgebra

/-!
Article: bezout, Proposition D.1, physical root-order and interval invariances.
Use: the actual first-variation signal matrix, operator norm and HS energy have
the asserted ordering invariance; LF/Prefix ratios depend only on chart points.
Proof: actual diagonal kernels reindex temporal columns, and their common
positive epsilon/Delta scale cancels from the literal physical matrix norms.
-/

namespace bezout.Channel.Roots
noncomputable section
variable {N : ℕ} {J : Type*} [Fintype J] [DecidableEq J]

omit [Fintype J] [DecidableEq J] in
/-- Permuting a physical root schedule permutes exactly the actual signal columns. -/
theorem signalMatrix_permute (α : Fin N → ℝ) (e : Equiv.Perm (Fin N)) (lam a : J → ℝ) :
    signalMatrix (history (α ∘ e)) lam a=columnPermutation (signalMatrix (history α) lam a) e := by
  funext j s
  simp only [signalMatrix,columnPermutation,history_diagonal_permute]

omit [DecidableEq J] in
/-- Root ordering leaves the true physical first-variation operator gain unchanged. -/
theorem signalNorm_permute (α : Fin N → ℝ) (e : Equiv.Perm (Fin N)) (lam a : J → ℝ) :
    rectangularNorm (signalMatrix (history (α ∘ e)) lam a)=
      rectangularNorm (signalMatrix (history α) lam a) := by
  rw [signalMatrix_permute,rectangularNorm_colperm]

omit [DecidableEq J] in
/-- Root ordering leaves the full physical first-variation HS energy unchanged. -/
theorem signalHsSq_permute (α : Fin N → ℝ) (e : Equiv.Perm (Fin N)) (lam a : J → ℝ) :
    rectangularHsSq (signalMatrix (history (α ∘ e)) lam a)=
      rectangularHsSq (signalMatrix (history α) lam a) := by
  rw [signalMatrix_permute,rectangularHsSq_colperm]

omit [Fintype J] [DecidableEq J] in
/-- Exact common-scale cancellation for the entire actual root signal matrix. -/
theorem normalized_signalMatrix (I I' : chebyshev1.SpectralInterval) (N : ℕ)
    (e : Equiv.Perm (Fin N)) (x a : J → ℝ) :
    (I.delta/I.epsilon N) • signalMatrix (history (steps I N e)) (inverseChart I ∘ x) a=
      (I'.delta/I'.epsilon N) • signalMatrix (history (steps I' N e)) (inverseChart I' ∘ x) a := by
  funext j s
  change I.delta/I.epsilon N*(a j*Lower.physicalKernel _ s _ _)=
    I'.delta/I'.epsilon N*(a j*Lower.physicalKernel _ s _ _)
  dsimp only [Function.comp_apply]
  calc
    _ = a j*(Lower.physicalKernel (history (steps I N e)) s (inverseChart I (x j))
      (inverseChart I (x j))*I.delta/I.epsilon N) := by ring
    _ = a j*(Lower.physicalKernel (history (steps I' N e)) s (inverseChart I' (x j))
      (inverseChart I' (x j))*I'.delta/I'.epsilon N) := by rw [normalized_chart_kernel I I']
    _ = _ := by ring

omit [Fintype J] [DecidableEq J] in
/-- Exact common-scale cancellation for the actual Prefix signal matrix. -/
theorem prefix_normalized_signalMatrix (I I' : chebyshev1.SpectralInterval) (N : ℕ) (hN : 0<N)
    (x a : J → ℝ) :
    (I.delta/I.epsilon N) • signalMatrix (Classical.history I N) (inverseChart I ∘ x) a=
      (I'.delta/I'.epsilon N) • signalMatrix (Classical.history I' N) (inverseChart I' ∘ x) a := by
  funext j s
  change I.delta/I.epsilon N*(a j*Lower.physicalKernel _ s _ _)=
    I'.delta/I'.epsilon N*(a j*Lower.physicalKernel _ s _ _)
  dsimp only [Function.comp_apply]
  calc
    _ = a j*(Lower.physicalKernel (Classical.history I N) s (inverseChart I (x j))
      (inverseChart I (x j))*I.delta/I.epsilon N) := by ring
    _ = a j*(Lower.physicalKernel (Classical.history I' N) s (inverseChart I' (x j))
      (inverseChart I' (x j))*I'.delta/I'.epsilon N) := by
        rw [prefix_normalized_chart_kernel I I' N hN]
    _ = _ := by ring

/-- The interval-dependent chart normalization is strictly positive. -/
theorem chartScale_pos (I : chebyshev1.SpectralInterval) (N : ℕ) : 0<I.delta/I.epsilon N :=
  div_pos I.delta_pos (one_div_pos.mpr (I.den_pos N))

omit [DecidableEq J] in
/-- At fixed chart coordinates the literal actual root/Prefix operator ratio is interval independent. -/
theorem signalNorm_ratio_interval (I I' : chebyshev1.SpectralInterval) (N : ℕ) (hN : 0<N)
    (e : Equiv.Perm (Fin N)) (x a : J → ℝ) :
    rectangularNorm (signalMatrix (history (steps I N e)) (inverseChart I ∘ x) a)/
      rectangularNorm (signalMatrix (Classical.history I N) (inverseChart I ∘ x) a)=
    rectangularNorm (signalMatrix (history (steps I' N e)) (inverseChart I' ∘ x) a)/
      rectangularNorm (signalMatrix (Classical.history I' N) (inverseChart I' ∘ x) a) := by
  have hr := congrArg rectangularNorm (normalized_signalMatrix I I' N e x a)
  have hp := congrArg rectangularNorm (prefix_normalized_signalMatrix I I' N hN x a)
  simp only [rectangularNorm_smul,abs_of_pos (chartScale_pos I N),
    abs_of_pos (chartScale_pos I' N)] at hr hp
  rw [← mul_div_mul_left _ _ (ne_of_gt (chartScale_pos I N)),hr,hp,
    mul_div_mul_left _ _ (ne_of_gt (chartScale_pos I' N))]

omit [DecidableEq J] in
/-- At fixed chart coordinates the literal actual root/Prefix HS ratio is interval independent. -/
theorem signalHsSq_ratio_interval (I I' : chebyshev1.SpectralInterval) (N : ℕ) (hN : 0<N)
    (e : Equiv.Perm (Fin N)) (x a : J → ℝ) :
    rectangularHsSq (signalMatrix (history (steps I N e)) (inverseChart I ∘ x) a)/
      rectangularHsSq (signalMatrix (Classical.history I N) (inverseChart I ∘ x) a)=
    rectangularHsSq (signalMatrix (history (steps I' N e)) (inverseChart I' ∘ x) a)/
      rectangularHsSq (signalMatrix (Classical.history I' N) (inverseChart I' ∘ x) a) := by
  have hr := congrArg rectangularHsSq (normalized_signalMatrix I I' N e x a)
  have hp := congrArg rectangularHsSq (prefix_normalized_signalMatrix I I' N hN x a)
  simp only [rectangularHsSq_smul] at hr hp
  rw [← mul_div_mul_left _ _ (pow_ne_zero 2 (ne_of_gt (chartScale_pos I N))),hr,hp,
    mul_div_mul_left _ _ (pow_ne_zero 2 (ne_of_gt (chartScale_pos I' N)))]

end
end bezout.Channel.Roots
