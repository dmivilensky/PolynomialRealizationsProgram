import chebyshev1.Jacobi.FiniteBounds

/-!
Article: chebyshev1, Theorem 4.3.
Every homogeneous insertion order attains its endpoint partition constant.
Use: `chebyshev1.JacobiData.opNorm_driftOrder_static` feeds
`chebyshev1.SineJacobi.driftOrder_static_attained` (The same static example attains every
homogeneous insertion order).
-/
namespace chebyshev1.JacobiData
noncomputable section
open Polynomial Polynomial.Chebyshev
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
variable (J : JacobiData) (I : SpectralInterval)

/--
Every homogeneous insertion order attains its endpoint partition constant.

Exact identity `J.driftOrder I N k (scalarMatrix I.mu) (fun _ => scalarMatrix (-delta)) =
scalarMatrix ((2*delta/I.delta)^k/J.den I N*(taylor 1 (J.leading N)).coeff k)`.

Use: `chebyshev1.JacobiData.opNorm_driftOrder_static` rewrites with this identity to
establish exact identity `opNorm (J.driftOrder I N k (scalarMatrix I.mu) (fun _ => scalarMatrix
(-delta))) = I.epsilon N*(2*delta/I.delta)^k*(taylor 1 (T ℝ N)).coeff k`.

Article: chebyshev1, Corollary 5.3 via
`chebyshev1.SineJacobi.driftOrder_static_attained`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral. Check each member of the finite index type; no case is omitted.
-/
theorem driftOrder_static_value {N : ℕ} (h : J.Admissible I N) (k : ℕ) (delta : ℝ) :
    J.driftOrder I N k (scalarMatrix I.mu) (fun _ => scalarMatrix (-delta)) =
      scalarMatrix ((2*delta/I.delta)^k/J.den I N*(taylor 1 (J.leading N)).coeff k) := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  rw [J.driftOrder_words I h]
  have hs : (∑ times ∈ (Finset.range N).powersetCard k,
      (-delta)^times.card*J.endpointWeight N times) =
      (-delta)^k*(taylor 1 (J.leading N)).coeff k := by
    rw [J.taylor_leading_coeff I h, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro times ht
    rw [(Finset.mem_powersetCard.mp ht).2]
  simp_rw [J.operatorWord_static I]
  apply Matrix.ext
  intro i j
  fin_cases i
  fin_cases j
  simp only [Matrix.smul_apply, Matrix.sum_apply, scalarMatrix,
    Matrix.diagonal_apply_eq, smul_eq_mul]
  rw [hs]
  have hp : (-(2/I.delta))^k*(-delta)^k = (2*delta/I.delta)^k := by
    rw [← mul_pow]
    congr 1
    ring
  calc _ = ((-(2/I.delta))^k*(-delta)^k)/J.den I N*(taylor 1 (J.leading N)).coeff k := by ring
       _ = _ := by rw [hp]

/--
Exact identity `opNorm (J.driftOrder I N k (scalarMatrix I.mu) (fun _ => scalarMatrix
(-delta))) = I.epsilon N*(2*delta/I.delta)^k*(taylor 1 (T ℝ N)).coeff k`.

Use: `chebyshev1.SineJacobi.driftOrder_static_attained` uses this identity to establish
exact identity `opNorm ((data N).driftOrder I N k (scalarMatrix I.mu) (fun _ => scalarMatrix
(-delta))) = I.epsilon N*(2*delta/I.delta)^k*(taylor 1 (T ℝ N)).coeff k`.

Article: chebyshev1, Corollary 5.3 via
`chebyshev1.SineJacobi.driftOrder_static_attained`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem opNorm_driftOrder_static {N : ℕ} (h : J.Admissible I N) (hm : J.EndpointMax N)
    (ht : J.leading N = C (2/(2:ℝ)^N)*T ℝ N) (k : ℕ) (delta : ℝ) (hd : 0 ≤ delta) :
    opNorm (J.driftOrder I N k (scalarMatrix I.mu) (fun _ => scalarMatrix (-delta))) =
      I.epsilon N*(2*delta/I.delta)^k*(taylor 1 (T ℝ N)).coeff k := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hc : 0 ≤ (taylor 1 (J.leading N)).coeff k := by
    rw [← J.partitionBound_eq_coeff I h hm k]
    exact Finset.sum_nonneg (fun times _ => J.blockWord_bound_nonneg N _)
  rw [J.driftOrder_static_value I h k delta, opNorm_scalarMatrix,
    abs_of_nonneg (mul_nonneg (div_nonneg (pow_nonneg (div_nonneg (by positivity) I.delta_pos.le) k)
      (h N le_rfl).le) hc)]
  have hden : J.den I N = (2/(2:ℝ)^N)*I.den N := by simp [den, ht, SpectralInterval.den]
  rw [ht, taylor_mul, taylor_C, coeff_C_mul, hden]
  dsimp [SpectralInterval.epsilon]
  field_simp

end
end chebyshev1.JacobiData
