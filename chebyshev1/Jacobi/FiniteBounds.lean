import chebyshev1.Jacobi.PartitionBounds
import chebyshev1.Chebyshev.CoshBound

/-!
Article: chebyshev1, Theorem 4.3.
The finite higher-order remainder bound in 4.3(iii).
Use: `chebyshev1.JacobiData.opNorm_driftRemainder_cosh_le` feeds
`chebyshev1.SineJacobi.opNorm_driftRemainder_cosh_le` (op Norm drift Remainder cosh le).
-/
namespace chebyshev1.JacobiData
noncomputable section
open Polynomial Polynomial.Chebyshev
open scoped BigOperators Matrix.Norms.L2Operator
set_option backward.isDefEq.respectTransparency false
variable (J : JacobiData) (I : SpectralInterval)
variable {d : Type*} [Fintype d] [DecidableEq d]

/--
The stated quantitative bound `opNorm (J.driftOrder I N k H E) ≤ I.epsilon N *
(2*delta/I.delta)^k * (taylor 1 (T ℝ N)).coeff k`.

Use: `chebyshev1.JacobiData.opNorm_driftRemainder_endpoint_le` uses this bound to establish
the stated quantitative bound `opNorm ((J.realization I).driftRemainder N H E) ≤ I.epsilon N *
((T ℝ N).eval (1+2*delta/I.delta)-1-2*(N:ℝ)^2*delta/I.delta)`.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.opNorm_finiteDrift_le`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem opNorm_driftOrder_endpoint_le {N k : ℕ} (h : J.Admissible I N)
    (hm : J.EndpointMax N) (ht : J.leading N = C (2/(2:ℝ)^N) * T ℝ N) (hk : k ≤ N)
    (H : Matrix d d ℝ) (hH : H.IsHermitian) (hspec : spectrum ℝ H ⊆ Set.Icc I.mu I.L)
    (E : ℕ → Matrix d d ℝ) (delta : ℝ) (hd : 0 ≤ delta)
    (hE : ∀ s < N, opNorm (E s) ≤ delta) :
    opNorm (J.driftOrder I N k H E) ≤
      I.epsilon N * (2*delta/I.delta)^k * (taylor 1 (T ℝ N)).coeff k := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hb := J.opNorm_driftOrder_G_le I h ht k H hH hspec E delta hd hE
  rw [J.G_eq_chebyshev_coeff I h hm ht hk] at hb
  convert hb using 1
  simp only [div_pow, mul_pow]
  rw [show (4:ℝ)^k = 2^k * 2^k by rw [← mul_pow]; norm_num]
  field_simp

/--
Exact identity `(J.realization I).driftRemainder N H E = ∑ k ∈ Finset.range (N-1), J.driftOrder
I N (k+2) H E`.

Use: `chebyshev1.JacobiData.opNorm_driftRemainder_endpoint_le` rewrites with this identity
to prove the bound `opNorm ((J.realization I).driftRemainder N H E) ≤
I.epsilon N * ((T ℝ N).eval (1+2*delta/I.delta)-1-2*(N:ℝ)^2*delta/I.delta)`.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.opNorm_driftRemainder_le`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem driftRemainder_orders (N : ℕ) (H : Matrix d d ℝ) (E : ℕ → Matrix d d ℝ) :
    (J.realization I).driftRemainder N H E =
      ∑ k ∈ Finset.range (N-1), J.driftOrder I N (k+2) H E := by
  unfold Realization.driftRemainder higherOrder driftOrder
  change (J.realization I).contractLinear _ = _
  rw [map_sum]
  rfl

/--
The full finite drift bound in 4.3(iii); no smallness condition on `delta`.

The stated quantitative bound `opNorm ((J.realization I).operatorTransfer N (fun s => H+E s) -
aeval H (I.residual N)) ≤ I.epsilon N * ((T ℝ N).eval (1+2*delta/I.delta)-1)`.

Use: `chebyshev1.Prefix.opNorm_finiteDrift_le` uses this identity to establish the stated
quantitative bound `opNorm ((realization I).operatorTransfer N (fun s => H+E s) - aeval H
(I.residual N)) ≤ I.epsilon N * ((T ℝ N).eval (1+2*delta/I.delta)-1)`.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.opNorm_finiteDrift_le`.

Proof: Use the identities/estimates `chebyshev1.JacobiData.operatorTransfer_driftOrders`,
`chebyshev1.JacobiData.driftOrder_zero`, `chebyshev1.JacobiData.operator_exact` with
the arguments shown in the proof.
-/
theorem opNorm_finiteDrift_endpoint_le {N : ℕ} (h : J.Admissible I N)
    (hm : J.EndpointMax N) (ht : J.leading N = C (2/(2:ℝ)^N) * T ℝ N)
    (H : Matrix d d ℝ) (hH : H.IsHermitian) (hspec : spectrum ℝ H ⊆ Set.Icc I.mu I.L)
    (E : ℕ → Matrix d d ℝ) (delta : ℝ) (hd : 0 ≤ delta)
    (hE : ∀ s < N, opNorm (E s) ≤ delta) :
    opNorm ((J.realization I).operatorTransfer N (fun s => H+E s) -
      aeval H (I.residual N)) ≤
        I.epsilon N * ((T ℝ N).eval (1+2*delta/I.delta)-1) := by
  -- Use the identities/estimates `chebyshev1.JacobiData.operatorTransfer_driftOrders`,
  -- `chebyshev1.JacobiData.driftOrder_zero`, `chebyshev1.JacobiData.operator_exact`
  -- with the arguments shown in the proof.
  let u := 2*delta/I.delta
  let c (k : ℕ) := I.epsilon N * u^k * (taylor 1 (T ℝ N)).coeff k
  have hs : ∑ k ∈ Finset.range (N+1), c k = I.epsilon N * (T ℝ N).eval (1+u) := by
    simp only [c, mul_assoc, ← Finset.mul_sum]
    rw [show (∑ k ∈ Finset.range (N+1), u^k * (taylor 1 (T ℝ N)).coeff k) =
      (taylor 1 (T ℝ N)).eval u by
        simp_rw [mul_comm (u^_)]; exact (eval_eq_sum_range' (by simp : (taylor 1 (T ℝ N)).natDegree < N+1) u).symm]
    rw [taylor_eval, add_comm]
  have hc0 : c 0 = I.epsilon N := by simp [c, taylor_coeff_zero]
  have he : (J.realization I).operatorTransfer N (fun s => H+E s) - aeval H (I.residual N) =
      ∑ k ∈ Finset.range N, J.driftOrder I N (k+1) H E := by
    rw [J.operatorTransfer_driftOrders I, Finset.sum_range_succ', J.driftOrder_zero I,
      J.operator_exact I h N le_rfl H, J.terminal_residual I (by positivity) ht]
    abel
  rw [he]
  calc
    _ ≤ ∑ k ∈ Finset.range N, opNorm (J.driftOrder I N (k+1) H E) := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range N, c (k+1) := by
      apply Finset.sum_le_sum
      intro k hk
      exact J.opNorm_driftOrder_endpoint_le I h hm ht (by have := Finset.mem_range.mp hk; omega)
        H hH hspec E delta hd hE
    _ = _ := by rw [Finset.sum_range_succ', hc0] at hs; dsimp [u] at hs; linarith

/--
The finite higher-order remainder bound in 4.3(iii).

The stated quantitative bound `opNorm ((J.realization I).driftRemainder N H E) ≤ I.epsilon N *
((T ℝ N).eval (1+2*delta/I.delta)-1-2*(N:ℝ)^2*delta/I.delta)`.

Use: `chebyshev1.JacobiData.opNorm_driftRemainder_cosh_le` uses this bound to establish the
stated quantitative bound `opNorm ((J.realization I).driftRemainder N H E) ≤ (2/3:ℝ)*I.epsilon
N*(N:ℝ)^4*(delta/I.delta)^2 * Real.cosh (2*(N:ℝ)*Real.sqrt (delta/I.delta))`.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.opNorm_driftRemainder_le`.

Proof: Use the identities/estimates `chebyshev1.JacobiData.driftRemainder_orders`,
`chebyshev1.JacobiData.opNorm_driftOrder_endpoint_le` with the arguments shown in the
proof.
-/
theorem opNorm_driftRemainder_endpoint_le {N : ℕ} (hN : 0 < N) (h : J.Admissible I N)
    (hm : J.EndpointMax N) (ht : J.leading N = C (2/(2:ℝ)^N) * T ℝ N)
    (H : Matrix d d ℝ) (hH : H.IsHermitian) (hspec : spectrum ℝ H ⊆ Set.Icc I.mu I.L)
    (E : ℕ → Matrix d d ℝ) (delta : ℝ) (hd : 0 ≤ delta)
    (hE : ∀ s < N, opNorm (E s) ≤ delta) :
    opNorm ((J.realization I).driftRemainder N H E) ≤
      I.epsilon N * ((T ℝ N).eval (1+2*delta/I.delta)-1-2*(N:ℝ)^2*delta/I.delta) := by
  -- Use the identities/estimates `chebyshev1.JacobiData.driftRemainder_orders`,
  -- `chebyshev1.JacobiData.opNorm_driftOrder_endpoint_le` with the arguments shown in the
  -- proof.
  let u := 2*delta/I.delta
  let c (k : ℕ) := I.epsilon N * u^k * (taylor 1 (T ℝ N)).coeff k
  have hs : ∑ k ∈ Finset.range (N+1), c k = I.epsilon N * (T ℝ N).eval (1+u) := by
    simp only [c, mul_assoc, ← Finset.mul_sum]
    rw [show (∑ k ∈ Finset.range (N+1), u^k * (taylor 1 (T ℝ N)).coeff k) =
      (taylor 1 (T ℝ N)).eval u by
        simp_rw [mul_comm (u^_)]; exact (eval_eq_sum_range' (by simp : (taylor 1 (T ℝ N)).natDegree < N+1) u).symm]
    rw [taylor_eval, add_comm]
  have hc0 : c 0 = I.epsilon N := by simp [c, taylor_coeff_zero]
  have hc1 : c 1 = I.epsilon N * (N:ℝ)^2 * u := by
    simp only [c, taylor_coeff_one, derivative_T_eval_one, pow_one, Int.cast_natCast]
    ring
  rw [show N+1 = (N-1)+1+1 by omega, Finset.sum_range_succ', Finset.sum_range_succ'] at hs
  rw [hc0] at hs
  change (∑ k ∈ Finset.range (N-1), c (k+2)) + c 1 + I.epsilon N = _ at hs
  rw [hc1] at hs
  rw [J.driftRemainder_orders I]
  calc
    _ ≤ ∑ k ∈ Finset.range (N-1), opNorm (J.driftOrder I N (k+2) H E) := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range (N-1), c (k+2) := by
      apply Finset.sum_le_sum
      intro k hk
      exact J.opNorm_driftOrder_endpoint_le I h hm ht (by have := Finset.mem_range.mp hk; omega)
        H hH hspec E delta hd hE
    _ = _ := by
      have hh := eq_sub_of_add_eq (eq_sub_of_add_eq hs)
      rw [hh]
      dsimp [u]
      ring

/--
The stated quantitative bound `opNorm ((J.realization I).driftRemainder N H E) ≤
(2/3:ℝ)*I.epsilon N*(N:ℝ)^4*(delta/I.delta)^2 * Real.cosh (2*(N:ℝ)*Real.sqrt (delta/I.delta))`.

Use: `chebyshev1.Prefix.opNorm_driftRemainder_cosh_le` uses this bound to establish the
stated quantitative bound `opNorm ((realization I).driftRemainder N H E) ≤ (2/3:ℝ)*I.epsilon
N*(N:ℝ)^4*(delta/I.delta)^2 * Real.cosh (2*(N:ℝ)*Real.sqrt (delta/I.delta))`.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.opNorm_driftRemainder_cosh_le`.

Proof: Use the identities/estimates `chebyshev1.SpectralInterval.delta_pos`,
`chebyshev1.chebyshev_remainder_cosh_le`, `chebyshev1.SpectralInterval.den_pos` with
the arguments shown in the proof.
-/
theorem opNorm_driftRemainder_cosh_le {N : ℕ} (hN : 0 < N) (h : J.Admissible I N)
    (hm : J.EndpointMax N) (ht : J.leading N = C (2/(2:ℝ)^N) * T ℝ N)
    (H : Matrix d d ℝ) (hH : H.IsHermitian) (hspec : spectrum ℝ H ⊆ Set.Icc I.mu I.L)
    (E : ℕ → Matrix d d ℝ) (delta : ℝ) (hd : 0 ≤ delta)
    (hE : ∀ s < N, opNorm (E s) ≤ delta) :
    opNorm ((J.realization I).driftRemainder N H E) ≤
      (2/3:ℝ)*I.epsilon N*(N:ℝ)^4*(delta/I.delta)^2 *
        Real.cosh (2*(N:ℝ)*Real.sqrt (delta/I.delta)) := by
  -- Use the identities/estimates `chebyshev1.SpectralInterval.delta_pos`,
  -- `chebyshev1.chebyshev_remainder_cosh_le`, `chebyshev1.SpectralInterval.den_pos`
  -- with the arguments shown in the proof.
  have hu : 0 ≤ 2*delta/I.delta := div_nonneg (by positivity) I.delta_pos.le
  have hsqrt : Real.sqrt (2*(2*delta/I.delta)) = 2*Real.sqrt (delta/I.delta) := by
    rw [show 2*(2*delta/I.delta) = 2^2*(delta/I.delta) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  have hb := mul_le_mul_of_nonneg_left (chebyshev_remainder_cosh_le N _ hu)
    (div_nonneg (by norm_num : (0:ℝ) ≤ 1) (I.den_pos N).le)
  have he : I.epsilon N * ((T ℝ N).eval (1+2*delta/I.delta)-1-(N:ℝ)^2*(2*delta/I.delta)) =
      I.epsilon N * ((T ℝ N).eval (1+2*delta/I.delta)-1-2*(N:ℝ)^2*delta/I.delta) := by ring
  change I.epsilon N * _ ≤ _ at hb
  rw [he, hsqrt] at hb
  convert (J.opNorm_driftRemainder_endpoint_le I hN h hm ht H hH hspec E delta hd hE).trans hb using 1
  dsimp [SpectralInterval.epsilon]
  rw [show (N:ℝ)*(2*Real.sqrt (delta/I.delta)) = 2*(N:ℝ)*Real.sqrt (delta/I.delta) by ring]
  ring

end
end chebyshev1.JacobiData
