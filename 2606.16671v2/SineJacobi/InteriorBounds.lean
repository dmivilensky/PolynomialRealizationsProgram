import «2606.16671v2».SineJacobi.BlockFourier
import «2606.16671v2».Jacobi.EndpointBound

/-!
Article: 2606.16671v2, Lemma E.8.
The all-block maximum principle in E.8, including the terminal block.
Use: `«2606.16671v2».SineJacobi.endpointMax` feeds `«2606.16671v2».SineJacobi.opNorm_finiteDrift_le`
(op Norm finite Drift le).
-/
namespace «2606.16671v2».SineJacobi
noncomputable section
open Polynomial Real
open scoped BigOperators

/--
The stated quantitative bound `0 ≤ (p*q).coeff k`.

Use: `«2606.16671v2».SineJacobi.blockFourier_interior_nonneg` uses this bound to establish the
stated quantitative bound `0 ≤ (blockFourier N a n).coeff k`.

Article: 2606.16671v2, Corollary 5.3 via `«2606.16671v2».SineJacobi.G_exact`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
private theorem coeff_nonneg_mul (p q : ℝ[X]) (hp : ∀ k, 0 ≤ p.coeff k)
    (hq : ∀ k, 0 ≤ q.coeff k) (k : ℕ) : 0 ≤ (p*q).coeff k := by
  rw [coeff_mul]
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hp i.1) (hq i.2))

/--
The stated quantitative bound `0 ≤ (blockFourier N 0 s).coeff k`.

Use: `«2606.16671v2».SineJacobi.blockFourier_interior_nonneg` uses this bound to establish the
stated quantitative bound `0 ≤ (blockFourier N a n).coeff k`.

Article: 2606.16671v2, Corollary 5.3 via `«2606.16671v2».SineJacobi.G_exact`.

Proof: Separate `k ≤ s` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem blockFourier_leading_nonneg (N s k : ℕ) (hs : s < N) :
    0 ≤ (blockFourier N 0 s).coeff k := by
  rw [blockFourier_leading N s hs, rogers_coeff]
  by_cases hk : k ≤ s
  · exact (coefficient_pos N s k hs hk).le
  · rw [coefficient_of_gt N s k (by omega)]

/--
The stated quantitative bound `(Continuant.couplingProduct (fun s => C (4*(data N).aSq s)*X) a
n).natDegree ≤ n`.

Use: `«2606.16671v2».SineJacobi.blockFourier_interior_nonneg` uses this identity to establish
the stated quantitative bound `0 ≤ (blockFourier N a n).coeff k`.

Article: 2606.16671v2, Corollary 5.3 via `«2606.16671v2».SineJacobi.G_exact`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem fourierCoupling_degree (N a n : ℕ) :
    (Continuant.couplingProduct (fun s => C (4*(data N).aSq s)*X) a n).natDegree ≤ n := by
  -- Rewrite the definitions and library identities explicitly named in the proof, then
  -- discharge the resulting algebraic or order relation.
  unfold Continuant.couplingProduct
  calc
    _ ≤ ∑ t ∈ Finset.range n, (C (4*(data N).aSq (a+t))*X).natDegree := natDegree_prod_le _ _
    _ ≤ ∑ _t ∈ Finset.range n, 1 := by
      apply Finset.sum_le_sum
      intro t _
      compute_degree
    _ = n := by simp

/--
E.8: the coefficient of an interior block is extracted at degree N+k. The correction term has
degree at most N-1 and therefore cannot contribute.

The stated quantitative bound `0 ≤ (blockFourier N a n).coeff k`.

Use: `«2606.16671v2».SineJacobi.blockFourier_nonneg` uses this bound to establish the stated
quantitative bound `0 ≤ (blockFourier N a n).coeff k`.

Article: 2606.16671v2, Corollary 5.3 via `«2606.16671v2».SineJacobi.G_exact`.

Proof: Use the identities/estimates `«2606.16671v2».Continuant.interior_identity`,
`«2606.16671v2».SineJacobi.fourierCoupling_degree`,
`«2606.16671v2».SineJacobi.blockFourier_degree` with the arguments shown in the proof.
-/
theorem blockFourier_interior_nonneg (N a n : ℕ) (ha : 0 < a) (hn : a+n < N) (k : ℕ) :
    0 ≤ (blockFourier N a n).coeff k := by
  -- Use the identities/estimates `«2606.16671v2».Continuant.interior_identity`,
  -- `«2606.16671v2».SineJacobi.fourierCoupling_degree`,
  -- `«2606.16671v2».SineJacobi.blockFourier_degree` with the arguments shown in the proof.
  have hid := Continuant.interior_identity (fun _ => (1+X : ℝ[X]))
    (fun s => C (4*(data N).aSq s)*X) ha n hn
  change blockFourier N 0 N*blockFourier N a n =
    blockFourier N 0 (a+n)*blockFourier N a (N-a) -
      Continuant.couplingProduct (fun s => C (4*(data N).aSq s)*X) a (n+1)*
        blockFourier N 0 (a-1)*blockFourier N (a+n+1) (N-(a+n+1)) at hid
  rw [blockFourier_terminal N (by omega),
    blockFourier_tail_of_end N a (N-a) (by omega)] at hid
  let correction := Continuant.couplingProduct (fun s => C (4*(data N).aSq s)*X) a (n+1)*
    blockFourier N 0 (a-1)*blockFourier N (a+n+1) (N-(a+n+1))
  have hdeg : correction.natDegree < N := by
    have h0 := fourierCoupling_degree N a (n+1)
    have h1 := blockFourier_degree N 0 (a-1)
    have h2 := blockFourier_degree N (a+n+1) (N-(a+n+1))
    have hm := natDegree_mul_le (p := Continuant.couplingProduct
      (fun s => C (4*(data N).aSq s)*X) a (n+1)) (q := blockFourier N 0 (a-1))
    have hm2 := natDegree_mul_le (p := Continuant.couplingProduct
      (fun s => C (4*(data N).aSq s)*X) a (n+1)*blockFourier N 0 (a-1))
      (q := blockFourier N (a+n+1) (N-(a+n+1)))
    dsimp [correction]
    omega
  have hc := congrArg (fun p : ℝ[X] => p.coeff (k+N)) hid
  rw [add_mul, one_mul, coeff_add, coeff_X_pow_mul, coeff_sub] at hc
  change (blockFourier N a n).coeff (k+N) + (blockFourier N a n).coeff k =
    (blockFourier N 0 (a+n)*blockFourier N 0 (N-a)).coeff (k+N) - correction.coeff (k+N) at hc
  have hz : (blockFourier N a n).coeff (k+N) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by have := blockFourier_degree N a n; omega)
  have hz2 : correction.coeff (k+N) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  rw [hz, hz2, zero_add, sub_zero] at hc
  rw [hc]
  exact coeff_nonneg_mul _ _ (blockFourier_leading_nonneg N (a+n) · hn)
    (blockFourier_leading_nonneg N (N-a) · (by omega)) _

/--
Every finite sine–Jacobi block has nonnegative Fourier coefficients.

The stated quantitative bound `0 ≤ (blockFourier N a n).coeff k`.

Use: `«2606.16671v2».SineJacobi.endpointMax` uses this bound to establish the precise assertion
is `(data N).EndpointMax N`.

Article: 2606.16671v2, Corollary 5.3 via `«2606.16671v2».SineJacobi.G_exact`.

Proof: Separate `a = 0` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem blockFourier_nonneg (N a n : ℕ) (hN : 0 < N) (hn : a+n ≤ N) (k : ℕ) :
    0 ≤ (blockFourier N a n).coeff k := by
  -- Separate `a = 0` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  by_cases h0 : a = 0
  · subst a
    by_cases hfull : n = N
    · subst n; rw [blockFourier_terminal N hN]
      simp only [coeff_add, coeff_one, coeff_X_pow]
      split_ifs <;> norm_num
    · exact blockFourier_leading_nonneg N n k (by omega)
  · by_cases hend : a+n = N
    · rw [blockFourier_tail_of_end N a n hend]
      exact blockFourier_leading_nonneg N n k (by omega)
    · exact blockFourier_interior_nonneg N a n (by omega) (by omega) k

/--
Exact identity `(2:ℝ)^n*((data N).block a n).eval (cos theta) = ∑ k ∈ Finset.range (n+1),
(blockFourier N a n).coeff k * cos (((n:ℝ)-2*(k:ℝ))*theta)`.

Use: `«2606.16671v2».SineJacobi.endpointMax` uses this identity to establish the precise
assertion is `(data N).EndpointMax N`.

Article: 2606.16671v2, Corollary 5.3 via `«2606.16671v2».SineJacobi.G_exact`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem block_fourier (N a n : ℕ) (theta : ℝ) :
    (2:ℝ)^n*((data N).block a n).eval (cos theta) =
      ∑ k ∈ Finset.range (n+1), (blockFourier N a n).coeff k *
        cos (((n:ℝ)-2*(k:ℝ))*theta) := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  rw [blockFourier_cosine]
  have hp := as_sum_range' (blockFourier N a n) (n+1) (by have := blockFourier_degree N a n; omega)
  conv_lhs => rw [hp, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [cosineTransform_monomial, Int.cast_natCast]

/--
The all-block maximum principle in E.8, including the terminal block.

The precise assertion is `(data N).EndpointMax N`.

Use: `«2606.16671v2».SineJacobi.G_exact` uses this assertion to establish the identity `(data
N).G N k = 2/(2:ℝ)^k*(taylor 1 (T ℝ N)).coeff k`.

Article: 2606.16671v2, Corollary 5.3 via `«2606.16671v2».SineJacobi.G_exact`.

Proof: Use the identities/estimates `«2606.16671v2».SineJacobi.block_fourier`,
`«2606.16671v2».SineJacobi.blockFourier_nonneg` with the arguments shown in the proof.
-/
theorem endpointMax (N : ℕ) (hN : 0 < N) : (data N).EndpointMax N := by
  -- Use the identities/estimates `«2606.16671v2».SineJacobi.block_fourier`,
  -- `«2606.16671v2».SineJacobi.blockFourier_nonneg` with the arguments shown in the proof.
  intro a n hn x hx
  have hf := block_fourier N a n (arccos x)
  rw [cos_arccos hx.1 hx.2] at hf
  have h1 := block_fourier N a n 0
  simp only [mul_zero, cos_zero, mul_one] at h1
  have hb : |(2:ℝ)^n*((data N).block a n).eval x| ≤
      (2:ℝ)^n*((data N).block a n).eval 1 := by
    rw [hf, h1]
    calc
      _ ≤ ∑ k ∈ Finset.range (n+1), |(blockFourier N a n).coeff k *
          cos (((n:ℝ)-2*(k:ℝ))*arccos x)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro k _
        have hc := blockFourier_nonneg N a n hN hn k
        rw [abs_mul, abs_of_nonneg hc]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (abs_cos_le_one _) hc
  rw [abs_mul, abs_of_pos (pow_pos (by norm_num : (0:ℝ) < 2) n)] at hb
  exact (mul_le_mul_iff_right₀ (pow_pos (by norm_num : (0:ℝ) < 2) n)).mp hb

end
end «2606.16671v2».SineJacobi
