import chebyshev2.Finite.Gain
import chebyshev1.Jacobi.LinearResponse

/-!
Article: chebyshev2, Theorem 2.2.
Equation (5): the complete normalized gain is independent of mu and L.
Result: `chebyshev2.Jacobi.gain_minimal` supplies the stated article conclusion.
-/
namespace chebyshev2.Jacobi
noncomputable section
open chebyshev1 Polynomial
open scoped BigOperators
variable {N : ℕ} (J : Jacobi N) (I : SpectralInterval)

/--
Lemma 2: the block formula for the actual derivative of the finite recurrence.

Exact identity `(J.recurrence I h).method.realization.linearResponse N H E =
-(2/(I.delta*J.data.den I N)) • ∑ s ∈ Finset.range N, aeval H (J.data.spectralBlock I (s+1)
(N-(s+1))) * E s * aeval H (J.data.spectralBlock I 0 s)`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev2, Theorem 2.2.

Proof: Use the identities/estimates `chebyshev2.Horizon.linearResponse_eq`,
`chebyshev2.Jacobi.recurrence_agree`, `chebyshev1.JacobiData.linearResponse_blocks`
with the arguments shown in the proof.
-/
theorem derivative_formula {d : Type*} [Fintype d] [DecidableEq d]
    (h : J.data.Admissible I N) (H : Matrix d d ℝ) (hH : H.IsHermitian)
    (E : ℕ → Matrix d d ℝ) :
    (J.recurrence I h).method.realization.linearResponse N H E =
      -(2/(I.delta*J.data.den I N)) • ∑ s ∈ Finset.range N,
        aeval H (J.data.spectralBlock I (s+1) (N-(s+1))) * E s *
          aeval H (J.data.spectralBlock I 0 s) := by
  -- Use the identities/estimates `chebyshev2.Horizon.linearResponse_eq`,
  -- `chebyshev2.Jacobi.recurrence_agree`,
  -- `chebyshev1.JacobiData.linearResponse_blocks` with the arguments shown in the proof.
  rw [Horizon.linearResponse_eq (J.recurrence_agree I h) H E]
  exact J.data.linearResponse_blocks I h H hH E

/--
The stated quantitative bound `hsNorm ((J.recurrence I h).method.realization.linearResponse N H
E) ≤ J.gain I h * Real.sqrt (∑ s ∈ Finset.range N, hsNorm (E s)^2)`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev2, Theorem 2.2.

Proof: Use the identities/estimates `chebyshev1.Realization.hsNorm_linearResponse_bound`
with the arguments shown in the proof.
-/
theorem gain_bound {d : Type*} [Fintype d] [DecidableEq d]
    (h : J.data.Admissible I N) (H : Matrix d d ℝ) (hH : H.IsHermitian)
    (hs : spectrum ℝ H ⊆ Set.Icc I.mu I.L) (E : ℕ → Matrix d d ℝ) :
    hsNorm ((J.recurrence I h).method.realization.linearResponse N H E) ≤
      J.gain I h * Real.sqrt (∑ s ∈ Finset.range N, hsNorm (E s)^2) :=
  (J.recurrence I h).method.realization.hsNorm_linearResponse_bound I N H hH hs E

/--
The stated quantitative bound `J.gain I h ≤ C`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev2, Theorem 2.2.

Proof: Use the identities/estimates `chebyshev1.Realization.hs_constant_minimal` with the
arguments shown in the proof.
-/
theorem gain_minimal (h : J.data.Admissible I N) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ H : Matrix (Fin 2) (Fin 2) ℝ, H.IsHermitian →
      spectrum ℝ H ⊆ Set.Icc I.mu I.L → ∀ E : ℕ → Matrix (Fin 2) (Fin 2) ℝ,
        hsNorm ((J.recurrence I h).method.realization.linearResponse N H E) ≤
          C * Real.sqrt (∑ s ∈ Finset.range N, hsNorm (E s)^2)) : J.gain I h ≤ C :=
  (J.recurrence I h).method.realization.hs_constant_minimal I N C hC hb

/--
Equation (5): the complete normalized gain is independent of mu and L.

Exact identity `I.delta*J.gain I (J.admissible I hN ht) / ((N:ℝ)^(3/2:ℝ)*I.epsilon N) =
2/((N:ℝ)^(3/2:ℝ)*(J.data.leading N).eval 1)*sSup (J.data.blockGainValues N)`.

Use: `chebyshev2.Jacobi.normalized_gain_interval_independent` rewrites with this identity
to establish the identity `I.delta*J.gain I (J.admissible I hN ht) / ((N:ℝ)^(3/2:ℝ)*I.epsilon
N) = K.delta*J.gain K (J.admissible K hN ht) / ((N:ℝ)^(3/2:ℝ)*K.epsilon N)`.

Article: chebyshev2, Theorem 2.2.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem normalized_gain (hN : 0 < N) (ht : J.Terminal) :
    I.delta*J.gain I (J.admissible I hN ht) /
      ((N:ℝ)^(3/2:ℝ)*I.epsilon N) =
    2/((N:ℝ)^(3/2:ℝ)*(J.data.leading N).eval 1)*sSup (J.data.blockGainValues N) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  rw [J.gain_formula I]
  have hr := J.endpoint_ratio I hN ht
  have hn : (N:ℝ)^(3/2:ℝ) ≠ 0 := Real.rpow_pos_of_pos (by exact_mod_cast hN) _ |>.ne'
  have hd := (J.admissible I hN ht N le_rfl).ne'
  have he : I.epsilon N ≠ 0 := one_div_ne_zero (I.den_ne N)
  field_simp [hn, hd, he, I.delta_pos.ne', (J.leading_endpoint_pos hN ht).ne'] at hr ⊢
  rw [hr]

/--
Exact identity `I.delta*J.gain I (J.admissible I hN ht) / ((N:ℝ)^(3/2:ℝ)*I.epsilon N) =
K.delta*J.gain K (J.admissible K hN ht) / ((N:ℝ)^(3/2:ℝ)*K.epsilon N)`.

Use: `chebyshev2.Optimal.finiteGain_interval_independent` uses this identity to establish
exact identity `finiteGain I n = finiteGain K n`.

Article: chebyshev2, Theorem 2.2.

Proof: Use the identities/estimates `chebyshev2.Jacobi.normalized_gain` with the arguments
shown in the proof.
-/
theorem normalized_gain_interval_independent (K : SpectralInterval) (hN : 0 < N)
    (ht : J.Terminal) :
    I.delta*J.gain I (J.admissible I hN ht) / ((N:ℝ)^(3/2:ℝ)*I.epsilon N) =
      K.delta*J.gain K (J.admissible K hN ht) / ((N:ℝ)^(3/2:ℝ)*K.epsilon N) := by rw [J.normalized_gain I hN ht, J.normalized_gain K hN ht]

end
end chebyshev2.Jacobi
