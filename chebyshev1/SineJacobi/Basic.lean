import chebyshev1.Jacobi.Determinant

/-!
Article: chebyshev1, Theorem E.1.
The exact reflection symmetry in E.6 follows directly from the sine coefficients.
Use: `chebyshev1.SineJacobi.couplingSq_reflect` feeds
`chebyshev1.SineJacobi.data_aSq_reflect` (data a Sq reflect).
Proof chain: `chebyshev1.SineJacobi.matrix_persymmetric` — chebyshev1, Theorem E.1;
Sine-lattice couplings, spectrum, expansion and symmetry.
-/
namespace chebyshev1.SineJacobi
noncomputable section
open Real

/--
Defines `h` of type `ℝ` by `π / N`.

Use: `chebyshev1.SineJacobi.angle_mem` uses this definition to establish membership in the
specified domain/enclosure: `t * h N ∈ Set.Ioo (0 : ℝ) π`.

Article: chebyshev1, Theorem E.1 via `chebyshev1.SineJacobi.couplingSq_pos`.
-/
def h (N : ℕ) : ℝ := π / N
/--
Defines `couplingSq` of type `ℝ` by `(1 / 4) * sin ((s : ℝ) * h N) ^ 2 / (sin (((s : ℝ) - 1 /
2) * h N) * sin (((s : ℝ) + 1 / 2) * h N))`.

Use: `chebyshev1.SineJacobi.couplingSq_reflect` uses this definition to establish exact
identity `couplingSq N (N - s) = couplingSq N s`.

Article: chebyshev1, Theorem E.1 via `chebyshev1.SineJacobi.couplingSq_pos`.
-/
def couplingSq (N s : ℕ) : ℝ :=
  (1 / 4) * sin ((s : ℝ) * h N) ^ 2 /
    (sin (((s : ℝ) - 1 / 2) * h N) * sin (((s : ℝ) + 1 / 2) * h N))

/--
Extend the finite chain by zero couplings outside its physical sites.

Use: `chebyshev1.SineJacobi.data_b` uses this definition to establish the identity `(data
N).b s = 0`.

Article: chebyshev1, Theorem 5.2 via `chebyshev1.SineJacobi.gain_exact`.
-/
def data (N : ℕ) : JacobiData where
  b := fun _ => 0
  aSq := fun s => if 0 < s ∧ s < N then couplingSq N s else 0

/--
Exact identity `(data N).b s = 0`.

Use: registered as a simplification rule for the displayed expression. The rule remains
available even when kernel reduction eliminates an explicit reference to this lemma.

Article: chebyshev1, Theorem E.1.

Proof: The identity follows by unfolding the definitions; no estimate or limiting argument is
involved.
-/
@[simp] theorem data_b (N s : ℕ) : (data N).b s = 0 := rfl
/--
Exact identity `(data N).aSq 0 = 0`.

Use: `chebyshev1.SineJacobi.method_initial` rewrites with this identity to establish exact
identity `((data N).method I).a 0 = 1 ∧ ((data N).method I).b 0 = 0 ∧ ((data N).method I).gamma
0 = 2/(I.L+I.mu)`.

Article: chebyshev1, Algorithm 2 via `chebyshev1.SineJacobi.method_initial`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
@[simp] theorem data_aSq_zero (N : ℕ) : (data N).aSq 0 = 0 := by simp [data]
/--
Exact identity `(data N).aSq s = couplingSq N s`.

Use: `chebyshev1.SineJacobi.data_aSq_nonneg` rewrites with this identity to establish the
stated quantitative bound `0 ≤ (data N).aSq s`.

Article: chebyshev1, Theorem E.3 via `chebyshev1.SineJacobi.endpoint_second_difference`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem data_aSq (N s : ℕ) (hs : 0 < s) (hsN : s < N) :
    (data N).aSq s = couplingSq N s := by simp [data, hs, hsN]

/--
Membership in the specified domain/enclosure: `t * h N ∈ Set.Ioo (0 : ℝ) π`.

Use: `chebyshev1.SineJacobi.couplingSq_pos` uses this assertion to establish the stated
quantitative bound `0 < couplingSq N s`.

Article: chebyshev1, Theorem E.1 via `chebyshev1.SineJacobi.couplingSq_pos`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem angle_mem (N : ℕ) (hN : 0 < N) {t : ℝ} (ht : 0 < t) (htN : t < N) :
    t * h N ∈ Set.Ioo (0 : ℝ) π := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hp : 0 < h N := div_pos pi_pos hn
  refine ⟨mul_pos ht hp, ?_⟩
  have he : (N : ℝ) * h N = π := by unfold h; field_simp
  rw [← he]
  exact mul_lt_mul_of_pos_right htN hp

/--
The stated quantitative bound `0 < sin (((s : ℝ) - 1 / 2) * h N) * sin (((s : ℝ) + 1 / 2) * h
N)`.

Use: `chebyshev1.SineJacobi.couplingSq_pos` uses this bound to establish the stated
quantitative bound `0 < couplingSq N s`.

Article: chebyshev1, Theorem E.1 via `chebyshev1.SineJacobi.couplingSq_pos`.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.angle_mem` with the arguments
shown in the proof.
-/
theorem coupling_den_pos (N s : ℕ) (hs : 0 < s) (hsN : s < N) :
    0 < sin (((s : ℝ) - 1 / 2) * h N) * sin (((s : ℝ) + 1 / 2) * h N) := by
  have hn : 0 < N := by omega
  have hs0 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hs1 : (s : ℝ) + 1 ≤ N := by exact_mod_cast hsN
  apply mul_pos
  · exact sin_pos_of_mem_Ioo (angle_mem N hn (by linarith) (by linarith))
  · exact sin_pos_of_mem_Ioo (angle_mem N hn (by linarith) (by linarith))

/--
The stated quantitative bound `0 < couplingSq N s`.

Use: `chebyshev1.SineJacobi.data_aSq_nonneg` uses this bound to establish the stated
quantitative bound `0 ≤ (data N).aSq s`.

Article: chebyshev1, Theorem E.1.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.angle_mem`,
`chebyshev1.SineJacobi.coupling_den_pos` with the arguments shown in the proof.
-/
theorem couplingSq_pos (N s : ℕ) (hs : 0 < s) (hsN : s < N) : 0 < couplingSq N s := by
  have hsin := sin_pos_of_mem_Ioo (angle_mem N (by omega)
    (show (0 : ℝ) < s by exact_mod_cast hs) (show (s : ℝ) < N by exact_mod_cast hsN))
  exact div_pos (mul_pos (by norm_num) (sq_pos_of_pos hsin)) (coupling_den_pos N s hs hsN)

/--
The stated quantitative bound `0 ≤ (data N).aSq s`.

Use: `chebyshev1.SineJacobi.admissible` uses this bound to establish the precise assertion
is `(data N).Admissible I N`.

Article: chebyshev1, Theorem E.1 via `chebyshev1.SineJacobi.spectrum_eq_nodes`.

Proof: Separate `0 < s ∧ s < N` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem data_aSq_nonneg (N s : ℕ) : 0 ≤ (data N).aSq s := by
  by_cases hs : 0 < s ∧ s < N
  · rw [data_aSq N s hs.1 hs.2]; exact (couplingSq_pos N s hs.1 hs.2).le
  · simp [data, hs]

/--
The exact reflection symmetry in E.6 follows directly from the sine coefficients.

Exact identity `couplingSq N (N - s) = couplingSq N s`.

Use: `chebyshev1.SineJacobi.data_aSq_reflect` uses this identity to establish exact
identity `(data N).aSq (N-s) = (data N).aSq s`.

Article: chebyshev1, Theorem E.1 via `chebyshev1.SineJacobi.kernel_abs_le_endpoint`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem couplingSq_reflect (N s : ℕ) (hs : 0 < s) (hsN : s < N) :
    couplingSq N (N - s) = couplingSq N s := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have he : (N : ℝ) * h N = π := by unfold h; field_simp
  unfold couplingSq
  rw [Nat.cast_sub hsN.le]
  have h0 : ((N : ℝ) - s) * h N = π - (s : ℝ) * h N := by rw [sub_mul, he]
  have hm : ((N : ℝ) - s - 1 / 2) * h N = π - ((s : ℝ) + 1 / 2) * h N := by rw [← he]; ring
  have hp : ((N : ℝ) - s + 1 / 2) * h N = π - ((s : ℝ) - 1 / 2) * h N := by rw [← he]; ring
  rw [h0, hm, hp, sin_pi_sub, sin_pi_sub, sin_pi_sub,
    mul_comm (sin (((s : ℝ) + 1 / 2) * h N)) (sin (((s : ℝ) - 1 / 2) * h N))]

end
end chebyshev1.SineJacobi
