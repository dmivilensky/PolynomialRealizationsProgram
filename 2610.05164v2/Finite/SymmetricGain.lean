import «2610.05164v2».Finite.Normalization
import «2610.05164v2».SineJacobi.Finite

/-!
Article: 2610.05164v2, Corollary 1.
Corollary 1: the lower bound is already attained by scalar symmetric perturbations.
Use: `«2610.05164v2».SineJacobi.symmetric_gain_exact` feeds
`«2610.05164v2».SineJacobi.normalized_symmetric_gain_exact` (normalized symmetric gain exact).
-/
namespace «2610.05164v2».Recurrence
noncomputable section
open «2606.16671v2» Matrix
open scoped BigOperators Matrix
variable {N : ℕ} (R : Recurrence N) (I : SpectralInterval)

/--
Definition 1 with symmetric perturbations, allowing every positive finite dimension.

Use: `«2610.05164v2».Recurrence.symmetricGain` uses this definition in the displayed
construction of `symmetricGain`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Corollary 1 via `«2610.05164v2».Jacobi.symmetric_gain_bounds`.
-/
def symmetricGainValues : Set ℝ := {a | ∃ p : ℕ, 0 < p ∧
  ∃ H : Matrix (Fin p) (Fin p) ℝ, H.IsHermitian ∧ spectrum ℝ H ⊆ Set.Icc I.mu I.L ∧
  ∃ E : ℕ → Matrix (Fin p) (Fin p) ℝ, (∀ s < N, (E s).IsHermitian) ∧
    0 < Real.sqrt (∑ s ∈ Finset.range N, hsNorm (E s)^2) ∧
    a = hsNorm (R.method.realization.linearResponse N H E) /
      Real.sqrt (∑ s ∈ Finset.range N, hsNorm (E s)^2)}

/--
Defines `symmetricGain` of type `ℝ` by `sSup (R.symmetricGainValues I)`.

Use: `«2610.05164v2».Jacobi.symmetric_gain_bounds` uses this definition to establish the bound
stated in that declaration.

Article: 2610.05164v2, Corollary 1 via `«2610.05164v2».Jacobi.symmetric_gain_bounds`.
-/
def symmetricGain : ℝ := sSup (R.symmetricGainValues I)

/--
The precise assertion is `BddAbove (R.symmetricGainValues I)`.

Use: `«2610.05164v2».Jacobi.symmetric_gain_bounds` uses this assertion to establish the bound
stated in that declaration.

Article: 2610.05164v2, Corollary 1 via `«2610.05164v2».Jacobi.symmetric_gain_bounds`.

Proof: Use the identities/estimates `«2606.16671v2».Realization.hsNorm_linearResponse_bound`
with the arguments shown in the proof.
-/
theorem symmetricGainValues_bddAbove : BddAbove (R.symmetricGainValues I) := by
  refine ⟨R.method.realization.gain I N, ?_⟩
  rintro a ⟨p,_,H,hH,hs,E,_,hp,rfl⟩
  apply (div_le_iff₀ hp).mpr
  exact R.method.realization.hsNorm_linearResponse_bound I N H hH hs E

/--
The stated quantitative bound `R.symmetricGain I ≤ R.method.realization.gain I N`.

Use: `«2610.05164v2».Jacobi.symmetric_gain_bounds` uses this bound to establish the bound
stated in that declaration.

Article: 2610.05164v2, Corollary 1 via `«2610.05164v2».Jacobi.symmetric_gain_bounds`.

Proof: Use the identities/estimates `«2606.16671v2».Realization.hsNorm_linearResponse_bound`
with the arguments shown in the proof.
-/
theorem symmetricGain_le (hn : (R.symmetricGainValues I).Nonempty) :
    R.symmetricGain I ≤ R.method.realization.gain I N := by
  apply csSup_le hn
  rintro a ⟨p,_,H,hH,hs,E,_,hp,rfl⟩
  apply (div_le_iff₀ hp).mpr
  exact R.method.realization.hsNorm_linearResponse_bound I N H hH hs E

/--
Defines `scalarWitness` of type `(s : ℕ)` by `«2606.16671v2».scalarMatrix
(R.method.realization.kernel N s I.mu I.mu)`.

Use: `«2610.05164v2».Recurrence.endpoint_mem_symmetricGainValues` rewrites with this definition
to establish membership in the specified domain/enclosure: `R.method.realization.kernelNorm N
I.mu I.mu ∈ R.symmetricGainValues I`.

Article: 2610.05164v2, Corollary 1 via `«2610.05164v2».Jacobi.symmetric_gain_bounds`.
-/
def scalarWitness (s : ℕ) := «2606.16671v2».scalarMatrix (R.method.realization.kernel N s I.mu I.mu)

/--
Exact identity `hsNorm («2606.16671v2».scalarMatrix c) = |c|`.

Use: `«2610.05164v2».Recurrence.scalarWitness_input` rewrites with this identity to establish
exact identity `Real.sqrt (∑ s ∈ Finset.range N, hsNorm (R.scalarWitness I s)^2) =
R.method.realization.kernelNorm N I.mu I.mu`.

Article: 2610.05164v2, Corollary 1 via `«2610.05164v2».Jacobi.symmetric_gain_bounds`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem hsNorm_scalarMatrix (c : ℝ) : hsNorm («2606.16671v2».scalarMatrix c) = |c| := by simp [hsNorm, hsSq, «2606.16671v2».scalarMatrix, Real.sqrt_sq_eq_abs]

/--
Exact identity `Real.sqrt (∑ s ∈ Finset.range N, hsNorm (R.scalarWitness I s)^2) =
R.method.realization.kernelNorm N I.mu I.mu`.

Use: `«2610.05164v2».Recurrence.endpoint_mem_symmetricGainValues` rewrites with this identity
to establish membership in the specified domain/enclosure: `R.method.realization.kernelNorm N
I.mu I.mu ∈ R.symmetricGainValues I`.

Article: 2610.05164v2, Corollary 1 via `«2610.05164v2».Jacobi.symmetric_gain_bounds`.

Proof: Use the identities/estimates `«2610.05164v2».Recurrence.hsNorm_scalarMatrix` with the
arguments shown in the proof.
-/
theorem scalarWitness_input : Real.sqrt (∑ s ∈ Finset.range N, hsNorm (R.scalarWitness I s)^2) =
    R.method.realization.kernelNorm N I.mu I.mu := by
  simp only [scalarWitness, hsNorm_scalarMatrix, sq_abs]
  rfl

/--
Exact identity `hsNorm (R.method.realization.linearResponse N («2606.16671v2».scalarMatrix
I.mu) (R.scalarWitness I)) = (R.method.realization.kernelNorm N I.mu I.mu)^2`.

Use: `«2610.05164v2».Recurrence.endpoint_mem_symmetricGainValues` rewrites with this identity
to establish membership in the specified domain/enclosure: `R.method.realization.kernelNorm N
I.mu I.mu ∈ R.symmetricGainValues I`.

Article: 2610.05164v2, Corollary 1 via `«2610.05164v2».Jacobi.symmetric_gain_bounds`.

Proof: Check each member of the finite index type; no case is omitted.
-/
theorem scalarWitness_output :
    hsNorm (R.method.realization.linearResponse N («2606.16671v2».scalarMatrix I.mu)
      (R.scalarWitness I)) = (R.method.realization.kernelNorm N I.mu I.mu)^2 := by
  -- Check each member of the finite index type; no case is omitted.
  have he : R.method.realization.linearResponse N («2606.16671v2».scalarMatrix I.mu)
      (R.scalarWitness I) = «2606.16671v2».scalarMatrix
        (∑ s ∈ Finset.range N, R.method.realization.kernel N s I.mu I.mu^2) := by
    ext i j
    fin_cases i; fin_cases j
    simp [«2606.16671v2».scalarMatrix, Realization.diagonal_linearResponse_entry,
      scalarWitness, pow_two]
  rw [he, hsNorm_scalarMatrix, abs_of_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  exact (Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))).symm

/--
Membership in the specified domain/enclosure: `R.method.realization.kernelNorm N I.mu I.mu ∈
R.symmetricGainValues I`.

Use: `«2610.05164v2».Jacobi.symmetric_gain_bounds` uses this assertion to establish the bound
stated in that declaration.

Article: 2610.05164v2, Corollary 1 via `«2610.05164v2».Jacobi.symmetric_gain_bounds`.

Proof: Use the identities/estimates `«2610.05164v2».Recurrence.scalarWitness_input`,
`«2610.05164v2».Recurrence.scalarWitness_output` with the arguments shown in the proof.
-/
theorem endpoint_mem_symmetricGainValues (hp : 0 < R.method.realization.kernelNorm N I.mu I.mu) :
    R.method.realization.kernelNorm N I.mu I.mu ∈ R.symmetricGainValues I := by
  -- Use the identities/estimates `«2610.05164v2».Recurrence.scalarWitness_input`,
  -- `«2610.05164v2».Recurrence.scalarWitness_output` with the arguments shown in the proof.
  refine ⟨1,by norm_num,«2606.16671v2».scalarMatrix I.mu,?_,?_,R.scalarWitness I,?_,?_,?_⟩
  · simp [«2606.16671v2».scalarMatrix, Matrix.IsHermitian]
  · rw [«2606.16671v2».scalarMatrix, spectrum_diagonal]
    rintro x ⟨i,rfl⟩; exact ⟨le_rfl,I.mu_lt_L.le⟩
  · intro s _; simp [scalarWitness, «2606.16671v2».scalarMatrix, Matrix.IsHermitian]
  · rw [R.scalarWitness_input I]; exact hp
  · rw [R.scalarWitness_input I, R.scalarWitness_output I, pow_two, mul_div_cancel_right₀ _ hp.ne']

end
end «2610.05164v2».Recurrence

namespace «2610.05164v2».Jacobi
noncomputable section
open «2606.16671v2»
variable {N : ℕ} (J : Jacobi N) (I : SpectralInterval)

/--
Corollary 1: the lower bound is already attained by scalar symmetric perturbations.

The stated quantitative bound `2*I.epsilon N/I.delta*Real.sqrt J.energy ≤ (J.recurrence I
(J.admissible I hN ht)).symmetricGain I ∧ (J.recurrence I (J.admissible I hN ht)).symmetricGain
I ≤ J.gain I (J.admissible I hN ht)`.

Use: `«2610.05164v2».SineJacobi.symmetric_gain_exact` uses this bound to establish exact
identity `((recurrenceEquiv I N hN) (fiber N hN)).val.symmetricGain I = 2*I.epsilon
N/I.delta*Real.sqrt (chain N).energy`.

Article: 2610.05164v2, Corollary 1.

Proof: Use the identities/estimates `«2610.05164v2».Jacobi.admissible`,
`«2610.05164v2».Horizon.kernelNorm_eq`, `«2610.05164v2».Jacobi.recurrence_agree` with the
arguments shown in the proof.
-/
theorem symmetric_gain_bounds (hN : 0 < N) (ht : J.Terminal) :
    2*I.epsilon N/I.delta*Real.sqrt J.energy ≤
      (J.recurrence I (J.admissible I hN ht)).symmetricGain I ∧
    (J.recurrence I (J.admissible I hN ht)).symmetricGain I ≤ J.gain I (J.admissible I hN ht) := by
  -- Use the identities/estimates `«2610.05164v2».Jacobi.admissible`,
  -- `«2610.05164v2».Horizon.kernelNorm_eq`, `«2610.05164v2».Jacobi.recurrence_agree` with the
  -- arguments shown in the proof.
  let R := J.recurrence I (J.admissible I hN ht)
  have he : R.method.realization.kernelNorm N I.mu I.mu =
      2*I.epsilon N/I.delta*Real.sqrt J.energy := by
    rw [Horizon.kernelNorm_eq (J.recurrence_agree I (J.admissible I hN ht))]
    exact J.endpoint_norm I hN ht
  have hp : 0 < R.method.realization.kernelNorm N I.mu I.mu := by
    rw [he]
    exact mul_pos (div_pos (mul_pos (by norm_num) (one_div_pos.mpr (I.den_pos N))) I.delta_pos)
      (Real.sqrt_pos.mpr (J.energy_pos hN ht))
  have hm := R.endpoint_mem_symmetricGainValues I hp
  refine ⟨?_, R.symmetricGain_le I ⟨_,hm⟩⟩
  rw [← he]
  exact le_csSup (R.symmetricGainValues_bddAbove I) hm

end
end «2610.05164v2».Jacobi

namespace «2610.05164v2».SineJacobi
noncomputable section
open «2606.16671v2»

/--
Exact identity `((recurrenceEquiv I N hN) (fiber N hN)).val.symmetricGain I = 2*I.epsilon
N/I.delta*Real.sqrt (chain N).energy`.

Use: `«2610.05164v2».SineJacobi.normalized_symmetric_gain_exact` rewrites with this identity to
establish exact identity `((recurrenceEquiv I N hN) (fiber N hN)).val.normalizedSymmetricGain I
= 2*sqrt (chain N).normalizedEnergy`.

Article: 2610.05164v2, Corollary 1.

Proof: Use the identities/estimates `«2610.05164v2».SineJacobi.terminal`,
`«2610.05164v2».Jacobi.symmetric_gain_bounds`, `«2610.05164v2».SineJacobi.gain_exact` with the
arguments shown in the proof.
-/
theorem symmetric_gain_exact (I : SpectralInterval) (N : ℕ) (hN : 0 < N) :
    ((recurrenceEquiv I N hN) (fiber N hN)).val.symmetricGain I =
      2*I.epsilon N/I.delta*Real.sqrt (chain N).energy := by
  obtain ⟨hl,hu⟩ := (chain N).symmetric_gain_bounds I hN (terminal N hN)
  apply le_antisymm ?_ hl
  exact hu.trans_eq (gain_exact I N hN)

end
end «2610.05164v2».SineJacobi
