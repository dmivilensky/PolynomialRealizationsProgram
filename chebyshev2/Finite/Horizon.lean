import chebyshev2.Finite.Basic
import chebyshev1.Realization.GainBounds
import chebyshev1.Realization.Expansion

/-!
Article: chebyshev2, Theorem 2.2.
Canonical extension of a finite recurrence.
Use: `chebyshev2.Horizon.linearResponse_eq` feeds `chebyshev2.Jacobi.derivative_formula`
(Lemma 2: the block formula for the actual derivative of the finite recurrence).
Proof chain: `chebyshev2.Jacobi.derivative_formula` — chebyshev2, Theorem 2.2; Sharp gain
formula, derivative and attaining examples.
-/
namespace chebyshev2.Horizon
noncomputable section
open chebyshev1
set_option backward.isDefEq.respectTransparency false

/--
Exact identity `S = T`.

Use: `chebyshev2.Recurrence.ext_of_agree` uses this identity to establish the identity `R
= S`.

Article: chebyshev2, Theorem 2.1 via `chebyshev2.recurrenceEquiv`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
@[ext] theorem twoTerm_ext {S T : TwoTerm} (ha : S.a = T.a) (hb : S.b = T.b)
    (hg : S.gamma = T.gamma) : S = T := by cases S; cases T; simp_all

/--
Exact identity `J = K`.

Use: `chebyshev2.Jacobi.jacobi_recurrence` uses this identity to establish the identity
`(J.recurrence I h).jacobi I = J`.

Article: chebyshev2, Theorem 2.1 via `chebyshev2.recurrenceEquiv`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
@[ext] theorem jacobiData_ext {J K : JacobiData} (hb : J.b = K.b)
    (ha : J.aSq = K.aSq) : J = K := by cases J; cases K; simp_all

/--
Canonical extension of a finite recurrence.

Use: `chebyshev2.Horizon.truncate_agree` rewrites with this definition to establish the
precise assertion is `Agree N (truncate N S) S`.

Article: chebyshev2, Theorem 2.1 via `chebyshev2.Jacobi.recurrence`.
-/
def truncate (N : ℕ) (S : TwoTerm) : TwoTerm where
  a i := if i < N then S.a i else 1
  b i := if i < N then S.b i else 0
  gamma i := if i < N then S.gamma i else 1

/--
Defines `Agree` of type `Prop` by `∀ i < N, S.a i = T.a i ∧ S.b i = T.b i ∧ S.gamma i = T.gamma
i`.

Use: `chebyshev2.Horizon.gain_eq` uses this definition to establish the identity
`S.realization.gain I N = T.realization.gain I N`.

Article: chebyshev2, Theorem 2.5 via `chebyshev2.SineJacobi.gain_exact`.
-/
def Agree (N : ℕ) (S T : TwoTerm) : Prop :=
  ∀ i < N, S.a i = T.a i ∧ S.b i = T.b i ∧ S.gamma i = T.gamma i

/--
The precise assertion is `Agree N (truncate N S) S`.

Use: `chebyshev2.Jacobi.recurrence_agree` uses this assertion to establish the precise
assertion is `Horizon.Agree N (J.recurrence I h).method (J.data.method I)`.

Article: chebyshev2, Theorem 2.5 via `chebyshev2.SineJacobi.gain_exact`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem truncate_agree (N : ℕ) (S : TwoTerm) : Agree N (truncate N S) S := by intro i hi; simp [truncate, hi]

/--
Exact identity `S.realization.scalarStep i x = T.realization.scalarStep i x`.

Use: `chebyshev2.Horizon.kernel_eq` uses this identity to establish the identity
`S.realization.kernel N s x y = T.realization.kernel N s x y`.

Article: chebyshev2, Theorem 2.1 via `chebyshev2.Jacobi.residual_eq`.

Proof: Use the identities/estimates `chebyshev1.TwoTerm.scalarStep_zero`,
`chebyshev1.TwoTerm.scalarStep_succ` with the arguments shown in the proof.
-/
theorem step_eq {N : ℕ} {S T : TwoTerm} (h : Agree N S T) {i : ℕ} (hi : i < N)
    (x : ℝ) : S.realization.scalarStep i x = T.realization.scalarStep i x := by
  obtain ⟨ha,hb,hg⟩ := h i hi
  cases i with
  | zero => simp only [TwoTerm.scalarStep_zero, hg]
  | succ i => simp only [TwoTerm.scalarStep_succ, ha, hb, hg]

/--
Exact identity `S.realization.scalarTransfer n x = T.realization.scalarTransfer n x`.

Use: `chebyshev2.Horizon.residual_eq` uses this identity to establish the identity
`S.realization.residualPolynomial n = T.realization.residualPolynomial n`.

Article: chebyshev2, Theorem 2.1 via `chebyshev2.Jacobi.residual_eq`.

Proof: Use the identities/estimates `chebyshev1.TwoTerm.scalarContract`,
`chebyshev1.orderedProduct_congr`, `chebyshev2.Horizon.step_eq` with the arguments
shown in the proof.
-/
theorem transfer_eq {N : ℕ} {S T : TwoTerm} (h : Agree N S T) {n : ℕ}
    (hn : n ≤ N) (x : ℝ) :
    S.realization.scalarTransfer n x = T.realization.scalarTransfer n x := by
  simp only [Realization.scalarTransfer, TwoTerm.scalarContract]
  rw [orderedProduct_congr (fun i hi => step_eq h (by omega) x)]

/--
Exact identity `S.realization.residualPolynomial n = T.realization.residualPolynomial n`.

Use: `chebyshev2.Jacobi.residual_eq` rewrites with this identity to establish exact
identity `(J.recurrence I h).method.realization.residualPolynomial n = J.data.residual I n`.

Article: chebyshev2, Theorem 2.1 via `chebyshev2.Jacobi.residual_eq`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem residual_eq {N : ℕ} {S T : TwoTerm} (h : Agree N S T) {n : ℕ}
    (hn : n ≤ N) : S.realization.residualPolynomial n = T.realization.residualPolynomial n := by
  apply Polynomial.funext
  intro x
  simp only [Realization.residualPolynomial_eval]
  exact transfer_eq h hn x

/--
Exact identity `S.realization.kernel N s x y = T.realization.kernel N s x y`.

Use: `chebyshev2.Horizon.kernelNorm_eq` rewrites with this identity to establish exact
identity `S.realization.kernelNorm N x y = T.realization.kernelNorm N x y`.

Article: chebyshev2, Corollary 1 via `chebyshev2.Jacobi.symmetric_gain_bounds`.

Proof: Use the identities/estimates `chebyshev1.orderedProduct_congr`,
`chebyshev2.Horizon.step_eq`, `chebyshev1.TwoTerm.queryFactor` with the arguments shown
in the proof.
-/
theorem kernel_eq {N : ℕ} {S T : TwoTerm} (h : Agree N S T) {s : ℕ}
    (hs : s < N) (x y : ℝ) : S.realization.kernel N s x y = T.realization.kernel N s x y := by
  -- Use the identities/estimates `chebyshev1.orderedProduct_congr`,
  -- `chebyshev2.Horizon.step_eq`, `chebyshev1.TwoTerm.queryFactor` with the arguments
  -- shown in the proof.
  have ht : orderedProduct (fun i => S.realization.scalarStep (s+1+i) x) (N-(s+1)) =
      orderedProduct (fun i => T.realization.scalarStep (s+1+i) x) (N-(s+1)) :=
    orderedProduct_congr (fun i hi => step_eq h (by omega) x)
  have hp : orderedProduct (fun i => S.realization.scalarStep i y) s =
      orderedProduct (fun i => T.realization.scalarStep i y) s :=
    orderedProduct_congr (fun i hi => step_eq h (by omega) y)
  simp only [Realization.kernel, TwoTerm.scalarContract, TwoTerm.queryFactor]
  simp only [ht, hp, (h s hs).2.2]

/--
Exact identity `S.realization.kernelNorm N x y = T.realization.kernelNorm N x y`.

Use: `chebyshev2.Horizon.gain_eq` rewrites with this identity to establish the identity
`S.realization.gain I N = T.realization.gain I N`.

Article: chebyshev2, Corollary 1 via `chebyshev2.Jacobi.symmetric_gain_bounds`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem kernelNorm_eq {N : ℕ} {S T : TwoTerm} (h : Agree N S T) (x y : ℝ) :
    S.realization.kernelNorm N x y = T.realization.kernelNorm N x y := by
  unfold Realization.kernelNorm
  apply congrArg Real.sqrt
  apply Finset.sum_congr rfl
  intro s hs
  rw [kernel_eq h (Finset.mem_range.mp hs)]

/--
Exact identity `S.realization.gain I N = T.realization.gain I N`.

Use: `chebyshev2.Jacobi.gain_eq` uses this identity to establish the identity `J.gain I h
= (J.data.realization I).gain I N`.

Article: chebyshev2, Theorem 2.5 via `chebyshev2.SineJacobi.gain_exact`.

Proof: Use the identities/estimates `chebyshev2.Horizon.kernelNorm_eq` with the arguments
shown in the proof.
-/
theorem gain_eq {N : ℕ} {S T : TwoTerm} (h : Agree N S T) (I : SpectralInterval) :
    S.realization.gain I N = T.realization.gain I N := by simp only [Realization.gain, Realization.gainValues, kernelNorm_eq h]

/--
Exact identity `S.realization.operatorStep i H = T.realization.operatorStep i H`.

Use: `chebyshev2.Horizon.linearResponse_eq` uses this identity to establish the identity
`S.realization.linearResponse N H E = T.realization.linearResponse N H E`.

Article: chebyshev2, Theorem 2.2 via `chebyshev2.Jacobi.derivative_formula`.

Proof: Use the identities/estimates `chebyshev1.TwoTerm.queryFactor` with the arguments
shown in the proof.
-/
theorem operator_step_eq {d : Type*} [Fintype d] [DecidableEq d]
    {N : ℕ} {S T : TwoTerm} (h : Agree N S T) {i : ℕ} (hi : i < N)
    (H : Matrix d d ℝ) : S.realization.operatorStep i H = T.realization.operatorStep i H := by
  have hp : S.realization.P i = T.realization.P i := by
    simp [TwoTerm.realization, (h i hi).1, (h i hi).2.1]
  have hq : S.realization.queryFactor i = T.realization.queryFactor i := by
    simp only [TwoTerm.queryFactor, (h i hi).2.2]
  simp only [Realization.operatorStep, hp, hq]

/--
Exact identity `S.realization.linearResponse N H E = T.realization.linearResponse N H E`.

Use: `chebyshev2.Jacobi.derivative_formula` rewrites with this identity to establish the
identity stated in that declaration.

Article: chebyshev2, Theorem 2.2 via `chebyshev2.Jacobi.derivative_formula`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem linearResponse_eq {d : Type*} [Fintype d] [DecidableEq d]
    {N : ℕ} {S T : TwoTerm} (h : Agree N S T)
    (H : Matrix d d ℝ) (E : ℕ → Matrix d d ℝ) :
    S.realization.linearResponse N H E = T.realization.linearResponse N H E := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  simp only [Realization.linearResponse_eq_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hsN := Finset.mem_range.mp hs
  have ht : orderedProduct (fun i => S.realization.operatorStep (s+1+i) H) (N-(s+1)) =
      orderedProduct (fun i => T.realization.operatorStep (s+1+i) H) (N-(s+1)) :=
    orderedProduct_congr (fun i hi => operator_step_eq h (by omega) H)
  have hp : orderedProduct (fun i => S.realization.operatorStep i H) s =
      orderedProduct (fun i => T.realization.operatorStep i H) s :=
    orderedProduct_congr (fun i hi => operator_step_eq h (by omega) H)
  have hd : S.realization.operatorInsertion s (E s) = T.realization.operatorInsertion s (E s) := by
    simp only [Realization.operatorInsertion, TwoTerm.queryFactor, (h s hsN).2.2]
  rw [ht, hp, hd]
  rfl

end
end chebyshev2.Horizon
