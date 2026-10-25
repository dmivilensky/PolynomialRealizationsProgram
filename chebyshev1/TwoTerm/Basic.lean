import chebyshev1.Prefix.Exactness
import chebyshev1.Chebyshev.Polynomial

/-!
Article: chebyshev1, Theorem C.1.
A causal two-term one-gradient recurrence; time zero uses only `gamma 0`.
Use: `chebyshev1.TwoTerm.transfer_recurrence` feeds `chebyshev1.TwoTerm.coefficients_unique`
(Theorem C.1, for every used noninitial time).
Proof chain: `chebyshev1.TwoTerm.coefficients_unique_explicit` — chebyshev1, Theorem C.1;
Local uniqueness of the causal two-term realization.
-/
namespace chebyshev1
noncomputable section
open scoped Matrix BigOperators

/--
A causal two-term one-gradient recurrence; time zero uses only `gamma 0`.

Use: `chebyshev1.TwoTerm.previous_transfer` uses this record of data and proof obligations
to establish the identity `orderedProduct (fun s => S.realization.scalarStep s lam) (n + 1) 1
0 = S.realization.scalarTransfer n lam`.

Article: chebyshev1, Theorem 3.1 via `chebyshev1.TwoTerm.kernel_eq_prefix`.
-/
structure TwoTerm where
  /-- Coefficient multiplying the current error in the two-term recurrence. -/
  a : ℕ → ℝ
  /-- Coefficient multiplying the preceding error, representing momentum/memory. -/
  b : ℕ → ℝ
  /-- Stepsize coefficient multiplying the Hessian action; positivity is imposed by the relevant admissibility hypotheses. -/
  gamma : ℕ → ℝ

namespace TwoTerm

/--
Constructs `realization` of type `Realization (Fin 2)` by the displayed record fields. Data
fields specify the construction; proof fields discharge its required properties.

Use: `chebyshev1.TwoTerm.queryFactor` rewrites with this definition to establish exact
identity `S.realization.queryFactor t = !![S.gamma t, 0; 0, 0]`.

Article: chebyshev1, Theorem 3.1 via `chebyshev1.TwoTerm.kernel_eq_prefix`.
-/
def realization (S : TwoTerm) : Realization (Fin 2) where
  b := ![1, 0]
  readout := ![1, 0]
  P := fun t => if t = 0 then !![1, 0; 1, 0] else !![S.a t, S.b t; 1, 0]
  g := fun t => ![S.gamma t, 0]
  q := fun _ => ![1, 0]

/--
Defines `PrefixExact` of type `Prop` by `∀ t ≤ N, ∀ lam ∈ Set.Icc I.mu I.L,
S.realization.scalarTransfer t lam = (I.residual t).eval lam`.

Use: `chebyshev1.TwoTerm.coefficients_unique` uses this definition to establish exact
identity `S.a t = 1 + Prefix.beta I t ∧ S.b t = -Prefix.beta I t ∧ S.gamma t = Prefix.gamma I
t`.

Article: chebyshev1, Theorem 3.1 via `chebyshev1.TwoTerm.kernel_eq_prefix`.
-/
def PrefixExact (S : TwoTerm) (I : SpectralInterval) (N : ℕ) : Prop :=
  ∀ t ≤ N, ∀ lam ∈ Set.Icc I.mu I.L,
    S.realization.scalarTransfer t lam = (I.residual t).eval lam

/--
Exact identity `S.realization.scalarContract M = M 0 0`.

Use: `chebyshev1.TwoTerm.transfer_recurrence` rewrites with this identity to establish
exact identity `S.realization.scalarTransfer (n + 2) lam = (S.a (n + 1) - S.gamma (n + 1) *
lam) * S.realization.scalarTransfer (n + 1) lam + S.b (n + 1) * S.realization.scalarTransfer n
lam`.

Article: chebyshev1, Theorem 3.1 via `chebyshev1.TwoTerm.kernel_eq_prefix`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
@[simp] theorem scalarContract (S : TwoTerm) (M : Matrix (Fin 2) (Fin 2) ℝ) :
    S.realization.scalarContract M = M 0 0 := by simp [Realization.scalarContract, realization, Fin.sum_univ_two]

/--
Exact identity `S.realization.queryFactor t = !![S.gamma t, 0; 0, 0]`.

Use: `chebyshev1.TwoTerm.kernel_eq_prefix` rewrites with this identity to establish exact
identity `S.realization.kernel N s lam nu = (Prefix.realization I).kernel N s lam nu`.

Article: chebyshev1, Theorem 3.1 via `chebyshev1.TwoTerm.kernel_eq_prefix`.

Proof: Check each member of the finite index type; no case is omitted.
-/
@[simp] theorem queryFactor (S : TwoTerm) (t : ℕ) :
    S.realization.queryFactor t = !![S.gamma t, 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Realization.queryFactor, realization, Matrix.vecMulVec]

/--
Exact identity `S.realization.scalarStep 0 lam = !![1 - S.gamma 0 * lam, 0; 1, 0]`.

Use: `chebyshev1.TwoTerm.previous_transfer` rewrites with this identity to establish exact
identity `orderedProduct (fun s => S.realization.scalarStep s lam) (n + 1) 1 0 =
S.realization.scalarTransfer n lam`.

Article: chebyshev1, Theorem 3.1 via `chebyshev1.TwoTerm.kernel_eq_prefix`.

Proof: Check each member of the finite index type; no case is omitted.
-/
theorem scalarStep_zero (S : TwoTerm) (lam : ℝ) :
    S.realization.scalarStep 0 lam = !![1 - S.gamma 0 * lam, 0; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Realization.scalarStep, Realization.queryFactor, realization, Matrix.vecMulVec, mul_comm]

/--
Exact identity `S.realization.scalarStep (t + 1) lam = !![S.a (t + 1) - S.gamma (t + 1) * lam,
S.b (t + 1); 1, 0]`.

Use: `chebyshev1.TwoTerm.previous_transfer` rewrites with this identity to establish exact
identity `orderedProduct (fun s => S.realization.scalarStep s lam) (n + 1) 1 0 =
S.realization.scalarTransfer n lam`.

Article: chebyshev1, Theorem 3.1 via `chebyshev1.TwoTerm.kernel_eq_prefix`.

Proof: Check each member of the finite index type; no case is omitted.
-/
theorem scalarStep_succ (S : TwoTerm) (t : ℕ) (lam : ℝ) :
    S.realization.scalarStep (t + 1) lam =
      !![S.a (t + 1) - S.gamma (t + 1) * lam, S.b (t + 1); 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Realization.scalarStep, Realization.queryFactor, realization, Matrix.vecMulVec, mul_comm]

/--
Exact identity `S.realization.scalarTransfer 1 lam = 1 - S.gamma 0 * lam`.

Use: `chebyshev1.TwoTerm.initial_unique` rewrites with this identity to establish exact
identity `S.gamma 0 = 2 / (I.L + I.mu)`.

Article: chebyshev1, Theorem 3.1 via `chebyshev1.TwoTerm.kernel_eq_prefix`.

Proof: Use the identities/estimates `chebyshev1.TwoTerm.scalarStep_zero` with the arguments
shown in the proof.
-/
theorem transfer_one (S : TwoTerm) (lam : ℝ) :
    S.realization.scalarTransfer 1 lam = 1 - S.gamma 0 * lam := by simp [Realization.scalarTransfer, orderedProduct, scalarStep_zero]

/--
Exact identity `orderedProduct (fun s => S.realization.scalarStep s lam) (n + 1) 1 0 =
S.realization.scalarTransfer n lam`.

Use: `chebyshev1.TwoTerm.transfer_recurrence` rewrites with this identity to establish
exact identity `S.realization.scalarTransfer (n + 2) lam = (S.a (n + 1) - S.gamma (n + 1) *
lam) * S.realization.scalarTransfer (n + 1) lam + S.b (n + 1) * S.realization.scalarTransfer n
lam`.

Article: chebyshev1, Theorem C.1 via `chebyshev1.TwoTerm.coefficients_unique_explicit`.

Proof: Use the identities/estimates `chebyshev1.TwoTerm.scalarStep_zero`,
`chebyshev1.orderedProduct_succ`, `chebyshev1.TwoTerm.scalarStep_succ` with the
arguments shown in the proof.
-/
theorem previous_transfer (S : TwoTerm) (n : ℕ) (lam : ℝ) :
    orderedProduct (fun s => S.realization.scalarStep s lam) (n + 1) 1 0 =
      S.realization.scalarTransfer n lam := by
  cases n with
  | zero => simp [orderedProduct, scalarStep_zero, Realization.scalarTransfer]
  | succ n =>
    rw [orderedProduct_succ, scalarStep_succ]
    simp [Matrix.mul_apply, Fin.sum_univ_two, Realization.scalarTransfer]

/--
Exact identity `S.realization.scalarTransfer (n + 2) lam = (S.a (n + 1) - S.gamma (n + 1) *
lam) * S.realization.scalarTransfer (n + 1) lam + S.b (n + 1) * S.realization.scalarTransfer n
lam`.

Use: `chebyshev1.TwoTerm.coefficients_unique` rewrites with this identity to establish
exact identity `S.a t = 1 + Prefix.beta I t ∧ S.b t = -Prefix.beta I t ∧ S.gamma t =
Prefix.gamma I t`.

Article: chebyshev1, Theorem C.1 via `chebyshev1.TwoTerm.coefficients_unique_explicit`.

Proof: Use the identities/estimates `chebyshev1.TwoTerm.scalarContract`,
`chebyshev1.orderedProduct_succ`, `chebyshev1.TwoTerm.scalarStep_succ` with the
arguments shown in the proof.
-/
theorem transfer_recurrence (S : TwoTerm) (n : ℕ) (lam : ℝ) :
    S.realization.scalarTransfer (n + 2) lam =
      (S.a (n + 1) - S.gamma (n + 1) * lam) * S.realization.scalarTransfer (n + 1) lam +
      S.b (n + 1) * S.realization.scalarTransfer n lam := by
  -- Use the identities/estimates `chebyshev1.TwoTerm.scalarContract`,
  -- `chebyshev1.orderedProduct_succ`, `chebyshev1.TwoTerm.scalarStep_succ` with the
  -- arguments shown in the proof.
  simp only [Realization.scalarTransfer, scalarContract]
  rw [orderedProduct_succ, scalarStep_succ]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [previous_transfer]
  simp [Realization.scalarTransfer]

end TwoTerm
end
end chebyshev1
