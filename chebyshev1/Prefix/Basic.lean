import chebyshev1.Chebyshev.Normalization
import chebyshev1.Realization.Polynomial

/-!
Article: chebyshev1, Algorithm 1.
The normalized matrix is precisely the advertised two-term gradient update.
Use: `chebyshev1.Prefix.algorithmStep_succ` feeds `chebyshev1.Prefix.residual_recurrence`
(residual recurrence).
Proof chain: `chebyshev1.Prefix.quadraticError_exact` — chebyshev1, Theorem 2.1; Prefix-exact
recurrence and quadratic transfer.
-/
namespace chebyshev1.Prefix

noncomputable section
open Polynomial Polynomial.Chebyshev
open scoped Matrix BigOperators

variable (I : SpectralInterval)

/--
`beta (t+1)` is the coefficient at the paper's time `t+1`.

Use: `chebyshev1.Prefix.algorithmStep_succ` rewrites with this definition to establish
exact identity `(realization I).scalarStep (t + 1) lam = !![(1 + beta I (t + 1)) * (1 - (2 /
(I.L + I.mu)) * lam), -beta I (t + 1); 1, 0]`.

Article: chebyshev1, Theorem 2.1 via `chebyshev1.Prefix.quadraticError_exact`.
-/
def beta (t : ℕ) : ℝ := I.den (t - 1) / I.den (t + 1)
/--
Defines `gamma` by pattern matching with result type `ℕ → ℝ`. The displayed branches determine
the recursive cases and their returned values.

Use: `chebyshev1.Prefix.algorithmStep_succ` uses this definition to establish exact
identity `(realization I).scalarStep (t + 1) lam = !![(1 + beta I (t + 1)) * (1 - (2 / (I.L +
I.mu)) * lam), -beta I (t + 1); 1, 0]`.

Article: chebyshev1, Theorem 2.2 via `chebyshev1.Prefix.kernel_zero`.
-/
def gamma : ℕ → ℝ
  | 0 => 2 / (I.L + I.mu)
  | t + 1 => 4 * I.den (t + 1) / (I.delta * I.den (t + 2))

/--
Memory stores the current and previous errors; the initial previous slot is unused.

Use: `chebyshev1.Prefix.queryFactor` rewrites with this definition to establish exact
identity `(realization I).queryFactor s = !![gamma I s, 0; 0, 0]`.

Article: chebyshev1, Theorem 2.1 via `chebyshev1.Prefix.residualPolynomial_eq`.
-/
def realization : Realization (Fin 2) where
  b := ![1, 0]
  readout := ![1, 0]
  P := fun t => match t with
    | 0 => !![1, 0; 1, 0]
    | t + 1 => !![2 * I.eta * I.den (t + 1) / I.den (t + 2),
        -(I.den t / I.den (t + 2)); 1, 0]
  g := fun t => ![gamma I t, 0]
  q := fun _ => ![1, 0]

/--
Exact identity `2 * I.eta * I.den (t + 1) / I.den (t + 2) = 1 + beta I (t + 1)`.

Use: `chebyshev1.Prefix.algorithmStep_succ` rewrites with this identity to establish exact
identity `(realization I).scalarStep (t + 1) lam = !![(1 + beta I (t + 1)) * (1 - (2 / (I.L +
I.mu)) * lam), -beta I (t + 1); 1, 0]`.

Article: chebyshev1, Theorem C.1 via `chebyshev1.TwoTerm.local_unique`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem beta_coefficient (t : ℕ) :
    2 * I.eta * I.den (t + 1) / I.den (t + 2) = 1 + beta I (t + 1) := by
  simp only [beta, Nat.add_sub_cancel]
  have h := I.den_add_two t
  field_simp [I.den_ne (t + 2)]
  linarith

/--
Exact identity `gamma I (t + 1) = (1 + beta I (t + 1)) * (2 / (I.L + I.mu))`.

Use: `chebyshev1.Prefix.algorithmStep_succ` rewrites with this identity to establish exact
identity `(realization I).scalarStep (t + 1) lam = !![(1 + beta I (t + 1)) * (1 - (2 / (I.L +
I.mu)) * lam), -beta I (t + 1); 1, 0]`.

Article: chebyshev1, Theorem C.1 via `chebyshev1.TwoTerm.local_unique`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem gamma_succ (t : ℕ) :
    gamma I (t + 1) = (1 + beta I (t + 1)) * (2 / (I.L + I.mu)) := by
  rw [← beta_coefficient]
  dsimp [gamma, SpectralInterval.eta]
  field_simp [I.den_ne (t + 2), ne_of_gt I.delta_pos, ne_of_gt I.sum_pos]
  ring

/--
Exact identity `(realization I).scalarContract M = M 0 0`.

Use: `chebyshev1.Prefix.residual_recurrence` rewrites with this identity to establish exact
identity `I.residual (n + 2) = Polynomial.C (1 + beta I (n + 1)) * (1 - Polynomial.C (2 / (I.L
+ I.mu)) * Polynomial.X) * I.residual (n + 1) - Polynomial.C (beta I (n + 1)) * I.residual n`.

Article: chebyshev1, Theorem 3.1 via `chebyshev1.TwoTerm.kernel_eq_prefix`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
@[simp] theorem scalarContract (M : Matrix (Fin 2) (Fin 2) ℝ) :
    (realization I).scalarContract M = M 0 0 := by simp [Realization.scalarContract, realization, Fin.sum_univ_two]

/--
Exact identity `(realization I).queryFactor s = !![gamma I s, 0; 0, 0]`.

Use: `chebyshev1.TwoTerm.kernel_eq_prefix` rewrites with this identity to establish exact
identity `S.realization.kernel N s lam nu = (Prefix.realization I).kernel N s lam nu`.

Article: chebyshev1, Theorem 3.1 via `chebyshev1.TwoTerm.kernel_eq_prefix`.

Proof: Check each member of the finite index type; no case is omitted.
-/
@[simp] theorem queryFactor (s : ℕ) :
    (realization I).queryFactor s = !![gamma I s, 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Realization.queryFactor, realization, Matrix.vecMulVec]

/--
Exact identity `(realization I).scalarStep 0 lam = !![I.z lam / I.eta, 0; 1, 0]`.

Use: `chebyshev1.Prefix.prefix_column` rewrites with this identity to establish the precise
assertion is `let M`.

Article: chebyshev1, Theorem 2.2 via `chebyshev1.Prefix.kernel_succ`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity. Check each member of the finite index type; no case is omitted.
-/
theorem scalarStep_zero (lam : ℝ) :
    (realization I).scalarStep 0 lam = !![I.z lam / I.eta, 0; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Realization.scalarStep, realization, gamma, Realization.queryFactor,
      Matrix.vecMulVec]
  dsimp [SpectralInterval.z, SpectralInterval.eta]
  field_simp [ne_of_gt I.delta_pos, ne_of_gt I.sum_pos]

/--
Exact identity `(realization I).scalarStep (t + 1) lam = !![2 * I.z lam * I.den (t + 1) / I.den
(t + 2), -(I.den t / I.den (t + 2)); 1, 0]`.

Use: `chebyshev1.Prefix.algorithmStep_succ` rewrites with this identity to establish exact
identity `(realization I).scalarStep (t + 1) lam = !![(1 + beta I (t + 1)) * (1 - (2 / (I.L +
I.mu)) * lam), -beta I (t + 1); 1, 0]`.

Article: chebyshev1, Theorem 2.2 via `chebyshev1.Prefix.kernel_succ`.

Proof: Check each member of the finite index type; no case is omitted.
-/
theorem scalarStep_succ (t : ℕ) (lam : ℝ) :
    (realization I).scalarStep (t + 1) lam =
      !![2 * I.z lam * I.den (t + 1) / I.den (t + 2),
          -(I.den t / I.den (t + 2)); 1, 0] := by
  -- Check each member of the finite index type; no case is omitted.
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Realization.scalarStep, realization, gamma, Realization.queryFactor,
      Matrix.vecMulVec]
  rw [I.z_eq]
  ring

/--
The normalized matrix is precisely the advertised two-term gradient update.

Exact identity `(realization I).scalarStep (t + 1) lam = !![(1 + beta I (t + 1)) * (1 - (2 /
(I.L + I.mu)) * lam), -beta I (t + 1); 1, 0]`.

Use: `chebyshev1.Prefix.residual_recurrence` rewrites with this identity to establish exact
identity `I.residual (n + 2) = Polynomial.C (1 + beta I (n + 1)) * (1 - Polynomial.C (2 / (I.L
+ I.mu)) * Polynomial.X) * I.residual (n + 1) - Polynomial.C (beta I (n + 1)) * I.residual n`.

Article: chebyshev1, Theorem 2.1 via `chebyshev1.Prefix.quadraticError_exact`.

Proof: Check each member of the finite index type; no case is omitted.
-/
theorem algorithmStep_succ (t : ℕ) (lam : ℝ) :
    (realization I).scalarStep (t + 1) lam =
      !![(1 + beta I (t + 1)) * (1 - (2 / (I.L + I.mu)) * lam),
        -beta I (t + 1); 1, 0] := by
  -- Check each member of the finite index type; no case is omitted.
  rw [scalarStep_succ]
  have hc : 2 * I.z lam * I.den (t + 1) / I.den (t + 2) =
      2 * I.eta * I.den (t + 1) / I.den (t + 2) - gamma I (t + 1) * lam := by
    rw [I.z_eq]
    dsimp [gamma]
    ring
  rw [hc, beta_coefficient, gamma_succ]
  simp only [beta, Nat.add_sub_cancel]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  ring

end
end chebyshev1.Prefix
