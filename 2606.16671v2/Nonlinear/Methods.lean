import «2606.16671v2».Jacobi.PrefixFiniteBounds
import «2606.16671v2».SineJacobi.FiniteBounds
import «2606.16671v2».Chebyshev.Amplification
import «2606.16671v2».TwoTerm.VariableHessian

/-!
Article: 2606.16671v2, Corollary 5.4.
The total finite drift bound used for nonlinear objectives.
Use: `«2606.16671v2».Nonlinear.MethodFamily.transfer_le` feeds
`«2606.16671v2».Nonlinear.lipschitzHessian_error_le` (Corollary 5.4 in coordinates centered at the
stationary point).
Proof chain: `«2606.16671v2».Nonlinear.lipschitzHessian_error_le` — 2606.16671v2, Corollary 5.4;
Lipschitz-Hessian error bound for both methods.
-/
namespace «2606.16671v2».Nonlinear
noncomputable section
open Polynomial Polynomial.Chebyshev
variable {d : Type*} [Fintype d] [DecidableEq d]

/--
Defines the alternatives used to distinguish the cases in the subsequent construction.

Use: `«2606.16671v2».Nonlinear.MethodFamily.data` uses this definition in the displayed
construction of `MethodFamily.data`. Its inputs and component formulas are fixed by that
definition.

Article: 2606.16671v2, Corollary 5.4 via `«2606.16671v2».Nonlinear.lipschitzHessian_error_le`.
-/
inductive MethodFamily
  /-- The prefix-exact Chebyshev/Jacobi realization used in the common nonlinear error bound. -/
  | prefix
  /-- The finite sine-Jacobi realization used in the same nonlinear error bound. -/
  | sine

/--
Defines `MethodFamily.data` of type `JacobiData` by `match family with | .prefix =>
Prefix.jacobiData | .sine => SineJacobi.data N`.

Use: `«2606.16671v2».Nonlinear.MethodFamily.finiteDrift_le` uses this definition to establish
the stated quantitative bound `opNorm (((family.data N).realization I).operatorTransfer N (fun
s => H+E s) - aeval H (I.residual N)) ≤ I.epsilon N * ((T ℝ N).eval (1+2*delta/I.delta)-1)`.

Article: 2606.16671v2, Corollary 5.4 via `«2606.16671v2».Nonlinear.lipschitzHessian_error_le`.
-/
def MethodFamily.data (family : MethodFamily) (N : ℕ) : JacobiData :=
  match family with
  | .prefix => Prefix.jacobiData
  | .sine => SineJacobi.data N

/--
The stated quantitative bound `opNorm (((family.data N).realization I).operatorTransfer N (fun
s => H+E s) - aeval H (I.residual N)) ≤ I.epsilon N * ((T ℝ N).eval (1+2*delta/I.delta)-1)`.

Use: `«2606.16671v2».Nonlinear.MethodFamily.transfer_le` uses this identity to establish the
stated quantitative bound `opNorm (((family.data N).realization I).operatorTransfer N Hs) ≤
I.epsilon N * (T ℝ N).eval (1+2*delta/I.delta)`.

Article: 2606.16671v2, Corollary 5.4 via `«2606.16671v2».Nonlinear.lipschitzHessian_error_le`.

Proof: Use the identities/estimates `«2606.16671v2».Prefix.jacobi_realization`,
`«2606.16671v2».Prefix.opNorm_finiteDrift_le`,
`«2606.16671v2».SineJacobi.opNorm_finiteDrift_le` with the arguments shown in the proof.
-/
theorem MethodFamily.finiteDrift_le (family : MethodFamily) (I : SpectralInterval)
    {N : ℕ} (hN : 0 < N) (H : Matrix d d ℝ) (hH : H.IsHermitian)
    (hspec : spectrum ℝ H ⊆ Set.Icc I.mu I.L)
    (E : ℕ → Matrix d d ℝ) (delta : ℝ) (hd : 0 ≤ delta)
    (hE : ∀ s < N, opNorm (E s) ≤ delta) :
    opNorm (((family.data N).realization I).operatorTransfer N (fun s => H+E s) -
      aeval H (I.residual N)) ≤
      I.epsilon N * ((T ℝ N).eval (1+2*delta/I.delta)-1) := by
  -- Use the identities/estimates `«2606.16671v2».Prefix.jacobi_realization`,
  -- `«2606.16671v2».Prefix.opNorm_finiteDrift_le`,
  -- `«2606.16671v2».SineJacobi.opNorm_finiteDrift_le` with the arguments shown in the proof.
  cases family with
  | «prefix» =>
    change opNorm ((Prefix.jacobiData.realization I).operatorTransfer N _ - _) ≤ _
    rw [Prefix.jacobi_realization]
    exact Prefix.opNorm_finiteDrift_le I hN H hH hspec E delta hd hE
  | sine => exact SineJacobi.opNorm_finiteDrift_le I hN H hH hspec E delta hd hE

/--
The total finite drift bound used for nonlinear objectives.

The stated quantitative bound `opNorm (((family.data N).realization I).operatorTransfer N Hs) ≤
I.epsilon N * (T ℝ N).eval (1+2*delta/I.delta)`.

Use: `«2606.16671v2».Nonlinear.MethodFamily.transfer_exp_le` uses this bound to establish the
stated quantitative bound `opNorm (((family.data N).realization I).operatorTransfer N Hs) ≤
2*Real.exp (-2*(N:ℝ)*(Real.sqrt I.mu-Real.sqrt delta)/Real.sqrt I.L)`.

Article: 2606.16671v2, Corollary 5.4 via `«2606.16671v2».Nonlinear.lipschitzHessian_error_le`.

Proof: Use the identities/estimates `«2606.16671v2».Nonlinear.MethodFamily.finiteDrift_le`,
`«2606.16671v2».opNorm_add_le`, `«2606.16671v2».opNorm_residual_le` with the arguments shown in
the proof.
-/
theorem MethodFamily.transfer_le (family : MethodFamily) (I : SpectralInterval)
    {N : ℕ} (hN : 0 < N) (H : Matrix d d ℝ) (hH : H.IsHermitian)
    (hspec : spectrum ℝ H ⊆ Set.Icc I.mu I.L)
    (Hs : ℕ → Matrix d d ℝ) (delta : ℝ) (hd : 0 ≤ delta)
    (hE : ∀ s < N, opNorm (Hs s-H) ≤ delta) :
    opNorm (((family.data N).realization I).operatorTransfer N Hs) ≤
      I.epsilon N * (T ℝ N).eval (1+2*delta/I.delta) := by
  -- Use the identities/estimates `«2606.16671v2».Nonlinear.MethodFamily.finiteDrift_le`,
  -- `«2606.16671v2».opNorm_add_le`, `«2606.16671v2».opNorm_residual_le` with the arguments
  -- shown in the proof.
  have hb := family.finiteDrift_le I hN H hH hspec (fun s => Hs s-H) delta hd hE
  simp only [add_sub_cancel] at hb
  have ht := opNorm_add_le
    (((family.data N).realization I).operatorTransfer N Hs - aeval H (I.residual N))
    (aeval H (I.residual N))
  rw [sub_add_cancel] at ht
  have hc := opNorm_residual_le I N H hH hspec
  nlinarith

/--
The stated quantitative bound `opNorm (((family.data N).realization I).operatorTransfer N Hs) ≤
2*Real.exp (-2*(N:ℝ)*(Real.sqrt I.mu-Real.sqrt delta)/Real.sqrt I.L)`.

Use: a standalone supporting bound for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2606.16671v2, Corollary 5.4.

Proof: Use the identities/estimates `«2606.16671v2».Nonlinear.MethodFamily.transfer_le`,
`«2606.16671v2».SpectralInterval.amplification_exp_le` with the arguments shown in the proof.
-/
theorem MethodFamily.transfer_exp_le (family : MethodFamily) (I : SpectralInterval)
    {N : ℕ} (hN : 0 < N) (H : Matrix d d ℝ) (hH : H.IsHermitian)
    (hspec : spectrum ℝ H ⊆ Set.Icc I.mu I.L)
    (Hs : ℕ → Matrix d d ℝ) (delta : ℝ) (hd : 0 ≤ delta) (hdmu : delta ≤ I.mu)
    (hE : ∀ s < N, opNorm (Hs s-H) ≤ delta) :
    opNorm (((family.data N).realization I).operatorTransfer N Hs) ≤
      2*Real.exp (-2*(N:ℝ)*(Real.sqrt I.mu-Real.sqrt delta)/Real.sqrt I.L) :=
  (family.transfer_le I hN H hH hspec Hs delta hd hE).trans
    (I.amplification_exp_le N delta hd hdmu)

end
end «2606.16671v2».Nonlinear
