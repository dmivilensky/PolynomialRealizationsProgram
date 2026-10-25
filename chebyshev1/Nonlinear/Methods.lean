import chebyshev1.Jacobi.PrefixFiniteBounds
import chebyshev1.SineJacobi.FiniteBounds
import chebyshev1.Chebyshev.Amplification
import chebyshev1.TwoTerm.VariableHessian

/-!
Article: chebyshev1, Corollary 5.4.
The total finite drift bound used for nonlinear objectives.
Use: `chebyshev1.Nonlinear.MethodFamily.transfer_le` feeds
`chebyshev1.Nonlinear.lipschitzHessian_error_le` (Corollary 5.4 in coordinates centered at the
stationary point).
Proof chain: `chebyshev1.Nonlinear.lipschitzHessian_error_le` — chebyshev1, Corollary 5.4;
Lipschitz-Hessian error bound for both methods.
-/
namespace chebyshev1.Nonlinear
noncomputable section
open Polynomial Polynomial.Chebyshev
variable {d : Type*} [Fintype d] [DecidableEq d]

/--
Defines the alternatives used to distinguish the cases in the subsequent construction.

Use: `chebyshev1.Nonlinear.MethodFamily.data` uses this definition in the displayed
construction of `MethodFamily.data`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev1, Corollary 5.4 via `chebyshev1.Nonlinear.lipschitzHessian_error_le`.
-/
inductive MethodFamily
  /-- The prefix-exact Chebyshev/Jacobi realization used in the common nonlinear error bound. -/
  | prefix
  /-- The finite sine-Jacobi realization used in the same nonlinear error bound. -/
  | sine

/--
Defines `MethodFamily.data` of type `JacobiData` by `match family with | .prefix =>
Prefix.jacobiData | .sine => SineJacobi.data N`.

Use: `chebyshev1.Nonlinear.MethodFamily.finiteDrift_le` uses this definition to establish
the stated quantitative bound `opNorm (((family.data N).realization I).operatorTransfer N (fun
s => H+E s) - aeval H (I.residual N)) ≤ I.epsilon N * ((T ℝ N).eval (1+2*delta/I.delta)-1)`.

Article: chebyshev1, Corollary 5.4 via `chebyshev1.Nonlinear.lipschitzHessian_error_le`.
-/
def MethodFamily.data (family : MethodFamily) (N : ℕ) : JacobiData :=
  match family with
  | .prefix => Prefix.jacobiData
  | .sine => SineJacobi.data N

/--
The stated quantitative bound `opNorm (((family.data N).realization I).operatorTransfer N (fun
s => H+E s) - aeval H (I.residual N)) ≤ I.epsilon N * ((T ℝ N).eval (1+2*delta/I.delta)-1)`.

Use: `chebyshev1.Nonlinear.MethodFamily.transfer_le` uses this identity to establish the
stated quantitative bound `opNorm (((family.data N).realization I).operatorTransfer N Hs) ≤
I.epsilon N * (T ℝ N).eval (1+2*delta/I.delta)`.

Article: chebyshev1, Corollary 5.4 via `chebyshev1.Nonlinear.lipschitzHessian_error_le`.

Proof: Use the identities/estimates `chebyshev1.Prefix.jacobi_realization`,
`chebyshev1.Prefix.opNorm_finiteDrift_le`,
`chebyshev1.SineJacobi.opNorm_finiteDrift_le` with the arguments shown in the proof.
-/
theorem MethodFamily.finiteDrift_le (family : MethodFamily) (I : SpectralInterval)
    {N : ℕ} (hN : 0 < N) (H : Matrix d d ℝ) (hH : H.IsHermitian)
    (hspec : spectrum ℝ H ⊆ Set.Icc I.mu I.L)
    (E : ℕ → Matrix d d ℝ) (delta : ℝ) (hd : 0 ≤ delta)
    (hE : ∀ s < N, opNorm (E s) ≤ delta) :
    opNorm (((family.data N).realization I).operatorTransfer N (fun s => H+E s) -
      aeval H (I.residual N)) ≤
      I.epsilon N * ((T ℝ N).eval (1+2*delta/I.delta)-1) := by
  -- Use the identities/estimates `chebyshev1.Prefix.jacobi_realization`,
  -- `chebyshev1.Prefix.opNorm_finiteDrift_le`,
  -- `chebyshev1.SineJacobi.opNorm_finiteDrift_le` with the arguments shown in the proof.
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

Use: `chebyshev1.Nonlinear.MethodFamily.transfer_exp_le` uses this bound to establish the
stated quantitative bound `opNorm (((family.data N).realization I).operatorTransfer N Hs) ≤
2*Real.exp (-2*(N:ℝ)*(Real.sqrt I.mu-Real.sqrt delta)/Real.sqrt I.L)`.

Article: chebyshev1, Corollary 5.4 via `chebyshev1.Nonlinear.lipschitzHessian_error_le`.

Proof: Use the identities/estimates `chebyshev1.Nonlinear.MethodFamily.finiteDrift_le`,
`chebyshev1.opNorm_add_le`, `chebyshev1.opNorm_residual_le` with the arguments shown in
the proof.
-/
theorem MethodFamily.transfer_le (family : MethodFamily) (I : SpectralInterval)
    {N : ℕ} (hN : 0 < N) (H : Matrix d d ℝ) (hH : H.IsHermitian)
    (hspec : spectrum ℝ H ⊆ Set.Icc I.mu I.L)
    (Hs : ℕ → Matrix d d ℝ) (delta : ℝ) (hd : 0 ≤ delta)
    (hE : ∀ s < N, opNorm (Hs s-H) ≤ delta) :
    opNorm (((family.data N).realization I).operatorTransfer N Hs) ≤
      I.epsilon N * (T ℝ N).eval (1+2*delta/I.delta) := by
  -- Use the identities/estimates `chebyshev1.Nonlinear.MethodFamily.finiteDrift_le`,
  -- `chebyshev1.opNorm_add_le`, `chebyshev1.opNorm_residual_le` with the arguments
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

Article: chebyshev1, Corollary 5.4.

Proof: Use the identities/estimates `chebyshev1.Nonlinear.MethodFamily.transfer_le`,
`chebyshev1.SpectralInterval.amplification_exp_le` with the arguments shown in the proof.
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
end chebyshev1.Nonlinear
