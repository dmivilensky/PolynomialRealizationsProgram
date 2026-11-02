import jacobi.Applications.NesterovQueries
import jacobi.Applications.ChebyshevDouble
import jacobi.Applications.BlockKernel
import jacobi.Applications.TerminalRealization
import jacobi.Jacobi.ChebyshevSecond

/-!
Article: jacobi, Theorem 5.1.
Every original U-fibre block has the same terminal polynomial as the
actual original Nesterov recurrence at the exact horizon 2*m+2.
Use: Article combines the literal terminal-polynomial identity with the
sharp gain theorem, which compares two genuine terminal-equivalent methods.
-/
namespace jacobi.Applications
noncomputable section
open Polynomial Polynomial.Chebyshev Set jacobi.Finite chebyshev1 chebyshev2
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The actual original Nesterov scalar transfer equals the current-error coordinate of its genuine forward recurrence.
Use: block_terminal_nesterov compares the actual generic-realization transfers of both original methods.
Article: jacobi, Theorem 5.1.
Proof: the original forward memory is already proved to store the actual current and previous errors. Its original readout is exactly the current coordinate. -/
theorem nesterov_transfer (b l:ℝ) (k:ℕ) :
    (nesterovMethod b).scalarTransfer k l=nesterovError b l k := by
  have h:=congrFun (nesterov_forward_memory b l k) 0
  simpa [Realization.scalarTransfer,Realization.scalarContract,nesterovMethod,
    Matrix.mulVec,Fin.sum_univ_two,Matrix.vecHead,Matrix.vecTail] using h

/-- Every genuine U-fibre Jacobi stage has the original normalized U terminal transfer.
Use: block_terminal_nesterov retains the entire original fibre when identifying the terminal-equivalent block.
Article: jacobi, Theorem 5.1.
Proof: the actual arbitrary-fibre prefix theorem gives its normalized characteristic polynomial. The proved terminal identification and half-integer Jacobi formula give the literal U polynomial. -/
theorem u_fibre_transfer {m:ℕ} {J:Jacobi m}
    (hJ:InFiber J (jacobi.Jacobi.nodes (1/2) (1/2) (by norm_num) (by norm_num) m).polynomial) (l:ℝ) :
    (endpointMethod J).realization.scalarTransfer m l=(U ℝ (m:ℤ)).eval (1-2*l)/((m:ℝ)+1) := by
  rw [← Realization.residualPolynomial_eval,endpoint_prefix_exact _ hJ m le_rfl,
    endpoint_terminal_exact _ _ hJ,jacobi.Jacobi.shiftedPolynomial_half_sine]
  simp only [eval_mul,eval_C,eval_comp,eval_sub,eval_one,eval_X]
  ring

/-- The genuine original b=1 Nesterov iteration and every original U-fibre-plus-Landweber block have identical terminal transfers throughout the original spectral interval, with exactly the same application count.
Use: block_terminal_polynomial obtains equality of their actual residual polynomials, so the same statement holds on every fixed operator by the earlier article's polynomial semantics.
Article: jacobi, Theorem 5.1.
Proof: the real original Nesterov recurrence has its proved wave formula. The exact Chebyshev quadratic identity gives its original U factor and integer Landweber power. Every true U-fibre stage has exactly that factor, and the actual appended Landweber realization supplies the same remaining power. -/
theorem block_terminal_nesterov {m:ℕ} {J:Jacobi m}
    (hJ:InFiber J (jacobi.Jacobi.nodes (1/2) (1/2) (by norm_num) (by norm_num) m).polynomial)
    {l:ℝ} (hl:l≤1) :
    (blockMethod J).realization.scalarTransfer (2*m+2) l=
      (nesterovMethod 1).scalarTransfer (2*m+2) l := by
  -- Both sides are actual realization transfers, not separately defined desired residual formulas.
  rw [blockMethod,show 2*m+2=m+(m+2) by omega,append_transfer,u_fibre_transfer hJ]
  rw [show m+(m+2)=(2*m+1)+1 by omega,nesterov_transfer,nesterovError_wave,nesterovWave_odd m hl]
  push_cast
  field_simp
  ring

/-- The actual full residual polynomials of the original b=1 Nesterov method and every original U block are exactly equal.
Use: Article checks literal terminal equivalence, and the first article's aeval operator theorem transports this identity to arbitrary fixed finite-dimensional operators.
Article: jacobi, Theorem 5.1.
Proof: both genuine transfers are evaluations of the original realization residual polynomials. They agree at every lambda<=1, an infinite set, so the community polynomial identity theorem gives literal polynomial equality. -/
theorem block_terminal_polynomial {m:ℕ} {J:Jacobi m}
    (hJ:InFiber J (jacobi.Jacobi.nodes (1/2) (1/2) (by norm_num) (by norm_num) m).polynomial) :
    (blockMethod J).realization.residualPolynomial (2*m+2)=
      (nesterovMethod 1).residualPolynomial (2*m+2) := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.Iic_infinite (1:ℝ)).mono
  intro l hl
  change Polynomial.eval l ((blockMethod J).realization.residualPolynomial (2*m+2))=
    Polynomial.eval l ((nesterovMethod 1).residualPolynomial (2*m+2))
  rw [Realization.residualPolynomial_eval,Realization.residualPolynomial_eval]
  exact block_terminal_nesterov hJ hl

end
end jacobi.Applications
