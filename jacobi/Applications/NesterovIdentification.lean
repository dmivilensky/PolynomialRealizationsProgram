import jacobi.Applications.NesterovQueries
import jacobi.Jacobi.SymmetricCoordinate

/-!
Article: jacobi, Proposition A.1.
The actual general-momentum error recurrence is the original normalized
Gegenbauer residual in the square coordinate. This connects the already
proved hard-edge polynomial family to the genuine original iterates.
Use: NesterovResidualIdentification transfers the full hard-edge and
numbered-zero results to the actual Nesterov realization.
-/
namespace jacobi.Applications
noncomputable section
open Polynomial jacobi.Jacobi
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- The genuine original Nesterov error is precisely its original normalized symmetric Jacobi/Gegenbauer expression in the square coordinate for every admissible momentum parameter.
Use: NesterovResidualIdentification obtains equality of the actual original realization residual with the polynomial family used by the full hard-edge theorem.
Article: jacobi, Proposition A.1.
Proof: initialize the actual first two Landweber steps. The actual momentum coefficients match the independently proved degree recurrence of the original normalized symmetric Jacobi polynomials. Integer powers preserve the identity at the zero square-coordinate endpoint without division by that coordinate. -/
theorem nesterovError_square {b:ℝ} (hb:-1<b) (z:ℝ) (n:ℕ) :
    nesterovError b (1-z^2) (n+1)=z^(n+2)*symmetricUnit (b/2) n z := by
  -- Induction uses the same actual error recurrence and its genuine source polynomial family at every degree.
  have ha:-(1/2:ℝ)<b/2:=by linarith
  induction n using Nat.twoStepInduction with
  | zero=>simp [nesterovError]
  | one=>simp [nesterovError,nesterovMomentum,symmetricUnit_one ha]; ring
  | more n ih0 ih1=>
    rw [show n+2+1=(n+1)+2 by omega,nesterovError,ih1,ih0]
    have hk:0<n+1+1:=by omega
    simp only [nesterovMomentum,ite_eq_right (Nat.ne_of_gt hk)]
    have hd:=nesterov_denominator_pos hb hk
    have hr:=symmetricUnit_recurrence (a:=b/2) (by linarith) n z
    push_cast at hd ⊢
    field_simp [hd.ne']
    linear_combination (norm := (simp only [pow_succ]; ring)) -(z^(n+4))*hr

end
end jacobi.Applications
