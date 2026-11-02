import krylov.Stability.UniformGram
import krylov.Reference.CanonicalSteps
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(c), finite genuine centred inverse risk.
Use: the real centring inverse correction has its actual leading robust
residual and explicit cubic loss, without assuming an asymptotic output.
Source: proved native Neumann inverse bounds, actual inverse cancellation
and exact decomposition of the true inverse correction about minus rho.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Reference krylov.Stability
open scoped Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The true inverse centring correction has its leading hidden/output
residual bound and explicit finite inverse loss, with the actual inverse
domain and inverse error derived from its genuine measured centre.
Use: the known-base centring method obtains a uniform cubic remainder
from real norm budgets even at discontinuous hidden-centre corners.
Article: main_krylov, thm:local(c), finite attained upper algorithm bound.
Proof: genuine Neumann bounds supply the actual inverse and bound the
true correction's difference from minus rho. Exact inverse cancellation
leaves only the real hidden and output operators. Split their action into
the leading value at minus rho and the genuine inverse correction error. -/
theorem centred_inverse_residual_bound (C : Matrix (Fin n) (Fin n) ℝ)
    (hC : ‖C-1‖≤(1/2 : ℝ))
    (Delta F : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (rho : EuclideanSpace ℝ (Fin n)) :
    let u := -(cgOperator C⁻¹ rho)
    ‖rho+(cgOperator C+Delta+F) u‖≤‖Delta rho‖+‖F‖*‖rho‖+
      (‖Delta‖+‖F‖)*(2*‖C-1‖*‖rho‖) := by
  let u := -(cgOperator C⁻¹ rho)
  have hinv := near_identity_inverse C hC
  have hcancel : rho+cgOperator C u=0 := by
    change rho+cgOperator C (-(cgOperator C⁻¹ rho))=0
    simp only [map_neg,cgOperator,← mul_apply_eq_comp,← map_mul,Matrix.mul_nonsing_inv _ hinv.1,map_one,one_apply_eq_self,add_neg_cancel]
  have hu : u+rho= -(cgOperator (C⁻¹-1) rho) := by
    simp only [u,cgOperator,map_sub,map_one,_root_.sub_apply,one_apply_eq_self,neg_sub]
    abel
  have huBound : ‖u+rho‖≤2*‖C-1‖*‖rho‖ := by
    rw [hu,norm_neg]
    have hn : ‖cgOperator (C⁻¹-1)‖=‖C⁻¹-1‖ := (Matrix.l2_opNorm_toEuclideanCLM _).symm
    exact ((cgOperator (C⁻¹-1)).le_opNorm rho).trans (by rw [hn];gcongr;exact hinv.2.2)
  have houtput : rho+(cgOperator C+Delta+F) u=Delta u+F u := by
    simp only [_root_.add_apply]
    have he : rho+(cgOperator C u+Delta u+F u)=(rho+cgOperator C u)+(Delta u+F u) := by abel
    rw [he,hcancel,zero_add]
  have hsplit : Delta u+F u= -(Delta rho+F rho)+(Delta (u+rho)+F (u+rho)) := by
    simp only [map_add]
    abel
  have hLeading : ‖Delta rho+F rho‖≤‖Delta rho‖+‖F‖*‖rho‖ :=
    (norm_add_le _ _).trans (add_le_add le_rfl (F.le_opNorm rho))
  have hRemainder : ‖Delta (u+rho)+F (u+rho)‖≤(‖Delta‖+‖F‖)*(2*‖C-1‖*‖rho‖) := by
    have he := (norm_add_le (Delta (u+rho)) (F (u+rho))).trans
      (add_le_add (Delta.le_opNorm (u+rho)) (F.le_opNorm (u+rho)))
    have hsum : ‖Delta‖*‖u+rho‖+‖F‖*‖u+rho‖=(‖Delta‖+‖F‖)*‖u+rho‖ := by ring
    rw [hsum] at he
    exact he.trans (mul_le_mul_of_nonneg_left huBound (by positivity))
  dsimp only
  rw [houtput,hsplit]
  exact (norm_add_le _ _).trans (by rw [norm_neg];exact add_le_add hLeading hRemainder)

end
end krylov.OneGradient
