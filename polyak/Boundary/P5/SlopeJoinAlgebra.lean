import polyak.Boundary.Envelope
import polyak.Boundary.P5.P2Lift
import polyak.Boundary.P5.EndpointJoin
import polyak.Boundary.P5.DerivativeSource

/-! The common endpoint envelope for the P2/P5 join. The vanishing lag-five
weight leaves the same three normalized active equations on both branches. -/
noncomputable section
namespace polyak.Boundary.P5.SlopeJoin
open Spectral Filter Envelope Polynomial
open scoped Topology

def symbol (w : ℝ) (v : Point) : ℝ :=
  -(v 1-v 2)*((1-v 2^2-v 0^2)*cubicAlpha (v 1) w (v 2)-
    2*v 0*(1-v 2^2)*quadraticBeta (v 1) w (v 2))

theorem symbol_differentiable (w : ℝ) (v : Point) : DifferentiableAt ℝ (symbol w) v := by
  unfold symbol cubicAlpha quadraticBeta
  fun_prop

/-- The common dual is nondegenerate in the value direction at every interior atom. -/
theorem alpha_pos {G w c : ℝ} (hG : 1<G) (hw : 0<w ∧ w<1)
    (hc : -1<c ∧ c<1) : 0<cubicAlpha G w c := by
  have h0 : 0<8*G^3+4*G^2*c+4*G*c^2-4*G := by
    have hq : 0<2*G^2-1+G*c+c^2 := by
      nlinarith [sq_nonneg (c+G/2),sq_nonneg (G-1)]
    nlinarith [mul_pos (by linarith : (0 : ℝ)<4*G) hq]
  have h1 : 0<8*G^3-2*G+(4*G^2-1)*c := by
    have hp : 0<(2*G-1)*(4*G^2-1) := mul_pos (by linarith) (by nlinarith)
    have hm := mul_pos (by nlinarith : (0 : ℝ)<4*G^2-1) (by linarith : 0<c+1)
    nlinarith
  have hm0:=mul_pos (by linarith : 0<1-w) h0
  have hm1:=mul_pos hw.1 h1
  unfold cubicAlpha
  nlinarith

theorem beta_pos {G w c : ℝ} (hG : 1<G) (hw : 0<w ∧ w<1)
    (hc : -1<c ∧ c<1) : 0<quadraticBeta G w c := by
  have hp := mul_pos (by linarith : (0 : ℝ)<4*G) (by linarith : 0<G-1)
  have hwg := mul_pos hw.1 (by linarith : 0<4*G-1)
  have hm := mul_pos (mul_pos (by linarith : 0<4*G) (by linarith : 0<1-w))
    (by linarith : 0<c+1)
  unfold quadraticBeta
  nlinarith

theorem symbol_u_hasDerivAt (u G w c : ℝ) :
    HasDerivAt (fun r => symbol w (point r G c))
      (2*(G-c)*(u*cubicAlpha G w c+(1-c^2)*quadraticBeta G w c)) u := by
  have hd:=((((hasDerivAt_const u (1-c^2)).sub ((hasDerivAt_id u).pow 2)).mul_const
    (cubicAlpha G w c)).sub
      ((((hasDerivAt_id u).const_mul 2).mul_const (1-c^2)).mul_const (quadraticBeta G w c))).const_mul (-(G-c))
  convert hd using 1
  · funext r
    rfl
  · dsimp only [id_eq]
    ring

theorem symbol_u_partial (u G w c : ℝ) :
    fderiv ℝ (symbol w) (point u G c) (basis 0)=
      2*(G-c)*(u*cubicAlpha G w c+(1-c^2)*quadraticBeta G w c) := by
  have hd:=(symbol_differentiable w (point u G c)).hasFDerivAt.comp_hasDerivAt u
    (point_hasDerivAt (hasDerivAt_id u) (hasDerivAt_const u G) (hasDerivAt_const u c))
  have he : point (1 : ℝ) 0 0=basis 0 := by ext i; fin_cases i <;> simp [point,basis]
  rw [he] at hd
  exact hd.unique (symbol_u_hasDerivAt u G w c)

theorem symbol_u_partial_pos {u G w c : ℝ} (hu : 0<u) (hG : 1<G)
    (hw : 0<w ∧ w<1) (hc : -1<c ∧ c<1) :
    0<fderiv ℝ (symbol w) (point u G c) (basis 0) := by
  rw [symbol_u_partial]
  apply mul_pos (mul_pos (by norm_num) (by linarith))
  have hc2 : 0<1-c^2 := by nlinarith [mul_pos (by linarith : 0<c+1) (by linarith : 0<1-c)]
  exact add_pos (mul_pos hu (alpha_pos hG hw hc)) (mul_pos hc2 (beta_pos hG hw hc))

/-- The endpoint source is exactly a factored double contact, before differentiating it. -/
theorem symbol_p2_factor {z : ℝ} (hz : z∈P2.parameterInterval) (c : ℝ) :
    symbol (P2.W z) (point (P2.u z) (P2.G z) c)=
      (P2.G z-c)*(4*P2.G z*(1-P2.W z))*((c-P2.x z)*(c-P2.y z))^2 := by
  change -(P2.G z-c)*((1-c^2-P2.u z^2)*cubicAlpha (P2.G z) (P2.W z) c-
    2*P2.u z*(1-c^2)*quadraticBeta (P2.G z) (P2.W z) c)=_
  have hh:=P2.double_square_identity hz c
  rw [P2.atomPolynomial_factor hz] at hh
  linear_combination (P2.G z-c)*hh

theorem symbol_p2_contact {z : ℝ} (hz : z∈P2.parameterInterval) {c : ℝ}
    (hc : c=P2.x z ∨ c=P2.y z) :
    symbol (P2.W z) (point (P2.u z) (P2.G z) c)=0 ∧
    fderiv ℝ (symbol (P2.W z)) (point (P2.u z) (P2.G z) c) (basis 2)=0 := by
  constructor
  · rw [symbol_p2_factor hz]
    rcases hc with rfl|rfl <;> simp
  · let Q : ℝ[X] := (C (P2.G z)-Polynomial.X)*C (4*P2.G z*(1-P2.W z))*
      ((Polynomial.X-C (P2.x z))*(Polynomial.X-C (P2.y z)))^2
    have he : (fun r => symbol (P2.W z) (point (P2.u z) (P2.G z) r))=fun r => Q.eval r := by
      funext r
      rw [symbol_p2_factor hz]
      simp [Q]
    have hd:=(symbol_differentiable (P2.W z) (point (P2.u z) (P2.G z) c)).hasFDerivAt.comp_hasDerivAt c
      (point_hasDerivAt (hasDerivAt_const c (P2.u z)) (hasDerivAt_const c (P2.G z)) (hasDerivAt_id c))
    have hb : point (0 : ℝ) 0 1=basis 2 := by ext i; fin_cases i <;> simp [point,basis]
    rw [hb] at hd
    have hq : Q.derivative.eval c=0 := by
      rcases hc with rfl|rfl <;>
        simp [Q,derivative_mul,derivative_pow,derivative_sub,derivative_C,derivative_X]
    change HasDerivAt (fun r => symbol (P2.W z) (point (P2.u z) (P2.G z) r))
      (fderiv ℝ (symbol (P2.W z)) (point (P2.u z) (P2.G z) c) (basis 2)) c at hd
    rw [he] at hd
    exact (hd.unique (Q.hasDerivAt c)).trans hq

end polyak.Boundary.P5.SlopeJoin
