import polyak.Boundary.P1.Algebra
import polyak.Boundary.SpiralEndpoint

/-! Article: exact P1/spiral junction at zW=GW⁻¹, including the source root. -/
noncomputable section
namespace polyak.Boundary.P1

/-- The reciprocal outer spiral endpoint, in the regular P1 parameter. -/
def zW : ℝ := 1/GW

theorem zW_pos : 0<zW := one_div_pos.mpr (by linarith [GW_bounds.1])

theorem zW_bounds : 731/1000<zW ∧ zW<733/1000 := by
  have hg : 0<GW := by linarith [GW_bounds.1]
  unfold zW
  constructor
  · rw [lt_div_iff₀ hg]
    nlinarith [GW_bounds.2]
  · rw [div_lt_iff₀ hg]
    nlinarith [GW_bounds.1]

theorem zW_equation : zW^2+2*zW-2=0 := by
  have hg : GW≠0 := ne_of_gt (by linarith [GW_bounds.1])
  have hi : zW*GW=1 := by unfold zW; field_simp
  have hi2 : zW^2*GW^2=1 := by rw [← mul_pow,hi]; norm_num
  have hh : (zW^2+2*zW-2)*GW^2= -(2*GW^2-2*GW-1) := by
    have hiG := congrArg (fun x : ℝ => x*GW) hi
    nlinarith
  rw [GW_equation,neg_zero] at hh
  exact (mul_eq_zero.mp hh).resolve_right (pow_ne_zero _ hg)

/-- The exact endpoint in the divided source coordinates. -/
def endpoint : Coordinates := ![0,-1/(2*zW)]

theorem endpoint_u : branchU zW (endpoint 0)=1-zW/2 := by simp [branchU,endpoint]
theorem endpoint_atom : branchAtom zW (endpoint 1)= -zW/2 := by
  norm_num [branchAtom,endpoint]
  field_simp [zW_pos.ne']

theorem endpoint_contacts : quartic zW (1-zW/2) (-zW/2)=0 ∧
    quarticDerivative zW (1-zW/2) (-zW/2)=0 := by
  constructor
  · unfold quartic
    ring
  · have hf : quarticDerivative zW (1-zW/2) (-zW/2)=
        -zW*(zW-2)*(zW^2+2*zW-2)/2 := by unfold quarticDerivative; ring
    rw [hf,zW_equation]
    ring

/-- Exact substitution into both regularized P1 equations. -/
theorem endpoint_regularSystem : regularSystem (zW,endpoint)=0 := by
  have h0 := quartic_division zW (endpoint 0) (endpoint 1)
  have h1 := derivative_division zW (endpoint 0) (endpoint 1)
  rw [endpoint_u,endpoint_atom,endpoint_contacts.1] at h0
  rw [endpoint_u,endpoint_atom,endpoint_contacts.2] at h1
  have hz2 : zW^2≠0 := pow_ne_zero _ zW_pos.ne'
  have he0 := (mul_eq_zero.mp h0).resolve_left hz2
  have he1 := (mul_eq_zero.mp h1).resolve_left hz2
  ext i
  fin_cases i <;> simp [regularSystem,he0,he1]

/-- The endpoint twist and atom agree exactly with the spiral formulas. -/
theorem endpoint_spiral_formulas :
    branchU zW (endpoint 0)=1-1/(2*GW) ∧
      branchAtom zW (endpoint 1)= -1/(2*GW) := by
  rw [endpoint_u,endpoint_atom]
  unfold zW
  constructor <;> ring

end polyak.Boundary.P1
