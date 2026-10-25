import polyak.Boundary.P1.Endpoint
import polyak.Boundary.P1.CoreBounds

/-! The exact radical endpoint is an admissible contact, independent of numerical boxes. -/
noncomputable section
namespace polyak.Boundary.P1

theorem endpoint_residual_left :
    residualConstant zW (1-zW/2) (-zW/2)-residualLinear zW (1-zW/2) (-zW/2)=zW := by
  have hi : residualConstant zW (1-zW/2) (-zW/2)-residualLinear zW (1-zW/2) (-zW/2)=
      zW+(zW-1)*(zW^2+2*zW-2) := by unfold residualConstant residualLinear; ring
  rw [hi,zW_equation]
  ring

theorem endpoint_residual_right :
    residualConstant zW (1-zW/2) (-zW/2)+residualLinear zW (1-zW/2) (-zW/2)=11*zW-8 := by
  have hi : residualConstant zW (1-zW/2) (-zW/2)+residualLinear zW (1-zW/2) (-zW/2)=
      11*zW-8+(zW-5)*(zW^2+2*zW-2) := by unfold residualConstant residualLinear; ring
  rw [hi,zW_equation]
  ring

theorem endpoint_admissible : ContactAdmissible (zW,endpoint) := by
  change 0<branchU zW (endpoint 0) ∧ |branchAtom zW (endpoint 1)|<1 ∧ _
  rw [endpoint_u,endpoint_atom]
  refine ⟨by linarith [zW_bounds.2],?_,?_⟩
  · apply abs_lt.mpr
    constructor <;> linarith [zW_bounds.1,zW_bounds.2]
  · apply abs_lt.mpr
    constructor
    · have hh := endpoint_residual_right
      linarith [zW_bounds.1]
    · have hh := endpoint_residual_left
      linarith [zW_pos]

end polyak.Boundary.P1
