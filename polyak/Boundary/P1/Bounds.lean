import polyak.Boundary.P1.Algebra

/-! Scalar inequalities for physical P1 source roots, independently of finite lag certificates. -/
noncomputable section
namespace polyak.Boundary.P1
open Spectral

/-- Scalar inequalities exported by the continuation boxes. No feasibility premise is stored. -/
structure PhysicalBounds (z : ℝ) (Z : Coordinates) : Prop where
  u_nonneg : 0≤branchU z (Z 0)
  u_le_one : branchU z (Z 0)≤1
  atom_lower : -z/2≤branchAtom z (Z 1)
  atom_nonpos : branchAtom z (Z 1)≤0
  gap_lower : z/2≤1-(branchAtom z (Z 1))^2-(branchU z (Z 0))^2
  residual_left : 0<residualConstant z (branchU z (Z 0)) (branchAtom z (Z 1))-
    residualLinear z (branchU z (Z 0)) (branchAtom z (Z 1))
  residual_right : 0<residualConstant z (branchU z (Z 0)) (branchAtom z (Z 1))+
    residualLinear z (branchU z (Z 0)) (branchAtom z (Z 1))

theorem PhysicalBounds.residual {z : ℝ} {Z : Coordinates} (h : PhysicalBounds z Z) :
    |residualLinear z (branchU z (Z 0)) (branchAtom z (Z 1))|<
      residualConstant z (branchU z (Z 0)) (branchAtom z (Z 1)) := by
  apply abs_lt.mpr
  constructor <;> linarith [h.residual_left,h.residual_right]

def physicalAtom {z : ℝ} {Z : Coordinates} (hz : 0<z) (hz1 : z≤3/4)
    (h : PhysicalBounds z Z) : Frequency :=
  ⟨branchAtom z (Z 1),⟨by linarith [h.atom_lower],by linarith [h.atom_nonpos]⟩⟩

end polyak.Boundary.P1
