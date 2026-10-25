import polyak.Boundary.P1.Bounds

/-! Scalar continuation reserves without the endpoint-tight atom inequality. -/
noncomputable section
namespace polyak.Boundary.P1
open Spectral

structure CoreBounds (z : ℝ) (Z : Coordinates) : Prop where
  u_nonneg : 0≤branchU z (Z 0)
  u_le_one : branchU z (Z 0)≤1
  atom_nonpos : branchAtom z (Z 1)≤0
  gap_lower : z/2≤1-(branchAtom z (Z 1))^2-(branchU z (Z 0))^2
  residual_left : 0<residualConstant z (branchU z (Z 0)) (branchAtom z (Z 1))-
    residualLinear z (branchU z (Z 0)) (branchAtom z (Z 1))
  residual_right : 0<residualConstant z (branchU z (Z 0)) (branchAtom z (Z 1))+
    residualLinear z (branchU z (Z 0)) (branchAtom z (Z 1))

theorem CoreBounds.residual {z : ℝ} {Z : Coordinates} (h : CoreBounds z Z) :
    |residualLinear z (branchU z (Z 0)) (branchAtom z (Z 1))|<
      residualConstant z (branchU z (Z 0)) (branchAtom z (Z 1)) :=
  abs_lt.mpr ⟨by linarith [h.residual_right],by linarith [h.residual_left]⟩

theorem CoreBounds.atom_abs_lt {z : ℝ} {Z : Coordinates} (hz : 0<z) (h : CoreBounds z Z) :
    |branchAtom z (Z 1)|<1 := by
  have hq : (branchAtom z (Z 1))^2<1 := by nlinarith [h.gap_lower,sq_nonneg (branchU z (Z 0))]
  exact abs_lt.mpr ⟨by nlinarith [sq_nonneg (branchAtom z (Z 1)+1)],
    by nlinarith [sq_nonneg (branchAtom z (Z 1)-1)]⟩

def coreAtom {z : ℝ} {Z : Coordinates} (hz : 0<z) (h : CoreBounds z Z) : Frequency :=
  ⟨branchAtom z (Z 1),(abs_le.mp (h.atom_abs_lt hz).le)⟩

theorem contactD_pos {z : ℝ} (hz : 0≤z) (hz1 : z≤3/4) (c : Frequency) : 0<contactD z c := by
  have hm : 0≤z*((c : ℝ)+1) := mul_nonneg hz (by linarith [c.property.1])
  unfold contactD
  nlinarith [sq_nonneg (z*(c : ℝ))]

theorem CoreBounds.u_pos {z : ℝ} {Z : Coordinates} (hz : 0<z) (hz1 : z≤3/4)
    (hZ : regularSystem (z,Z)=0) (h : CoreBounds z Z) : 0<branchU z (Z 0) := by
  apply lt_of_le_of_ne h.u_nonneg
  intro he
  have hact := contact_gap_identity (regularSystem_contacts hZ).1
  have hD := contactD_pos hz.le hz1 (coreAtom hz h)
  change 0<contactD z (branchAtom z (Z 1)) at hD
  rw [← he] at hact
  norm_num at hact
  have hg : 0<1-(branchAtom z (Z 1))^2 := by nlinarith [h.gap_lower,he]
  exact hact.elim hg.ne' hD.ne'

/-- Open qualitative conditions sufficient for algebraic contact uniqueness. -/
def ContactAdmissible (p : ℝ×Coordinates) : Prop :=
  0<branchU p.1 (p.2 0) ∧ |branchAtom p.1 (p.2 1)|<1 ∧
    |residualLinear p.1 (branchU p.1 (p.2 0)) (branchAtom p.1 (p.2 1))|<
      residualConstant p.1 (branchU p.1 (p.2 0)) (branchAtom p.1 (p.2 1))

theorem CoreBounds.admissible {z : ℝ} {Z : Coordinates} (hz : 0<z) (hz1 : z≤3/4)
    (hZ : regularSystem (z,Z)=0) (h : CoreBounds z Z) : ContactAdmissible (z,Z) :=
  ⟨h.u_pos hz hz1 hZ,h.atom_abs_lt hz,h.residual⟩

theorem contactAdmissible_open : IsOpen {p : ℝ×Coordinates | ContactAdmissible p} := by
  have hu : Continuous (fun p : ℝ×Coordinates => branchU p.1 (p.2 0)) := by
    unfold branchU
    fun_prop
  have ha : Continuous (fun p : ℝ×Coordinates => |branchAtom p.1 (p.2 1)|) := by
    unfold branchAtom
    fun_prop
  have hl : Continuous (fun p : ℝ×Coordinates =>
      |residualLinear p.1 (branchU p.1 (p.2 0)) (branchAtom p.1 (p.2 1))|) := by
    unfold residualLinear branchU branchAtom
    fun_prop
  have hr : Continuous (fun p : ℝ×Coordinates =>
      residualConstant p.1 (branchU p.1 (p.2 0)) (branchAtom p.1 (p.2 1))) := by
    unfold residualConstant branchU branchAtom
    fun_prop
  exact (isOpen_lt continuous_const hu).inter ((isOpen_lt ha continuous_const).inter (isOpen_lt hl hr))

end polyak.Boundary.P1
