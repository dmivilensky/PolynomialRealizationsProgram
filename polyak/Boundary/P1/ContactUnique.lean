import polyak.Boundary.P1.Bounds

/-! Article: the quartic residual identifies the unique contact atom and source coordinates. -/
noncomputable section
namespace polyak.Boundary.P1
open Spectral

theorem quartic_eq_zero_iff {z u : ℝ} {a : Frequency} (h0 : quartic z u a=0)
    (h1 : quarticDerivative z u a=0)
    (hq : |residualLinear z u a|<residualConstant z u a) (c : Frequency) :
    quartic z u c=0 ↔ c=a := by
  rw [quartic_factor h0 h1]
  constructor
  · intro he
    have hs := (mul_eq_zero.mp he).resolve_right (residual_pos hq c).ne'
    apply Subtype.ext
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hs)
  · rintro rfl
    simp

/-- Once the twist is fixed, physical contact roots of the divided source are unique. -/
theorem regularRoot_unique_of_u {z : ℝ} {Z W : Coordinates} (hz : 0<z) (hz1 : z≤3/4)
    (hZ : regularSystem (z,Z)=0) (hW : regularSystem (z,W)=0)
    (hZb : PhysicalBounds z Z) (hWb : PhysicalBounds z W)
    (hu : branchU z (Z 0)=branchU z (W 0)) : Z=W := by
  have hWa : quartic z (branchU z (Z 0)) (physicalAtom hz hz1 hWb)=0 := by
    rw [hu]
    exact (regularSystem_contacts hW).1
  have ha : physicalAtom hz hz1 hWb=physicalAtom hz hz1 hZb :=
    (quartic_eq_zero_iff (a := physicalAtom hz hz1 hZb)
      (regularSystem_contacts hZ).1 (regularSystem_contacts hZ).2
      hZb.residual (physicalAtom hz hz1 hWb)).mp hWa
  have ha' : branchAtom z (W 1)=branchAtom z (Z 1) := congrArg Subtype.val ha
  have hz2 : 0<z^2 := sq_pos_of_pos hz
  ext i
  fin_cases i
  · change Z 0=W 0
    apply mul_left_cancel₀ hz2.ne'
    unfold branchU at hu
    linarith
  · change Z 1=W 1
    apply mul_left_cancel₀ hz2.ne'
    unfold branchAtom at ha'
    exact ha'.symm

end polyak.Boundary.P1
