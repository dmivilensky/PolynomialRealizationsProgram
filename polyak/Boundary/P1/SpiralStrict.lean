import polyak.Boundary.P1.Physical
import polyak.Boundary.P1.Endpoint
import polyak.Spiral.Feasibility

/-!
Article: Proposition spiralsub, strict improvement on the physical P1 arc.
Use: equality with the spiral would force its atom to be the sole quartic contact,
and the derivative contact then forces the exact switch zW.
-/
noncomputable section
namespace polyak.Boundary.P1
open Spectral

theorem quartic_spiral_zero (z : ℝ) : quartic z (1-z/2) (-z/2)=0 := by
  unfold quartic
  ring

theorem quarticDerivative_spiral (z : ℝ) :
    quarticDerivative z (1-z/2) (-z/2)= -z*(z-2)*(z^2+2*z-2)/2 := by
  unfold quarticDerivative
  ring

theorem positive_switch_unique {z : ℝ} (hz : 0<z) (he : z^2+2*z-2=0) : z=zW := by
  have hp : 0<z+zW+2 := by linarith [zW_pos]
  have hf : (z-zW)*(z+zW+2)=0 := by nlinarith [zW_equation]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_right hp.ne')

/-- Coincidence of the P1 twist with the spiral is possible only at their exact junction. -/
theorem regularRoot_spiral_eq_imp_switch {z : ℝ} {Z : Coordinates}
    (hz : 0<z) (hz1 : z≤3/4) (hZ : regularSystem (z,Z)=0)
    (h : PhysicalBounds z Z) (hu : branchU z (Z 0)=1-z/2) : z=zW := by
  let c : Frequency := ⟨-z/2,⟨by linarith,by linarith⟩⟩
  have h0 : quartic z (branchU z (Z 0)) c=0 := by
    change quartic z (branchU z (Z 0)) (-z/2)=0
    rw [hu]
    exact quartic_spiral_zero z
  have ha : c=physicalAtom hz hz1 h :=
    (quartic_eq_zero_iff (a := physicalAtom hz hz1 h) (regularSystem_contacts hZ).1
      (regularSystem_contacts hZ).2 h.residual c).mp h0
  have ha' : -z/2=branchAtom z (Z 1) := congrArg Subtype.val ha
  have hd := (regularSystem_contacts hZ).2
  rw [hu,← ha',quarticDerivative_spiral] at hd
  have hf : (-z)*(z-2)*(z^2+2*z-2)=0 := by linarith
  have hn : (-z)*(z-2)≠0 := mul_ne_zero (neg_ne_zero.mpr hz.ne') (by linarith)
  exact positive_switch_unique hz ((mul_eq_zero.mp hf).resolve_left hn)

theorem spiral_twist_le_regularRoot {z t : ℝ} {Z : Coordinates}
    (hz : 0<z) (hz1 : z≤3/4) (hZ : regularSystem (z,Z)=0)
    (h : PhysicalBounds z Z) (ht : Real.cosh t=1/z) :
    1-z/2≤branchU z (Z 0) := by
  have hs : Real.arsinh (Spiral.twist t)≤V t :=
    (isGreatest_V t).2 ⟨Spiral.spectrum t,Spiral.valueConstant t,Spiral.feasible t⟩
  rw [regularRoot_optimal hz hz1 hZ h ht] at hs
  have htw : Spiral.twist t=1-z/2 := by
    unfold Spiral.twist Spiral.G
    rw [ht]
    field_simp
  rw [htw] at hs
  exact Real.arsinh_le_arsinh.mp hs

/-- The actual P1 optimum strictly exceeds the spiral away from the exact switch. -/
theorem regularRoot_strict_spiral {z t : ℝ} {Z : Coordinates}
    (hz : 0<z) (hz1 : z≤3/4) (hZ : regularSystem (z,Z)=0)
    (h : PhysicalBounds z Z) (ht : Real.cosh t=1/z) (hW : z≠zW) :
    Real.arsinh (1-1/(2*Real.cosh t))<V t := by
  have hu : 1-z/2<branchU z (Z 0) := by
    apply lt_of_le_of_ne (spiral_twist_le_regularRoot hz hz1 hZ h ht)
    intro he
    exact hW (regularRoot_spiral_eq_imp_switch hz hz1 hZ h he.symm)
  rw [regularRoot_optimal hz hz1 hZ h ht,ht]
  have he : 1-1/(2*(1/z))=1-z/2 := by field_simp
  rw [he]
  exact Real.arsinh_strictMono hu

end polyak.Boundary.P1
