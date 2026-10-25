import polyak.Boundary.P1.CoreBounds
import polyak.Boundary.P1.ContactUnique

/-!
Article: P1 continuation gluing, uniqueness before primal feasibility is known.
The actual quartic is strictly increasing in the nonnegative twist coordinate;
two nonnegative quartics with interior double contacts therefore coincide.
-/
noncomputable section
namespace polyak.Boundary.P1
open Spectral

theorem quartic_sub (z u v c : ℝ) :
    quartic z v c-quartic z u c=(v-u)*((u+v)*contactD z c+
      2*z*(1-c^2)*(1+z*c)) := by
  unfold quartic contactD
  ring

theorem quartic_strictMono_u {z : ℝ} (hz : 0≤z) (hz1 : z≤3/4) (c : Frequency) :
    StrictMonoOn (fun u => quartic z u c) (Set.Ici 0) := by
  intro u hu v hv huv
  change 0≤u at hu
  change 0≤v at hv
  have hD := contactD_pos hz hz1 c
  have hc : 0≤1-(c : ℝ)^2 := by nlinarith [c.property.1,c.property.2]
  have hzc : 0<1+z*(c : ℝ) := by
    have hm := mul_nonneg hz (show 0≤(c : ℝ)+1 by linarith [c.property.1])
    nlinarith
  have hp : 0<(u+v)*contactD z c+2*z*(1-(c : ℝ)^2)*(1+z*(c : ℝ)) :=
    add_pos_of_pos_of_nonneg (mul_pos (by linarith) hD) (by positivity)
  have hh := mul_pos (sub_pos.mpr huv) hp
  rw [← quartic_sub] at hh
  linarith

def admissibleAtom {z : ℝ} {Z : Coordinates} (h : ContactAdmissible (z,Z)) : Frequency :=
  ⟨branchAtom z (Z 1),abs_le.mp h.2.1.le⟩

/-- Algebraic gluing works even on the small extension past the physical junction. -/
theorem admissibleRoot_unique {z : ℝ} {Z W : Coordinates} (hz : 0≤z) (hz1 : z≤3/4)
    (hZ : regularSystem (z,Z)=0) (hW : regularSystem (z,W)=0)
    (hZa : ContactAdmissible (z,Z)) (hWa : ContactAdmissible (z,W)) : Z=W := by
  by_cases hz0 : z=0
  · subst z
    exact (criticalPoint_unique Z hZ).trans (criticalPoint_unique W hW).symm
  have hzp : 0<z := lt_of_le_of_ne hz (Ne.symm hz0)
  let a := admissibleAtom hZa
  let b := admissibleAtom hWa
  have hQZ : ∀ c : Frequency, 0≤quartic z (branchU z (Z 0)) c :=
    quartic_nonneg (regularSystem_contacts hZ).1 (regularSystem_contacts hZ).2 hZa.2.2
  have hQW : ∀ c : Frequency, 0≤quartic z (branchU z (W 0)) c :=
    quartic_nonneg (regularSystem_contacts hW).1 (regularSystem_contacts hW).2 hWa.2.2
  have hu : branchU z (Z 0)=branchU z (W 0) := by
    rcases lt_trichotomy (branchU z (Z 0)) (branchU z (W 0)) with he | he | he
    · have hm := quartic_strictMono_u hz hz1 b hZa.1.le hWa.1.le he
      have hb : quartic z (branchU z (W 0)) b=0 := (regularSystem_contacts hW).1
      linarith [hQZ b]
    · exact he
    · have hm := quartic_strictMono_u hz hz1 a hWa.1.le hZa.1.le he
      have ha : quartic z (branchU z (Z 0)) a=0 := (regularSystem_contacts hZ).1
      linarith [hQW a]
  have hb : quartic z (branchU z (Z 0)) b=0 := by rw [hu]; exact (regularSystem_contacts hW).1
  have ha : b=a := (quartic_eq_zero_iff (a := a) (regularSystem_contacts hZ).1
    (regularSystem_contacts hZ).2 hZa.2.2 b).mp hb
  have hat : branchAtom z (W 1)=branchAtom z (Z 1) := congrArg Subtype.val ha
  have hz2 : z^2≠0 := pow_ne_zero _ hz0
  ext i
  fin_cases i
  · change Z 0=W 0
    apply mul_left_cancel₀ hz2
    unfold branchU at hu
    linarith
  · change Z 1=W 1
    apply mul_left_cancel₀ hz2
    exact hat.symm

theorem coreRoot_unique {z : ℝ} {Z W : Coordinates} (hz : 0<z) (hz1 : z≤3/4)
    (hZ : regularSystem (z,Z)=0) (hW : regularSystem (z,W)=0)
    (hZb : CoreBounds z Z) (hWb : CoreBounds z W) : Z=W :=
  admissibleRoot_unique hz.le hz1 hZ hW (hZb.admissible hz hz1 hZ) (hWb.admissible hz hz1 hW)

end polyak.Boundary.P1
