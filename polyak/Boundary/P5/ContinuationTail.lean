import polyak.Boundary.P5.LocalLimits
import Mathlib.Analysis.Calculus.MeanValue

/-!
Article: (centralbounds), global uniform tail reserves from polynomial continuation bounds.
Use: a fixed arccos derivative bound supplies phase control; elementary sine
Lipschitz control supplies amplitude, and the charge is bounded after exact regularization.
-/
noncomputable section
namespace polyak.Boundary.P5
open Spectral

private theorem arccos_local_lipschitz {x : ℝ} (hx : x∈Set.Icc (-51/100 : ℝ) (-1/2)) :
    |Real.arccos x-Real.arccos (-1/2)|≤(6/5)*|x-(-1/2)| := by
  have hd (r : ℝ) (hr : r∈Set.Icc (-51/100 : ℝ) (-1/2)) : DifferentiableAt ℝ Real.arccos r :=
    (Real.hasDerivAt_arccos (by linarith [hr.1]) (by linarith [hr.2])).differentiableAt
  have hb (r : ℝ) (hr : r∈Set.Icc (-51/100 : ℝ) (-1/2)) : ‖deriv Real.arccos r‖≤(6/5 : ℝ) := by
    have hr2 : r^2≤(51/100 : ℝ)^2 := by
      have hp := mul_nonpos_of_nonneg_of_nonpos (show 0≤r+51/100 by linarith [hr.1])
        (show r-51/100≤0 by linarith [hr.2])
      nlinarith
    have hpos : 0<1-r^2 := by nlinarith
    have hs : 5/6<Real.sqrt (1-r^2) := by
      nlinarith [Real.sq_sqrt hpos.le,Real.sqrt_nonneg (1-r^2)]
    rw [Real.deriv_arccos,Real.norm_eq_abs,abs_neg,abs_div,abs_one,abs_of_pos (by linarith : 0<Real.sqrt (1-r^2))]
    exact (div_le_iff₀ (by linarith : 0<Real.sqrt (1-r^2))).mpr (by linarith)
  have hm := Convex.norm_image_sub_le_of_norm_deriv_le hd hb (convex_Icc (-51/100 : ℝ) (-1/2))
    (show (-1/2 : ℝ)∈Set.Icc (-51/100) (-1/2) by norm_num) hx
  simpa only [Real.norm_eq_abs] using hm

theorem phase_of_coordinate_bounds {h B : ℝ} (hh : 0<h) (hmax : h≤59/2500)
    (hB : -27/100<B ∧ B<0) :
    |Real.arccos (-1/2+h*B)-2*Real.pi/3|<h/3 := by
  have hp := mul_lt_mul_of_pos_left hB.1 hh
  have hx : -1/2+h*B∈Set.Icc (-51/100 : ℝ) (-1/2) := by
    constructor
    · nlinarith
    · have hmul := mul_nonpos_of_nonneg_of_nonpos hh.le hB.2.le
      linarith
  have hm := arccos_local_lipschitz hx
  have ha : Real.arccos (-1/2 : ℝ)=2*Real.pi/3 := by
    simpa [Spiral.cosine,Spiral.G] using Spiral.angle_zero
  rw [ha,show (-1/2+h*B)-(-1/2)=h*B by ring,abs_mul,abs_of_pos hh,abs_of_neg hB.2] at hm
  nlinarith

theorem amplitude_of_coordinate_bounds {h A B : ℝ} (hh : 0<h) (hA : 0<A ∧ A<11/20)
    (hphase : |Real.arccos (-1/2+h*B)-2*Real.pi/3|<h/3) :
    |2*(1/2+h*A)*Real.sin (Real.arccos (-1/2+h*B))-Real.sqrt 3/2|<2*h := by
  let θ := Real.arccos (-1/2+h*B)
  change |θ-2*Real.pi/3|<h/3 at hphase
  have hs0 : Real.sin (2*Real.pi/3)=Real.sqrt 3/2 := by
    have ha : Real.arccos (-1/2 : ℝ)=2*Real.pi/3 := by
      simpa [Spiral.cosine,Spiral.G] using Spiral.angle_zero
    rw [← ha,Real.sin_arccos,sqrt_cycle]
  have hs := Real.abs_sin_sub_sin_le θ (2*Real.pi/3)
  rw [hs0] at hs
  have he : 2*(1/2+h*A)*Real.sin θ-Real.sqrt 3/2=
      2*h*A*Real.sin θ+(Real.sin θ-Real.sqrt 3/2) := by ring
  have hp : |2*h*A*Real.sin θ|≤2*h*A := by
    rw [abs_mul,abs_of_pos (mul_pos (mul_pos (by norm_num) hh) hA.1)]
    simpa using mul_le_mul_of_nonneg_left (Real.abs_sin_le_one θ) (mul_nonneg (mul_nonneg (by norm_num) hh.le) hA.1.le)
  have htri := abs_add_le (2*h*A*Real.sin θ) (Real.sin θ-Real.sqrt 3/2)
  change |2*(1/2+h*A)*Real.sin θ-Real.sqrt 3/2|<2*h
  rw [he]
  have hAA := mul_lt_mul_of_pos_left hA.2 hh
  nlinarith

theorem charge_abs_lt {h D : ℝ} (hh : 0<h) (hmax : h≤59/2500)
    (hD : 0≤D ∧ D≤11/5) : |h*D/Real.sinh (Real.arcosh (1+h))|<6/25 := by
  rw [charge_eq_regular hh]
  have hsq : (regularCharge h D)^2=h*D^2/(h+2) := by
    unfold regularCharge
    rw [div_pow,mul_pow,Real.sq_sqrt hh.le,Real.sq_sqrt (by linarith : 0≤h+2)]
  have hd2 : D^2≤(11/5 : ℝ)^2 := (sq_le_sq₀ hD.1 (by norm_num)).mpr hD.2
  have hprod := mul_le_mul_of_nonneg_left hd2 hh.le
  have hh2 : 0<h+2 := by linarith
  have hb : h*D^2/(h+2)<(6/25 : ℝ)^2 := by
    rw [div_lt_iff₀ hh2]
    nlinarith
  apply (sq_lt_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ)≤6/25)).mp
  simpa only [sq_abs,hsq] using hb

/-- All reserves are polynomial or coordinate inequalities supplied by finite boxes. -/
structure ContinuationTailBounds (h : ℝ) (Z : Coordinates) : Prop where
  h_pos : 0<h
  h_le : h≤59/2500
  A_band : 0<Z 0 ∧ Z 0<11/20
  B_band : -27/100<Z 1 ∧ Z 1<0
  P_band : 0<Z 3 ∧ Z 3<3
  D_band : 0<Z 4 ∧ Z 4<11/5
  x_interior : -1<branchX h Z ∧ branchX h Z<1
  y_interior : -1<Z 2 ∧ Z 2<1
  gap_gt : 49/100<branchGap h Z
  main_coefficient : |mainGapCoefficient h Z|<1
  mean_coefficient : |meanGapCoefficient h Z|<2

theorem ContinuationTailBounds.toTailBounds {h : ℝ} {Z : Coordinates}
    (hb : ContinuationTailBounds h Z) :
    TailBounds h (branchU h Z) (h*Z 3) (h*Z 4)
      ⟨branchX h Z,⟨hb.x_interior.1.le,hb.x_interior.2.le⟩⟩
      ⟨Z 2,⟨hb.y_interior.1.le,hb.y_interior.2.le⟩⟩ := by
  have hphase := phase_of_coordinate_bounds hb.h_pos hb.h_le hb.B_band
  have hamp := amplitude_of_coordinate_bounds hb.h_pos hb.A_band hphase
  have hc := charge_abs_lt hb.h_pos hb.h_le ⟨hb.D_band.1.le,hb.D_band.2.le⟩
  refine {
    h_pos := hb.h_pos
    h_le := hb.h_le
    u_nonneg := ?_
    u_lt := ?_
    p_nonneg := mul_nonneg hb.h_pos.le hb.P_band.1.le
    p_le := ?_
    d_nonneg := mul_nonneg hb.h_pos.le hb.D_band.1.le
    d_le := ?_
    gap_gt := hb.gap_gt
    star_gt := ?_
    main_gap := ?_
    mean_gap := ?_
    amplitude := hamp
    phase := hphase }
  · unfold branchU
    exact add_nonneg (by norm_num) (mul_nonneg hb.h_pos.le hb.A_band.1.le)
  · have hh := mul_lt_mul_of_pos_left hb.A_band.2 hb.h_pos
    unfold branchU
    nlinarith [hb.h_le]
  · nlinarith [mul_lt_mul_of_pos_left hb.P_band.2 hb.h_pos]
  · nlinarith [mul_lt_mul_of_pos_left hb.D_band.2 hb.h_pos]
  · change 1/4<branchGap h Z-|h*Z 4/Real.sinh (Real.arcosh (1+h))|
    linarith [hb.gap_gt]
  · change |g (branchU h Z) (branchX h Z)-1/2|<h
    rw [main_gap_difference,abs_mul,abs_of_pos hb.h_pos]
    nlinarith [mul_lt_mul_of_pos_left hb.main_coefficient hb.h_pos]
  · change |branchGap h Z-1/2|<2*h
    rw [mean_gap_difference,abs_mul,abs_of_pos hb.h_pos]
    nlinarith [mul_lt_mul_of_pos_left hb.mean_coefficient hb.h_pos]

end polyak.Boundary.P5
