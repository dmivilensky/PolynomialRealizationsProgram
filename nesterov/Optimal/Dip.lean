import nesterov.Optimal.ModerateAlgebra

/-! The affine dip, its vertex/depth, and the source's literal dip bound. -/
namespace nesterov.TwoStep.Scaling
noncomputable section
open Filter Set
open scoped Topology
variable {A : Type*} {l : Filter A} (F : Scaling A l 3 2 (1/2))

def cornerBPrime (a : A) : ℝ := (F.stabilityMargin a+4*F.cornerAlpha a-12)/2
def cornerAffineB (a : A) (ξ : ℝ) : ℝ := 5-4*F.cornerAlpha a+F.cornerBPrime a*ξ

theorem corner_N_reformulation (a : A) (ξ : ℝ) :
    F.cornerNAt a ξ-4*(3-ξ)=2*ξ*F.cornerAffineB a ξ+
      (F.thetaAt a-3)*(4+2*ξ-4*ξ^2) := by
  unfold cornerNAt cornerAffineB cornerBPrime
  ring

theorem corner_B_two (a : A) : F.cornerAffineB a 2=F.stabilityMargin a-7 := by
  unfold cornerAffineB cornerBPrime
  ring

theorem corner_dip_completed_square (a : A) (ξ : ℝ)
    (hd : 0<F.cornerDefect a) (hB : F.cornerBPrime a≠0) :
    ξ*F.cornerAffineB a ξ=F.cornerBPrime a*(ξ-F.cornerDefect a/(2*F.cornerBPrime a))^2-
      F.cornerDefect a^2/(4*F.cornerBPrime a) := by
  have hpos : 0<4*F.cornerAlpha a-5 := by
    have hh : 0<max (4*F.cornerAlpha a-5) 0 := hd
    exact (lt_max_iff.mp hh).resolve_right (lt_irrefl 0)
  unfold cornerAffineB cornerDefect
  rw [max_eq_left hpos.le]
  field_simp
  ring

theorem corner_dip_minimum (a : A) (hd : 0<F.cornerDefect a)
    (hB : 0<F.cornerBPrime a)
    (hv : F.cornerDefect a/(2*F.cornerBPrime a)∈Icc (0:ℝ) 2) :
    IsLeast ((fun ξ=>ξ*F.cornerAffineB a ξ) '' Icc (0:ℝ) 2)
      (-(F.cornerDefect a^2/(4*F.cornerBPrime a))) := by
  constructor
  · refine ⟨F.cornerDefect a/(2*F.cornerBPrime a),hv,?_⟩
    dsimp only
    rw [F.corner_dip_completed_square a _ hd hB.ne',sub_self,zero_pow (by decide : 2≠0),mul_zero,zero_sub]
  · rintro v ⟨ξ,_,rfl⟩
    dsimp only
    rw [F.corner_dip_completed_square a ξ hd hB.ne']
    nlinarith [mul_nonneg hB.le (sq_nonneg (ξ-F.cornerDefect a/(2*F.cornerBPrime a)))]

theorem corner_dip_upper (a : A) {ξ c : ℝ} (hd : 0<F.cornerDefect a)
    (hB : 0<F.cornerBPrime a) (hc : c≤1) (hξ : ξ∈Icc (0:ℝ) 2)
    (hx : ξ≤F.cornerDefect a/(2*F.cornerBPrime a)) :
    F.cornerNAt a ξ-4*c*(3-ξ)≤ -F.cornerDefect a*ξ+12*(1-c)+
      24*|F.thetaAt a-3| := by
  have hprod : 2*F.cornerBPrime a*ξ≤F.cornerDefect a :=
    by nlinarith [(le_div_iff₀ (by positivity : 0<2*F.cornerBPrime a)).mp hx]
  have hmul := mul_le_mul_of_nonneg_right hprod hξ.1
  have hshape : |4+2*ξ-4*ξ^2|≤24 := by
    have hsq : ξ^2≤4 := by nlinarith [hξ.1,hξ.2]
    exact abs_le.mpr ⟨by nlinarith,by nlinarith [sq_nonneg ξ]⟩
  have he : (F.thetaAt a-3)*(4+2*ξ-4*ξ^2)≤24*|F.thetaAt a-3| := by
    calc
      _≤|(F.thetaAt a-3)*(4+2*ξ-4*ξ^2)| := le_abs_self _
      _=|F.thetaAt a-3| * |4+2*ξ-4*ξ^2| := abs_mul _ _
      _≤|F.thetaAt a-3| * 24 := mul_le_mul_of_nonneg_left hshape (abs_nonneg _)
      _=24*|F.thetaAt a-3| := by ring
  rw [F.cornerN_defect_expansion a hd]
  have hBex : 2*F.cornerBPrime a=F.stabilityMargin a+5+F.cornerDefect a-12 := by
    have hpos : 0<4*F.cornerAlpha a-5 := by
      have hh : 0<max (4*F.cornerAlpha a-5) 0 := hd
      exact (lt_max_iff.mp hh).resolve_right (lt_irrefl 0)
    unfold cornerBPrime cornerDefect
    rw [max_eq_left hpos.le]
    ring
  rw [hBex] at hmul
  nlinarith [mul_nonneg (sub_nonneg.mpr hc) hξ.1]

theorem corner_dip_error_tendsto :
    Tendsto (fun a=>24*|F.thetaAt a-3|) l (𝓝 0) := by
  have h : Tendsto (fun a=>F.thetaAt a-3) l (𝓝 0) := by
    simpa only [thetaAt,sub_self] using F.theta_tendsto.sub_const 3
  simpa using h.abs.const_mul 24

end
end nesterov.TwoStep.Scaling
