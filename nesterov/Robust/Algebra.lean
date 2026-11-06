import nesterov.TwoStep.Cubic

/-! Exact robust-momentum circle algebra, including a positive-circle
interpolation between the two extreme largest-curvature roots. -/
namespace nesterov.Robust
noncomputable section
open Set

def symbol (r ρ zL ξ : ℝ) : ℝ :=
  TwoStep.P0 r (ρ+ρ^2) zL (ρ^3) 0+
    TwoStep.P1 r (ρ+ρ^2) zL (ρ^3) 0*ξ+
    TwoStep.P2 r (ρ+ρ^2) zL (ρ^3) 0*ξ^2

theorem symbol_on_design (ρ zL ξ : ℝ) :
    symbol ρ ρ zL ξ=ρ^3*(ρ+zL)*ξ*((1-ρ)^2+2*ρ*ξ) := by
  unfold symbol TwoStep.P0 TwoStep.P1 TwoStep.P2 TwoStep.E0 TwoStep.E1 TwoStep.E2
  ring

def tmmG (r ρ ξ : ℝ) : ℝ :=
  (r-ρ^2)*(1-r)+ξ*(r^2+ρ^2+4*r*ρ)-2*r*ρ*ξ^2

theorem symbol_tmm (r ρ ξ : ℝ) :
    symbol r ρ (-ρ) ξ=r*(r^2-ρ^2)*tmmG r ρ ξ := by
  unfold symbol tmmG TwoStep.P0 TwoStep.P1 TwoStep.P2 TwoStep.E0 TwoStep.E1 TwoStep.E2
  ring

theorem tmmG_on_design (ρ ξ : ℝ) :
    tmmG ρ ρ ξ=ρ*((1-ρ)^2+2*ρ*ξ*(3-ξ)) := by
  unfold tmmG
  ring

theorem symbol_top (r ρ ξ : ℝ) :
    symbol r ρ ρ ξ=
      r*((r-ρ)^2+2*r*ρ*ξ)*((r-ρ^2)*(1-r)+(r^2+ρ^2)*ξ) := by
  unfold symbol TwoStep.P0 TwoStep.P1 TwoStep.P2 TwoStep.E0 TwoStep.E1 TwoStep.E2
  ring

theorem symbol_interpolation (r ρ zL ξ : ℝ) :
    2*ρ*symbol r ρ zL ξ=
      (ρ-zL)*symbol r ρ (-ρ) ξ+(ρ+zL)*symbol r ρ ρ ξ := by
  unfold symbol TwoStep.P0 TwoStep.P1 TwoStep.P2 TwoStep.E0 TwoStep.E1 TwoStep.E2
  ring

theorem symbol_pos {r ρ zL ξ : ℝ} (hρ : 0<ρ) (hρ1 : ρ<1)
    (hrρ : ρ<r) (hr1 : r<1) (hzL : zL∈Icc (-ρ) ρ) (hξ : ξ∈Icc (0:ℝ) 2) :
    0<symbol r ρ zL ξ := by
  have hr : 0<r := hρ.trans hrρ
  have hξ0 : 0≤ξ := hξ.1
  have hρsq : ρ^2<r := (by nlinarith : ρ^2<ρ).trans hrρ
  have hbase : 0<(r-ρ^2)*(1-r) := mul_pos (sub_pos.mpr hρsq) (sub_pos.mpr hr1)
  have hG : 0<tmmG r ρ ξ := by
    have hb : 0≤r^2+ρ^2+2*r*ρ*(2-ξ) :=
      add_nonneg (add_nonneg (sq_nonneg r) (sq_nonneg ρ))
        (mul_nonneg (by positivity) (by linarith [hξ.2]))
    have hh := mul_nonneg hξ.1 hb
    unfold tmmG
    nlinarith
  have hlow : 0<symbol r ρ (-ρ) ξ := by
    rw [symbol_tmm]
    exact mul_pos (mul_pos hr (by nlinarith)) hG
  have htop : 0<symbol r ρ ρ ξ := by
    rw [symbol_top]
    apply mul_pos
    · exact mul_pos hr (add_pos_of_pos_of_nonneg (sq_pos_of_pos (sub_pos.mpr hrρ))
        (by positivity))
    · exact add_pos_of_pos_of_nonneg hbase (by positivity)
  have hi := symbol_interpolation r ρ zL ξ
  have hp : 0<(ρ-zL)*symbol r ρ (-ρ) ξ+(ρ+zL)*symbol r ρ ρ ξ := by
    by_cases hz : zL<ρ
    · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hz) hlow)
        (mul_nonneg (by linarith [hzL.1]) htop.le)
    · have he : zL=ρ := le_antisymm hzL.2 (le_of_not_gt hz)
      rw [he,sub_self,zero_mul,zero_add]
      exact mul_pos (by linarith) htop
  rw [←hi] at hp
  exact (mul_pos_iff_of_pos_left (by positivity : (0:ℝ)<2*ρ)).mp hp

end
end nesterov.Robust
