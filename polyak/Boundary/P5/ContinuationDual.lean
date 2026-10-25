import polyak.Boundary.P5.LocalDual
import polyak.Boundary.P5.LocalLimits

/-! Exact two-contact dual factorization for arbitrary continued P5 source roots. -/
noncomputable section
namespace polyak.Boundary.P5
open Spectral Polynomial

def residual₂ (h : ℝ) (Z : Coordinates) : ℝ := (dualReal h Z).coeff 6
def residual₁ (h : ℝ) (Z : Coordinates) : ℝ :=
  (dualReal h Z).coeff 5+2*(branchX h Z+Z 2)*(dualReal h Z).coeff 6
def residual₀ (h : ℝ) (Z : Coordinates) : ℝ :=
  (dualReal h Z).coeff 4+2*(branchX h Z+Z 2)*(dualReal h Z).coeff 5+
    (3*(branchX h Z)^2+4*branchX h Z*Z 2+3*(Z 2)^2)*(dualReal h Z).coeff 6

theorem continuation_dual_factor {h : ℝ} {Z : Coordinates} (hh : 0≤h)
    (hZ : regularSystem (h,Z)=0) (hp : h*Z 3<1) (hx : branchX h Z<1)
    (hxy : branchX h Z<Z 2) (c : ℝ) :
    (dualReal h Z).eval c=(c-branchX h Z)^2*(c-Z 2)^2*
      (residual₂ h Z*c^2+residual₁ h Z*c+residual₀ h Z) := by
  obtain ⟨hy,hdx,hdy⟩ := regularSystem_dual_exact h Z
  rw [hZ] at hy hdx hdy
  have hf := hermite_sextic_eval (dualReal_natDegree h Z) (ne_of_lt hxy)
    (dualReal_main_root hh hZ hp hx) hdx.symm hy.symm hdy.symm c
  simpa only [residual₂,residual₁,residual₀,branchX,add_assoc] using hf

theorem continuation_dual_nonneg {h : ℝ} {Z : Coordinates} (hh : 0≤h)
    (hZ : regularSystem (h,Z)=0) (hp : h*Z 3<1) (hx : branchX h Z<1)
    (hxy : branchX h Z<Z 2) (hq : 0<residual₀ h Z-|residual₁ h Z|-|residual₂ h Z|)
    (c : Frequency) : 0≤(dualReal h Z).eval (c : ℝ) := by
  rw [continuation_dual_factor hh hZ hp hx hxy]
  exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (quadratic_pos_on_frequency hq c).le

end polyak.Boundary.P5
