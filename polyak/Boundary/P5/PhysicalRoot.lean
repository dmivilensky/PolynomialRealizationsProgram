import polyak.Boundary.P5.GeometryCheck
import polyak.Boundary.P5.PrefixCheck
import polyak.Boundary.P5.LocalOptimal

/-! Full original spectral feasibility and optimality for any certified P5 source root.
Every finite arithmetic hypothesis below is discharged by the continuation tables. -/
noncomputable section
namespace polyak.Boundary.P5
open Spectral

theorem sourceRoot_feasible {h t : ℝ} {Z : Coordinates}
    (hb : ContinuationGeometry h Z) (ht : Real.cosh t=1+h)
    (hp : ∀ n : ℕ, 1≤n → n<24 → ∀ σ : ℝ, (σ= -1 ∨ σ=1) → 0≤actualPrimal h Z n σ) :
    FeasibleU (branchU h Z) t
      (twoAtomSpectrum (h*Z 3) (mul_nonneg hb.tail.h_pos.le hb.tail.P_band.1.le)
        hb.mass_lt_one.le
        ⟨branchX h Z,⟨hb.tail.x_interior.1.le,hb.tail.x_interior.2.le⟩⟩
        ⟨Z 2,⟨hb.tail.y_interior.1.le,hb.tail.y_interior.2.le⟩⟩)
      (h*Z 4/Real.sinh t) := by
  have ht0 : t≠0 := by
    rintro rfl
    norm_num only [Real.cosh_zero] at ht
    linarith [hb.tail.h_pos]
  exact feasibleU_of_tail_prefix Z
    ⟨hb.tail.x_interior.1.le,hb.tail.x_interior.2.le⟩
    ⟨hb.tail.y_interior.1.le,hb.tail.y_interior.2.le⟩ hb.tail.toTailBounds ht0 ht hp

theorem sourceRoot_optimal {h t : ℝ} {Z : Coordinates}
    (hb : ContinuationGeometry h Z) (hZ : regularSystem (h,Z)=0)
    (hw5 : 0≤1-Z 5-Z 6) (ht : Real.cosh t=1+h)
    (hp : ∀ n : ℕ, 1≤n → n<24 → ∀ σ : ℝ, (σ= -1 ∨ σ=1) → 0≤actualPrimal h Z n σ) :
    V t=Real.arsinh (branchU h Z) := by
  let W := weights235 (Z 5) (Z 6) hb.weight2.le hb.weight3.le hw5
  apply primal_dual_optimal W hb.tail.toTailBounds.u_nonneg (sourceRoot_feasible hb ht hp)
  intro c
  rw [ht]
  change 0≤(dualPolynomial (weights235 _ _ _ _ _) _ _).eval (c : ℝ)
  rw [dualPolynomial_eq_source (by linarith [hb.tail.h_pos] : (1 : ℝ)<1+h)]
  unfold branchU
  rw [← dualReal_closed]
  exact div_nonneg (continuation_dual_nonneg hb.tail.h_pos.le hZ hb.mass_lt_one
    hb.tail.x_interior.2 hb.atoms_ordered hb.residual c)
    (commonDenominator_pos (by linarith [hb.tail.h_pos])).le

end polyak.Boundary.P5
