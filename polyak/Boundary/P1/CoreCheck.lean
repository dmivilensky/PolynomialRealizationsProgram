import polyak.Boundary.P1.BoxBounds
import polyak.Boundary.P1.CoreBounds

/-! Exact scalar checks valid on the whole P1 continuation, including its short extension past zW. -/
namespace polyak.Boundary.P1
open LeanCert.Core LeanCert.Engine Numerics.Parametric

def coreCheck (I : IntervalRat) (cert : WeightedCertificate 2) (cfg : DyadicConfig) : Bool :=
  decide (∀ i : Fin 5, i≠3 →
    boundCheck (geometricExpr i) I (coordinateBox cert.center cert.radius) cfg false=true) &&
  decide (∀ i, boundCheck (residualExpr i) I (coordinateBox cert.center cert.radius) cfg true=true)

def atomCheck (I : IntervalRat) (cert : WeightedCertificate 2) (cfg : DyadicConfig) : Bool :=
  boundCheck (geometricExpr 3) I (coordinateBox cert.center cert.radius) cfg false

noncomputable section

theorem coreCheck_sound (I : IntervalRat) (cert : WeightedCertificate 2)
    (cfg : DyadicConfig) (hc : coreCheck I cert cfg=true)
    {z : ℝ} {x : Coordinates} (hz : 0≤z) (hs : z∈I)
    (hx : FinBoxMem x (coordinateBox cert.center cert.radius)) : CoreBounds z x := by
  simp only [coreCheck,Bool.and_eq_true,decide_eq_true_eq] at hc
  have hg (i : Fin 5) (hi : i≠3) := boundCheck_sound (geometricExpr i) I _ cfg false (hc.1 i hi) hs hx
  have hr (i : Fin 2) := boundCheck_sound (residualExpr i) I _ cfg true (hc.2 i) hs hx
  have ge := geometricExpr_eval z x
  have re := residualExpr_eval z x
  have h0 := hg 0 (by decide)
  have h1 := hg 1 (by decide)
  have h2 := hg 2 (by decide)
  have h4 := hg 4 (by decide)
  have r0 := hr 0
  have r1 := hr 1
  change 0≤eval (geometricExpr 0) z x at h0
  change 0≤eval (geometricExpr 1) z x at h1
  change 0≤eval (geometricExpr 2) z x at h2
  change 0≤eval (geometricExpr 4) z x at h4
  change 0<eval (residualExpr 0) z x at r0
  change 0<eval (residualExpr 1) z x at r1
  rw [show eval (geometricExpr 0) z x=_ from congrFun ge 0] at h0
  rw [show eval (geometricExpr 1) z x=_ from congrFun ge 1] at h1
  rw [show eval (geometricExpr 2) z x=_ from congrFun ge 2] at h2
  rw [show eval (geometricExpr 4) z x=_ from congrFun ge 4] at h4
  rw [show eval (residualExpr 0) z x=_ from congrFun re 0] at r0
  rw [show eval (residualExpr 1) z x=_ from congrFun re 1] at r1
  change 0≤branchU z (x 0) at h0
  change 0≤1/2-z*x 0 at h1
  change 0≤ -x 1 at h2
  change 0≤1/2+z*gapLinear z (x 0) (x 1) at h4
  refine ⟨h0,?_,?_,?_,r1,r0⟩
  · have hp := mul_nonneg hz h1
    unfold branchU
    nlinarith
  · exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg z) (by linarith)
  · have hp := mul_nonneg hz h4
    have he : 1-(branchAtom z (x 1))^2-(branchU z (x 0))^2=
        z+z^2*gapLinear z (x 0) (x 1) := by unfold branchAtom branchU gapLinear; ring
    rw [he]
    nlinarith

theorem atomCheck_sound (I : IntervalRat) (cert : WeightedCertificate 2)
    (cfg : DyadicConfig) (hc : atomCheck I cert cfg=true)
    {z : ℝ} {x : Coordinates} (hs : z∈I)
    (hx : FinBoxMem x (coordinateBox cert.center cert.radius)) : 0≤1/2+z*x 1 := by
  have hg := boundCheck_sound (geometricExpr 3) I _ cfg false hc hs hx
  change 0≤eval (geometricExpr 3) z x at hg
  rw [show eval (geometricExpr 3) z x=_ from congrFun (geometricExpr_eval z x) 3] at hg
  exact hg

theorem CoreBounds.with_atom_lower {z : ℝ} {x : Coordinates} (h : CoreBounds z x)
    (ha : -z/2≤branchAtom z (x 1)) : PhysicalBounds z x :=
  ⟨h.u_nonneg,h.u_le_one,ha,h.atom_nonpos,h.gap_lower,h.residual_left,h.residual_right⟩

end
end polyak.Boundary.P1
