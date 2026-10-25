import polyak.Boundary.P1.Algebra
import polyak.Numerics.Parametric.Bounds
import polyak.Numerics.Parametric.Weighted

/-!
Article: Appendix B, physical geometry and the positive quadratic dual residual.
Use: the endpoint vanishing factors z and z² are handled algebraically, so
closed interval checks remain valid at the critical point z=0.
-/
namespace polyak.Boundary.P1
open LeanCert.Core LeanCert.Engine Numerics.Parametric

private def zExpr : Expr := .var 0
private def aExpr : Expr := .var 1
private def bExpr : Expr := .var 2
private def square (e : Expr) : Expr := .mul e e
private def uExpr : Expr := .add (.add (.const 1) (.neg (.mul (.const (1/2)) zExpr)))
  (.mul (square zExpr) aExpr)
private def atomExpr : Expr := .mul (square zExpr) bExpr
private def gapExpr : Expr := .add (.add (.neg (.add (.const (1/4))
  (.mul (.const 2) aExpr))) (.mul zExpr aExpr))
  (.neg (.mul (square zExpr) (.add (square aExpr) (square bExpr))))
private def linearExpr : Expr := .add (.add zExpr
  (.neg (.mul (.mul (.const 2) uExpr) (square zExpr))))
  (.mul (.mul (.const 2) (square zExpr)) atomExpr)
private def constantExpr : Expr := .add
  (.add (.add (.add (.const 2) (.neg (.mul (.mul (.const 2) zExpr) uExpr)))
    (.mul (square zExpr) (square uExpr))) (.neg (.mul (.const 2) (square zExpr))))
  (.add (.mul (.mul (.const 2) atomExpr) (.add zExpr
    (.neg (.mul (.mul (.const 2) uExpr) (square zExpr)))))
    (.mul (.mul (.const 3) (square atomExpr)) (square zExpr)))

def geometricExpr : Fin 5 → Expr := ![uExpr,
  .add (.const (1/2)) (.neg (.mul zExpr aExpr)), .neg bExpr,
  .add (.const (1/2)) (.mul zExpr bExpr),
  .add (.const (1/2)) (.mul zExpr gapExpr)]

def residualExpr : Fin 2 → Expr := ![.add constantExpr linearExpr,
  .add constantExpr (.neg linearExpr)]

def physicalCheck (I : IntervalRat) (cert : WeightedCertificate 2)
    (cfg : DyadicConfig) : Bool :=
  decide (∀ i, boundCheck (geometricExpr i) I (coordinateBox cert.center cert.radius) cfg false=true) &&
  decide (∀ i, boundCheck (residualExpr i) I (coordinateBox cert.center cert.radius) cfg true=true)

noncomputable section

theorem geometricExpr_eval (z : ℝ) (x : Coordinates) :
    (fun i => eval (geometricExpr i) z x)=![branchU z (x 0),
      1/2-z*x 0,-x 1,1/2+z*x 1,1/2+z*gapLinear z (x 0) (x 1)] := by
  have h0 : finEnv (embed z x) 0=z := rfl
  have h1 : finEnv (embed z x) 1=x 0 := rfl
  have h2 : finEnv (embed z x) 2=x 1 := rfl
  ext i
  fin_cases i <;>
    norm_num [geometricExpr,uExpr,zExpr,aExpr,bExpr,gapExpr,square,eval,evalFin,
      Expr.eval,h0,h1,h2,branchU,gapLinear] <;> ring_nf
  all_goals simp

theorem residualExpr_eval (z : ℝ) (x : Coordinates) :
    (fun i => eval (residualExpr i) z x)=![
      residualConstant z (branchU z (x 0)) (branchAtom z (x 1))+
        residualLinear z (branchU z (x 0)) (branchAtom z (x 1)),
      residualConstant z (branchU z (x 0)) (branchAtom z (x 1))-
        residualLinear z (branchU z (x 0)) (branchAtom z (x 1))] := by
  have h0 : finEnv (embed z x) 0=z := rfl
  have h1 : finEnv (embed z x) 1=x 0 := rfl
  have h2 : finEnv (embed z x) 2=x 1 := rfl
  ext i
  fin_cases i <;>
    norm_num [residualExpr,constantExpr,linearExpr,uExpr,atomExpr,zExpr,aExpr,bExpr,
      square,eval,evalFin,Expr.eval,h0,h1,h2,branchU,branchAtom,
      residualConstant,residualLinear] <;> ring_nf

theorem physicalCheck_sound (I : IntervalRat) (cert : WeightedCertificate 2)
    (cfg : DyadicConfig) (hc : physicalCheck I cert cfg=true)
    {z : ℝ} {x : Coordinates} (hz : 0≤z) (hs : z∈I)
    (hx : FinBoxMem x (coordinateBox cert.center cert.radius)) :
    0≤branchU z (x 0) ∧ branchU z (x 0)≤1 ∧
    (-z/2≤branchAtom z (x 1) ∧ branchAtom z (x 1)≤0) ∧
    z/2≤1-(branchAtom z (x 1))^2-(branchU z (x 0))^2 ∧
    |residualLinear z (branchU z (x 0)) (branchAtom z (x 1))|<
      residualConstant z (branchU z (x 0)) (branchAtom z (x 1)) := by
  simp only [physicalCheck,Bool.and_eq_true,decide_eq_true_eq] at hc
  have hg (i : Fin 5) := boundCheck_sound (geometricExpr i) I _ cfg false (hc.1 i) hs hx
  have hr (i : Fin 2) := boundCheck_sound (residualExpr i) I _ cfg true (hc.2 i) hs hx
  have ge := geometricExpr_eval z x
  have re := residualExpr_eval z x
  have h0 := hg 0
  have h1 := hg 1
  have h2 := hg 2
  have h3 := hg 3
  have h4 := hg 4
  have r0 := hr 0
  have r1 := hr 1
  change 0≤eval (geometricExpr 0) z x at h0
  change 0≤eval (geometricExpr 1) z x at h1
  change 0≤eval (geometricExpr 2) z x at h2
  change 0≤eval (geometricExpr 3) z x at h3
  change 0≤eval (geometricExpr 4) z x at h4
  change 0<eval (residualExpr 0) z x at r0
  change 0<eval (residualExpr 1) z x at r1
  rw [show eval (geometricExpr 0) z x=_ from congrFun ge 0] at h0
  rw [show eval (geometricExpr 1) z x=_ from congrFun ge 1] at h1
  rw [show eval (geometricExpr 2) z x=_ from congrFun ge 2] at h2
  rw [show eval (geometricExpr 3) z x=_ from congrFun ge 3] at h3
  rw [show eval (geometricExpr 4) z x=_ from congrFun ge 4] at h4
  rw [show eval (residualExpr 0) z x=_ from congrFun re 0] at r0
  rw [show eval (residualExpr 1) z x=_ from congrFun re 1] at r1
  change 0≤branchU z (x 0) at h0
  change 0≤1/2-z*x 0 at h1
  change 0≤ -x 1 at h2
  change 0≤1/2+z*x 1 at h3
  change 0≤1/2+z*gapLinear z (x 0) (x 1) at h4
  change 0<residualConstant z (branchU z (x 0)) (branchAtom z (x 1))+
    residualLinear z (branchU z (x 0)) (branchAtom z (x 1)) at r0
  change 0<residualConstant z (branchU z (x 0)) (branchAtom z (x 1))-
    residualLinear z (branchU z (x 0)) (branchAtom z (x 1)) at r1
  refine ⟨h0,?_,⟨?_,?_⟩,?_,?_⟩
  · have hp := mul_nonneg hz h1
    unfold branchU
    nlinarith
  · have hp := mul_nonneg hz h3
    unfold branchAtom
    nlinarith
  · exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg z) (by linarith)
  · have hp := mul_nonneg hz h4
    have he : 1-(branchAtom z (x 1))^2-(branchU z (x 0))^2=
        z+z^2*gapLinear z (x 0) (x 1) := by
      unfold branchAtom branchU gapLinear
      ring
    rw [he]
    nlinarith
  · exact abs_lt.mpr ⟨by linarith,by linarith⟩

end
end polyak.Boundary.P1
