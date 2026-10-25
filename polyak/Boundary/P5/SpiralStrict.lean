import polyak.Boundary.P5.PhysicalRoot
import polyak.Certificates.Continuation.P5Properties

/-! Article: Proposition spiralsub on the global P5 regime.
A separate exact scalar reserve proves strict improvement at every positive h. -/
namespace polyak.Boundary.P5
open LeanCert.Core LeanCert.Engine Numerics.Parametric

private def spiralImprovementExpr : Expr := .add
  (.mul (.mul (.const 2) (.add (.const 1) (.var 0))) (.var 1)) (.const (-1))

private theorem improvementsAccepted : Certificates.Continuation.P5.slabs.all
    (fun slab => boundCheck spiralImprovementExpr slab.domain
      (coordinateBox slab.certificate.center slab.certificate.radius) {precision:=-80} true)=true := by
  kernel_decide

noncomputable section

theorem spiral_improvement_of_box {slab : Slab 7} (hm : slab∈Certificates.Continuation.P5.slabs)
    {h : ℝ} {Z : Coordinates} (hh : 0<h) (hs : h∈slab.domain)
    (hX : FinBoxMem Z (coordinateBox slab.certificate.center slab.certificate.radius)) :
    1-1/(2*(1+h))<branchU h Z := by
  have hc := List.all_eq_true.mp improvementsAccepted slab hm
  have hp := boundCheck_sound spiralImprovementExpr slab.domain _ {precision:=-80} true hc hs hX
  change 0<eval spiralImprovementExpr h Z at hp
  have e0 : finEnv (embed h Z) 0=h := rfl
  have e1 : finEnv (embed h Z) 1=Z 0 := rfl
  norm_num [eval,evalFin,spiralImprovementExpr,Expr.eval,e0,e1] at hp
  have hg : 0<1+h := by linarith
  have htw : 1/(2*(1+h))<Z 0 := by
    apply (div_lt_iff₀ (by positivity : 0<2*(1+h))).mpr
    nlinarith
  have hid : branchU h Z-(1-1/(2*(1+h)))=h*(Z 0-1/(2*(1+h))) := by
    unfold branchU
    field_simp
    ring
  have hpos := mul_pos hh (sub_pos.mpr htw)
  linarith

end
end polyak.Boundary.P5
