import polyak.Boundary.P1.SlopeCheck
import polyak.Numerics.Parametric.Slab

/-! Article: the source derivative bounds on a finite accepted continuation cover. -/
namespace polyak.Boundary.P1
open LeanCert.Core LeanCert.Engine Numerics.Parametric

def allSourceSlopeCheck (F : Fin 2 → Expr) (ss : List (Slab 2)) (cfg : DyadicConfig) : Bool :=
  ss.all fun s => sourceSlopeCheck F s.domain
    (coordinateBox s.certificate.center s.certificate.radius) cfg

theorem allSourceSlopeCheck_append {F : Fin 2 → Expr} {as bs : List (Slab 2)} {cfg : DyadicConfig}
    (ha : allSourceSlopeCheck F as cfg=true) (hb : allSourceSlopeCheck F bs cfg=true) :
    allSourceSlopeCheck F (as++bs) cfg=true := by
  simp [allSourceSlopeCheck,List.all_append] at *
  tauto

noncomputable section

theorem allSourceSlopeCheck_sound (F : Fin 2 → Expr) (hF : ∀ i,ADSupported (F i))
    {ss : List (Slab 2)} {cfg : DyadicConfig} (hc : allSourceSlopeCheck F ss cfg=true)
    {slab : Slab 2} (hm : slab∈ss) {s : ℝ} {x v : Fin 2 → ℝ}
    (hs : s∈slab.domain) (hx : FinBoxMem x (coordinateBox slab.certificate.center slab.certificate.radius))
    (he : (jacobian F s x).mulVec v= -parameterDerivative F s x) :
    let du:= -1/2+2*s*x 0+s^2*v 0
    du<0 ∧ du^2*s^2*(1-s^2)<1+(1-s/2+s^2*x 0)^2 :=
  sourceSlopeCheck_sound F hF slab.domain _ cfg (List.all_eq_true.mp hc slab hm) hs hx he

end
end polyak.Boundary.P1
