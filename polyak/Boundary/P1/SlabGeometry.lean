import polyak.Boundary.P1.CoreCheck
import polyak.Boundary.P1.GeometrySlope
import polyak.Numerics.Parametric.Slab

/-! Finite scalar and derivative checks on the independently accepted P1 root slabs. -/
namespace polyak.Boundary.P1
open LeanCert.Core LeanCert.Engine Numerics.Parametric

def allCoreCheck (ss : List (Slab 2)) (cfg : DyadicConfig) : Bool :=
  ss.all fun s => coreCheck s.domain s.certificate cfg

def allAtomCheck (ss : List (Slab 2)) (cfg : DyadicConfig) : Bool :=
  ss.all fun s => atomCheck s.domain s.certificate cfg

def allSlopeCheck (F : Fin 2 → Expr) (ss : List (Slab 2)) (cfg : DyadicConfig) : Bool :=
  ss.all fun s => geometrySlopeCheck F s.domain
    (coordinateBox s.certificate.center s.certificate.radius) cfg

theorem allCoreCheck_append {as bs : List (Slab 2)} {cfg : DyadicConfig}
    (ha : allCoreCheck as cfg=true) (hb : allCoreCheck bs cfg=true) :
    allCoreCheck (as++bs) cfg=true := by simp [allCoreCheck,List.all_append] at *; tauto

theorem allAtomCheck_append {as bs : List (Slab 2)} {cfg : DyadicConfig}
    (ha : allAtomCheck as cfg=true) (hb : allAtomCheck bs cfg=true) :
    allAtomCheck (as++bs) cfg=true := by simp [allAtomCheck,List.all_append] at *; tauto

noncomputable section

theorem allCoreCheck_sound {ss : List (Slab 2)} {cfg : DyadicConfig}
    (hc : allCoreCheck ss cfg=true) {slab : Slab 2} (hm : slab∈ss)
    {z : ℝ} {x : Fin 2 → ℝ} (hz : 0≤z) (hs : z∈slab.domain)
    (hx : FinBoxMem x (coordinateBox slab.certificate.center slab.certificate.radius)) :
    CoreBounds z x :=
  coreCheck_sound slab.domain slab.certificate cfg (List.all_eq_true.mp hc slab hm) hz hs hx

theorem allAtomCheck_sound {ss : List (Slab 2)} {cfg : DyadicConfig}
    (hc : allAtomCheck ss cfg=true) {slab : Slab 2} (hm : slab∈ss)
    {z : ℝ} {x : Fin 2 → ℝ} (hs : z∈slab.domain)
    (hx : FinBoxMem x (coordinateBox slab.certificate.center slab.certificate.radius)) :
    0≤1/2+z*x 1 :=
  atomCheck_sound slab.domain slab.certificate cfg (List.all_eq_true.mp hc slab hm) hs hx

end
end polyak.Boundary.P1
