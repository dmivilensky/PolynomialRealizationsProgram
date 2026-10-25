import polyak.Boundary.P5.GeometryCheck
import polyak.Boundary.P5.PrefixCheck
import polyak.Numerics.Parametric.Slab

/-! Composition of finite source properties over the complete checked P5 cover. -/
namespace polyak.Boundary.P5
open LeanCert.Core LeanCert.Engine Numerics.Parametric

def allPrefixCheck (codes : (n : Fin 24) → LagCode n) (slabs : List (Slab 7))
    (cfg : DyadicConfig) : Bool :=
  slabs.all fun s => prefixCheck codes s.domain s.certificate cfg

def allGeometryCheck (slabs : List (Slab 7)) (cfg : DyadicConfig) : Bool :=
  slabs.all fun s => continuationGeometryCheck s.domain s.certificate cfg

theorem allPrefixCheck_append (codes : (n : Fin 24) → LagCode n)
    {a b : List (Slab 7)} {cfg : DyadicConfig}
    (ha : allPrefixCheck codes a cfg=true) (hb : allPrefixCheck codes b cfg=true) :
    allPrefixCheck codes (a++b) cfg=true := by
  simp only [allPrefixCheck,List.all_append,Bool.and_eq_true]
  exact ⟨ha,hb⟩

theorem allGeometryCheck_append {a b : List (Slab 7)} {cfg : DyadicConfig}
    (ha : allGeometryCheck a cfg=true) (hb : allGeometryCheck b cfg=true) :
    allGeometryCheck (a++b) cfg=true := by
  simp only [allGeometryCheck,List.all_append,Bool.and_eq_true]
  exact ⟨ha,hb⟩

noncomputable section

theorem allPrefixCheck_sound (codes : (n : Fin 24) → LagCode n)
    {slabs : List (Slab 7)} {cfg : DyadicConfig}
    (ha : allPrefixCheck codes slabs cfg=true) {s : Slab 7} (hs : s∈slabs)
    {h : ℝ} {Z : Coordinates} (hh : 0≤h) (hI : h∈s.domain)
    (hX : FinBoxMem Z (coordinateBox s.certificate.center s.certificate.radius))
    (hZ : regularSystem (h,Z)=0) :
    ∀ n : ℕ, 1≤n → n<24 → ∀ σ : ℝ, (σ= -1 ∨ σ=1) → 0≤actualPrimal h Z n σ := by
  exact prefixCheck_sound codes s.domain s.certificate cfg (List.all_eq_true.mp ha s hs) hh hI hX hZ

theorem allGeometryCheck_sound {slabs : List (Slab 7)} {cfg : DyadicConfig}
    (ha : allGeometryCheck slabs cfg=true) {s : Slab 7} (hs : s∈slabs)
    {h : ℝ} {Z : Coordinates} (hh : 0<h) (hmax : h≤59/2500) (hI : h∈s.domain)
    (hX : FinBoxMem Z (coordinateBox s.certificate.center s.certificate.radius)) :
    ContinuationGeometry h Z :=
  continuationGeometryCheck_sound s.domain s.certificate cfg (List.all_eq_true.mp ha s hs)
    hh hmax hI hX

end
end polyak.Boundary.P5
