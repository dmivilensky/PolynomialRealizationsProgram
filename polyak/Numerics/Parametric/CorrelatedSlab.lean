import polyak.Numerics.Parametric.Slab
import polyak.Numerics.Parametric.Correlated

/-! Article: Appendix B, finite coverage with correlated residual certificates. -/
namespace polyak.Numerics.Parametric
open LeanCert.Core LeanCert.Engine

def allCorrelatedAccepted {n : ℕ} (F : Fin n → Expr) (slabs : List (Slab n))
    (cfg : DyadicConfig) : Bool :=
  slabs.all (fun slab => checkCorrelated F slab.domain slab.certificate cfg)

noncomputable section

theorem allCorrelatedAccepted_append {n : ℕ} {F : Fin n → Expr}
    {left right : List (Slab n)} {cfg : DyadicConfig}
    (hl : allCorrelatedAccepted F left cfg=true)
    (hr : allCorrelatedAccepted F right cfg=true) :
    allCorrelatedAccepted F (left++right) cfg=true := by
  simpa only [allCorrelatedAccepted,List.all_append,Bool.and_eq_true] using And.intro hl hr

theorem correlatedCover_roots {n : ℕ} (F : Fin n → Expr) (slabs : List (Slab n))
    (cfg : DyadicConfig) (start stop : ℚ)
    (hcover : coverCheck start stop slabs=true)
    (haccept : allCorrelatedAccepted F slabs cfg=true)
    {s : ℝ} (hs : s∈Set.Icc (start : ℝ) stop) :
    ∃ slab∈slabs, s∈slab.domain ∧ ∃! x,
      FinBoxMem x (coordinateBox slab.certificate.center slab.certificate.radius) ∧
        system F s x=0 := by
  obtain ⟨slab,hmem,hslab⟩ := coverCheck_sound slabs start stop hcover hs
  have hh : checkCorrelated F slab.domain slab.certificate cfg=true :=
    List.all_eq_true.mp haccept slab hmem
  exact ⟨slab,hmem,hslab,checkCorrelated_sound F slab.domain slab.certificate cfg hh s hslab⟩

end
end polyak.Numerics.Parametric
