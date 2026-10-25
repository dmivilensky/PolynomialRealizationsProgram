import polyak.Numerics.Parametric.DyadicCheck

/-!
Article: Appendix B, exact finite coverage by continuation slabs.
Use: the cover is checked from rational endpoints, not from an archive flag;
each accepted box supplies an actual root for every real parameter it covers.
-/
namespace polyak.Numerics.Parametric
open LeanCert.Core LeanCert.Engine

structure Slab (n : ℕ) where
  domain : IntervalRat
  certificate : WeightedCertificate n

def coverCheck {n : ℕ} (start stop : ℚ) : List (Slab n) → Bool
  | [] => false
  | head::tail => decide (head.domain.lo≤start) &&
      (decide (stop≤head.domain.hi) || coverCheck head.domain.hi stop tail)

def allAccepted {n : ℕ} (F : Fin n → Expr) (slabs : List (Slab n))
    (cfg : DyadicConfig) : Bool :=
  slabs.all (fun slab => checkDyadic F slab.domain slab.certificate cfg)

noncomputable section

theorem allAccepted_append {n : ℕ} {F : Fin n → Expr} {left right : List (Slab n)}
    {cfg : DyadicConfig} (hl : allAccepted F left cfg=true)
    (hr : allAccepted F right cfg=true) : allAccepted F (left++right) cfg=true := by
  simpa only [allAccepted,List.all_append,Bool.and_eq_true] using And.intro hl hr

theorem coverCheck_sound {n : ℕ} (slabs : List (Slab n)) (start stop : ℚ)
    (hc : coverCheck start stop slabs=true) {s : ℝ}
    (hs : s∈Set.Icc (start : ℝ) stop) :
    ∃ slab∈slabs, s∈slab.domain := by
  induction slabs generalizing start stop with
  | nil => simp [coverCheck] at hc
  | cons head tail ih =>
    simp only [coverCheck,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq] at hc
    have hlo : (head.domain.lo : ℝ)≤start := by exact_mod_cast hc.1
    rcases hc.2 with htop|hrest
    · have hhi : (stop : ℝ)≤head.domain.hi := by exact_mod_cast htop
      exact ⟨head,List.mem_cons_self,⟨hlo.trans hs.1,hs.2.trans hhi⟩⟩
    · by_cases hhi : s≤head.domain.hi
      · exact ⟨head,List.mem_cons_self,⟨hlo.trans hs.1,hhi⟩⟩
      · obtain ⟨slab,hmem,hslab⟩ := ih head.domain.hi stop hrest
          ⟨(lt_of_not_ge hhi).le,hs.2⟩
        exact ⟨slab,List.mem_cons_of_mem _ hmem,hslab⟩

/-- The finite accepted table proves existence on the entire closed parameter domain. -/
theorem cover_roots {n : ℕ} (F : Fin n → Expr) (slabs : List (Slab n))
    (cfg : DyadicConfig) (start stop : ℚ)
    (hcover : coverCheck start stop slabs=true) (haccept : allAccepted F slabs cfg=true)
    {s : ℝ} (hs : s∈Set.Icc (start : ℝ) stop) :
    ∃ slab∈slabs, s∈slab.domain ∧ ∃! x,
      FinBoxMem x (coordinateBox slab.certificate.center slab.certificate.radius) ∧
        system F s x=0 := by
  obtain ⟨slab,hmem,hslab⟩ := coverCheck_sound slabs start stop hcover hs
  have hh : checkDyadic F slab.domain slab.certificate cfg=true :=
    List.all_eq_true.mp haccept slab hmem
  exact ⟨slab,hmem,hslab,checkDyadic_sound F slab.domain slab.certificate cfg hh s hslab⟩

end
end polyak.Numerics.Parametric
