import polyak.Numerics.Parametric.CorrelatedSlab
import polyak.Numerics.Parametric.CorrelatedInterior

/-!
Article: Appendix B, analytic gluing of a finite checked continuation cover.
Use: box-local uniqueness, compatibility on overlaps and strict root interiors
identify the selected root with a local analytic implicit function. Continuity
of the selection is a conclusion, including at every slab junction.
-/
noncomputable section
namespace polyak.Numerics.Parametric
open LeanCert.Core LeanCert.Engine Filter
open scoped Topology

def familyDomain {n k : ℕ} (slabs : Fin k → Slab n) : Set ℝ :=
  {s | ∃ i,s∈(slabs i).domain}

def familyRootProperty {n k : ℕ} (F : Fin n → Expr) (slabs : Fin k → Slab n)
    (s : ℝ) (x : Fin n → ℝ) : Prop :=
  system F s x=0 ∧ ∃ i,s∈(slabs i).domain ∧
    FinBoxMem x (coordinateBox (slabs i).certificate.center (slabs i).certificate.radius)

structure CompatibleFamily {n k : ℕ} (F : Fin n → Expr) (cfg : DyadicConfig)
    (slabs : Fin k → Slab n) : Prop where
  checked : ∀ i,checkCorrelated F (slabs i).domain (slabs i).certificate cfg=true
  compatible : ∀ i j (s : ℝ), s∈(slabs i).domain → s∈(slabs j).domain →
    ∀ x y : Fin n → ℝ,
      FinBoxMem x (coordinateBox (slabs i).certificate.center (slabs i).certificate.radius) →
      system F s x=0 →
      FinBoxMem y (coordinateBox (slabs j).certificate.center (slabs j).certificate.radius) →
      system F s y=0 → x=y

namespace CompatibleFamily
variable {n k : ℕ} {F : Fin n → Expr} {cfg : DyadicConfig} {slabs : Fin k → Slab n}
  (family : CompatibleFamily F cfg slabs)
include family

theorem exists_unique {s : ℝ} (hs : s∈familyDomain slabs) :
    ∃! x,familyRootProperty F slabs s x := by
  obtain ⟨i,hi⟩ := hs
  obtain ⟨x,hx,_⟩ := checkCorrelated_sound F (slabs i).domain (slabs i).certificate cfg
    (family.checked i) s hi
  refine ⟨x,⟨hx.2,i,hi,hx.1⟩,?_⟩
  rintro y ⟨hy,j,hj,hybox⟩
  exact family.compatible j i s hj hi y x hybox hy hx.1 hx.2

def root (s : ℝ) : Fin n → ℝ := by
  classical
  exact if hs : s∈familyDomain slabs then (family.exists_unique hs).choose else 0

theorem root_spec {s : ℝ} (hs : s∈familyDomain slabs) :
    familyRootProperty F slabs s (family.root s) := by
  classical
  simpa only [root,dite_eq_left hs] using (family.exists_unique hs).choose_spec.1

theorem root_source {s : ℝ} (hs : s∈familyDomain slabs) : system F s (family.root s)=0 :=
  (family.root_spec hs).1

theorem root_mem {s : ℝ} (i : Fin k) (hs : s∈(slabs i).domain) :
    FinBoxMem (family.root s)
      (coordinateBox (slabs i).certificate.center (slabs i).certificate.radius) := by
  obtain ⟨hzero,j,hj,hjbox⟩ := family.root_spec ⟨i,hs⟩
  obtain ⟨x,hx,_⟩ := checkCorrelated_sound F (slabs i).domain (slabs i).certificate cfg
    (family.checked i) s hs
  have he := family.compatible j i s hj hs (family.root s) x hjbox hzero hx.1 hx.2
  rw [he]
  exact hx.1

theorem local_agreement {s : ℝ} (hs : s∈familyDomain slabs) :
    ∃ g : ℝ → (Fin n → ℝ), AnalyticAt ℝ g s ∧ g s=family.root s ∧
      ∀ᶠ r in 𝓝 s, r∈familyDomain slabs → family.root r=g r := by
  obtain ⟨i,hi⟩ := hs
  obtain ⟨g,hg,hself,hzero⟩ := checkCorrelated_analytic_branch F (slabs i).domain
    (slabs i).certificate cfg (family.checked i) hi (family.root_mem i hi)
      (family.root_source ⟨i,hi⟩)
  have hboxes : ∀ᶠ r in 𝓝 s, ∀ j, r∈(slabs j).domain →
      FinBoxMem (g r) (coordinateBox (slabs j).certificate.center (slabs j).certificate.radius) := by
    apply Filter.eventually_all.mpr
    intro j
    by_cases hj : s∈(slabs j).domain
    · have hstrict := checkCorrelated_root_strict F (slabs j).domain (slabs j).certificate cfg
        (family.checked j) hj (family.root_mem j hj) (family.root_source ⟨j,hj⟩)
      have hnear : ∀ᶠ r in 𝓝 s, g r∈strictBox
          (coordinateBox (slabs j).certificate.center (slabs j).certificate.radius) :=
        hg.continuousAt ((isOpen_strictBox _).mem_nhds (by rwa [hself]))
      filter_upwards [hnear] with r hr _
      exact strictBox_subset hr
    · have hnear : {r : ℝ | r∉(slabs j).domain}∈𝓝 s :=
        isClosed_Icc.isOpen_compl.mem_nhds hj
      filter_upwards [hnear] with r hr hri
      exact (hr hri).elim
  refine ⟨g,hg,hself,?_⟩
  filter_upwards [hzero,hboxes] with r hr hbox hrD
  obtain ⟨j,hj⟩ := hrD
  exact (checkCorrelated_sound F (slabs j).domain (slabs j).certificate cfg
    (family.checked j) r hj).unique
      ⟨family.root_mem j hj,family.root_source ⟨j,hj⟩⟩ ⟨hbox j hj,hr⟩

theorem analyticWithinAt {s : ℝ} (hs : s∈familyDomain slabs) :
    AnalyticWithinAt ℝ family.root (familyDomain slabs) s := by
  obtain ⟨g,hg,hself,heq⟩ := family.local_agreement hs
  apply hg.analyticWithinAt.congr_of_eventuallyEq _ hself.symm
  filter_upwards [heq.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with r hr hrD
  exact hr hrD

theorem continuousOn : ContinuousOn family.root (familyDomain slabs) :=
  fun _ hs => (family.analyticWithinAt hs).continuousWithinAt

theorem analyticAt {s : ℝ} (hs : s∈interior (familyDomain slabs)) :
    AnalyticAt ℝ family.root s := by
  obtain ⟨g,hg,_,heq⟩ := family.local_agreement (interior_subset hs)
  apply hg.congr
  filter_upwards [heq,mem_interior_iff_mem_nhds.mp hs] with r hr hrD
  exact (hr hrD).symm

end CompatibleFamily
end polyak.Numerics.Parametric
