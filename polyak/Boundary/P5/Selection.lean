import polyak.Certificates.Continuation.P5Family

/-!
Article: Appendix B, the actual global regularized P5 continuation.
Use: exact checked endpoint transfers glue the finite interval cover. The
selected root is analytic, rather than being assumed continuous before gluing.
-/
noncomputable section
namespace polyak.Boundary.P5.Selection
open LeanCert.Core LeanCert.Engine Numerics.Parametric
open scoped Topology

theorem domain : familyDomain Certificates.Continuation.P5.table=Set.Icc (0 : ℝ) (11791/500000) := by
  have bounds : ∀ i : Fin 20,0≤(Certificates.Continuation.P5.table i).domain.lo ∧
      (Certificates.Continuation.P5.table i).domain.hi≤11791/500000 := by kernel_decide
  apply Set.Subset.antisymm
  · rintro h ⟨i,hi⟩
    have hlo : (0 : ℝ)≤(Certificates.Continuation.P5.table i).domain.lo := by exact_mod_cast (bounds i).1
    have hhi : ((Certificates.Continuation.P5.table i).domain.hi : ℝ)≤11791/500000 := by
      have hb : ((Certificates.Continuation.P5.table i).domain.hi : ℝ)≤
          ((11791/500000 : ℚ) : ℝ) := by exact_mod_cast (bounds i).2
      norm_num at hb ⊢
      exact hb
    exact ⟨hlo.trans hi.1,hi.2.trans hhi⟩
  · intro h hh
    obtain ⟨slab,hmem,hslab⟩ := coverCheck_sound Certificates.Continuation.P5.slabs 0 (11791/500000) Certificates.Continuation.P5.covered
      (s:=h) (by norm_num at *; exact hh)
    rw [← Certificates.Continuation.P5.table_list] at hmem
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hmem
    exact ⟨i,hslab⟩

def continuation : ℝ → (Fin 7 → ℝ) := Certificates.Continuation.P5.chain.compatibleFamily.root

theorem continuation_source {h : ℝ} (hh : h∈Set.Icc (0 : ℝ) (11791/500000)) :
    regularSystem (h,continuation h)=0 := by
  have hs : h∈familyDomain Certificates.Continuation.P5.table := by rwa [domain]
  simpa only [continuation,Certificates.Continuation.P5.source_system] using Certificates.Continuation.P5.chain.compatibleFamily.root_source hs

theorem continuation_mem (i : Fin 20) {h : ℝ} (hh : h∈(Certificates.Continuation.P5.table i).domain) :
    FinBoxMem (continuation h)
      (coordinateBox (Certificates.Continuation.P5.table i).certificate.center (Certificates.Continuation.P5.table i).certificate.radius) :=
  Certificates.Continuation.P5.chain.compatibleFamily.root_mem i hh

theorem analyticWithinAt {h : ℝ} (hh : h∈Set.Icc (0 : ℝ) (11791/500000)) :
    AnalyticWithinAt ℝ continuation (Set.Icc (0 : ℝ) (11791/500000)) h := by
  simpa only [continuation,domain] using Certificates.Continuation.P5.chain.compatibleFamily.analyticWithinAt
    (s:=h) (by rwa [domain])

theorem continuousOn : ContinuousOn continuation (Set.Icc (0 : ℝ) (11791/500000)) := by
  simpa only [continuation,domain] using Certificates.Continuation.P5.chain.compatibleFamily.continuousOn

theorem analyticAt {h : ℝ} (hh : h∈Set.Ioo (0 : ℝ) (11791/500000)) :
    AnalyticAt ℝ continuation h := by
  apply Certificates.Continuation.P5.chain.compatibleFamily.analyticAt
  simpa only [domain,interior_Icc] using hh

end polyak.Boundary.P5.Selection
