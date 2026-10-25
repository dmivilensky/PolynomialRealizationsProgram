import polyak.FareyPlateau.Ray.ThresholdDefinition

/-! The infimum over Fin m enumerations includes every finite indexed
admissible symbol; reindexing changes neither its phase floor nor its R. -/
noncomputable section
namespace polyak.FareyPlateau.Symbols
open scoped BigOperators
variable {I J : Type*} [Fintype I] [Fintype J]

theorem Admissible.reindex {k b : ℤ} {bar : ℝ} {n : I→ℤ} {w : I→ℝ}
    (h : Admissible k b bar n w) (e : J≃I) :
    Admissible k b bar (fun j=>n (e j)) (fun j=>w (e j)) := by
  classical
  refine ⟨h.injective.comp e.injective,fun j=>h.nonzero (e j),
    fun j=>h.positive (e j),?_,fun j=>h.positions (e j),?_,?_,?_⟩
  · rw [e.sum_comp]; exact h.normalization
  · obtain ⟨i,l,hne,hi,hl⟩ := h.two_one
    exact ⟨e.symm i,e.symm l,by simpa using hne,by simpa using hi,by simpa using hl⟩
  · have him : Finset.univ.image e=Finset.univ := by ext i; simp
    change Finset.univ.gcd (n ∘ e)=1
    rw [←Finset.gcd_image,him]
    exact h.support_gcd
  · simp only [Finset.sum_filter]
    rw [e.sum_comp (fun i=>if n i%k=b%k then w i*((n i:ℝ)-bar) else 0),
      e.sum_comp (fun i=>if n i%k=0 then w i*(n i:ℝ) else 0)]
    simpa only [Finset.sum_filter] using h.slope

end polyak.FareyPlateau.Symbols
