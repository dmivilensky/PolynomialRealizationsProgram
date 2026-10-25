import polyak.General.Regions.Contacts
import polyak.General.Regions.Radii
import polyak.General.Regions.Underdamped

/-! Named source regions for subsequent Part II stages. Rate divergence
and convergence of every fixed objective are separate predicates; no
unproved implication from a non-strict rate bound is used. -/
noncomputable section
namespace polyak.General.Regions
open Set

/-- Source D, defined by the original worst-case rate. -/
def divergenceSet : Set Tuning:={q | 1≤q.rate}

/-- The source quadratic regime in the lag-one region (Theorem B(b)). -/
def quadraticRegion : Set Tuning:=
  {q | OmegaOne q ∧ Real.sqrt q.beta<q.rhoQ ∧ rOne q=q.rhoQ}

theorem mem_divergenceSet_iff (q : Tuning) : q∈divergenceSet ↔ 1≤q.rate:=Iff.rfl

theorem quadraticRegion_iff_cubic (q : Tuning) : q∈quadraticRegion ↔
    OmegaOne q ∧ Real.sqrt q.beta<q.rhoQ ∧ ∀ c∈Icc (-1:ℝ) 1,0≤q.H q.rhoQ c := by
  constructor
  · rintro ⟨hΩ,hd,hr⟩
    exact ⟨hΩ,hd,(rOne_eq_rhoQ_iff q hΩ hd).mp hr⟩
  · rintro ⟨hΩ,hd,hH⟩
    exact ⟨hΩ,hd,(rOne_eq_rhoQ_iff q hΩ hd).mpr hH⟩

theorem rate_eq_quadratic_on_region {q : Tuning} (hq : q∈quadraticRegion) :
    q.rate=q.rhoQ := by
  have hb:=original_rate_bounds q hq.1
  exact le_antisymm (hq.2.2 ▸ hb.2.1) hb.1

theorem rate_eq_quadratic_requires_overdamping (q : Tuning) (h : q.rate=q.rhoQ) :
    Real.sqrt q.beta<q.rhoQ := by
  have hle : Real.sqrt q.beta≤q.rhoQ:=
    (sqrt_le_rootRadius (p:=1+q.beta-q.x) q.beta_nonneg).trans (le_max_left _ _)
  apply lt_of_le_of_ne hle
  intro he
  have hh:=underdamped_rate_strict q he.symm
  change q.rhoQ<q.rate at hh
  rw [h] at hh
  exact lt_irrefl _ hh

end polyak.General.Regions
