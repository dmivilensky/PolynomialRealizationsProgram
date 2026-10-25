import polyak.ModeLocking.Boundary.HeavyGraph
import Mathlib.Topology.Separation.Lemmas

/-! Periodic heavy atoms have rational angles. A nonconstant continuous heavy
position on a connected family forces uncountably many nonperiodic tunings. -/
noncomputable section
namespace polyak.ModeLocking
open General Levels MeasureTheory Set

theorem positive_atom_mem_carrier {w:Measure Frequency} {A:Set Frequency}
    (hcar:∀ᵐω∂w,ω∈A) {x:Frequency} (hx:0<w {x}) : x∈A := by
  by_contra hn
  have hz:w Aᶜ=0:=by
    rw [ae_iff] at hcar
    exact hcar
  have hsub:({x}:Set Frequency)⊆Aᶜ:=by simpa only [singleton_subset_iff,mem_compl_iff] using hn
  exact hx.ne' (measure_mono_null hsub hz)

theorem periodic_heavy_position {K:ℕ} {q:Tuning} (hq:q∈BoundaryInGap K)
    (hp:PeriodicBoundary q) {m:ℝ} (hm:1/2<m) {r:Frequency}
    (hr:∀ν:ProbabilityMeasure Frequency,NormalizedExtremal q ν→
      m≤(ν : Measure Frequency).real {r}) :
    ∃L:ℕ,3≤L ∧ r∈periodicGrid L := by
  obtain ⟨L,hL,w,hw,hcar⟩:=(boundary_periodic_iff hq).mp hp
  obtain ⟨ν,hν,hνcar⟩:=hw.normalize_carried hcar
  have hz:(ν : Measure Frequency) (periodicGrid L)ᶜ=0:=by
    have hz:=hνcar
    rw [ae_iff] at hz
    exact hz
  have hzero:(ν : Measure Frequency) {frequencyZero}=0:=by
    apply measure_mono_null (t:=(periodicGrid L)ᶜ) ?_ hz
    intro ω hω
    rw [mem_singleton_iff] at hω
    subst ω
    intro h
    exact lt_irrefl (0:ℝ) (by simpa only [frequencyZero] using h.1)
  have hmass:0<(ν : Measure Frequency).real {r}:=lt_of_lt_of_le (by linarith) (hr ν ⟨hν,hzero⟩)
  have hpos:0<(ν : Measure Frequency) {r}:=by
    apply bot_lt_iff_ne_bot.mpr
    intro hz
    simp only [Measure.real,hz] at hmass
    exact lt_irrefl _ hmass
  exact ⟨L,hL,positive_atom_mem_carrier hνcar hpos⟩

theorem grid_angle_rational {L:ℕ} (hL:0<L) {x:Frequency} (hx:x∈periodicGrid L) :
    ∃r:ℚ,(x:ℝ)=2*Real.pi*(r:ℝ) := by
  obtain ⟨_,j,hj⟩:=hx
  refine ⟨(j:ℚ)/(L:ℚ),?_⟩
  push_cast
  rw [←mul_div_assoc]
  apply (eq_div_iff (by exact_mod_cast hL.ne':(L:ℝ)≠0)).mpr
  nlinarith

theorem periodic_heavy_angle_rational {K:ℕ} {q:Tuning} (hq:q∈BoundaryInGap K)
    (hp:PeriodicBoundary q) {m:ℝ} (hm:1/2<m) {r:Frequency}
    (hr:∀ν:ProbabilityMeasure Frequency,NormalizedExtremal q ν→
      m≤(ν : Measure Frequency).real {r}) :
    ∃a:ℚ,(r:ℝ)=2*Real.pi*(a:ℝ) := by
  obtain ⟨L,hL,hgrid⟩:=periodic_heavy_position hq hp hm hr
  exact grid_angle_rational (by omega) hgrid

def allPeriodicFrequencies : Set Frequency := ⋃n:ℕ,periodicGrid (n+3)

theorem countable_allPeriodicFrequencies : allPeriodicFrequencies.Countable := by
  exact Set.countable_iUnion (fun n=>(periodicGrid_finite (by omega : 0<n+3)).countable)

theorem nonconstant_heavy_uncountable {K:ℕ} {C:Set Tuning}
    (hC:C⊆BoundaryInGap K) (hconn:IsConnected C) {m:ℝ} (hm:1/2<m)
    (hh:∀q∈C,∀ν:ProbabilityMeasure Frequency,NormalizedExtremal q ν→
      ∃x:Frequency,m≤(ν : Measure Frequency).real {x})
    (r:C→Frequency)
    (hr:∀q:C,∀ν:ProbabilityMeasure Frequency,NormalizedExtremal q ν→
      m≤(ν : Measure Frequency).real {r q})
    (hvar:¬∃x:Frequency,∀q:C,r q=x) :
    ¬(C\{q|PeriodicBoundary q}).Countable := by
  intro hcount
  let _ : PreconnectedSpace C := Subtype.preconnectedSpace hconn.isPreconnected
  have hc:=continuous_heavy_position hC hm hh r hr
  have hsmall:{p:C|¬PeriodicBoundary p}.Countable := by
    have ht:=hcount.preimage (f:=fun p:C=>(p:Tuning)) Subtype.val_injective
    apply ht.mono
    intro p hp
    exact ⟨p.property,hp⟩
  have hrange:(range r).Countable:=by
    apply (countable_allPeriodicFrequencies.union (hsmall.image r)).mono
    rintro x ⟨q,rfl⟩
    by_cases hp:PeriodicBoundary q
    · obtain ⟨L,hL,hgrid⟩:=periodic_heavy_position (hC q.property) hp hm (hr q)
      left
      apply mem_iUnion.mpr
      refine ⟨L-3,?_⟩
      simpa only [Nat.sub_add_cancel hL] using hgrid
    · exact Or.inr ⟨q,hp,rfl⟩
  have hsingle: (range r).Subsingleton:=hrange.isTotallyDisconnected _ subset_rfl
    (isPreconnected_range hc)
  obtain ⟨q,hq⟩:=hconn.nonempty
  let q0:C:=⟨q,hq⟩
  exact hvar ⟨r q0,fun p=>hsingle (mem_range_self p) (mem_range_self q0)⟩

end polyak.ModeLocking
