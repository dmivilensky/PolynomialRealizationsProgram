import polyak.Levels.Geometry.LevelZero
import polyak.Levels.Geometry.Boundary
import polyak.Levels.Geometry.DipInterior
import polyak.Levels.Geometry.Tangency
import polyak.General.Regions.Contacts

/-! All dynamical and boundary conclusions of Theorems tangency and levelzero. -/
noncomputable section
namespace polyak.Levels.Geometry
open General Set

def transportStrictSymbol {Θ Ψ : Curve} {N : Set ℤ} (he : Θ=Ψ)
    (S : StrictSymbol Θ N) : StrictSymbol Ψ N:=he ▸ S

theorem transportStrictSymbol_lags {Θ Ψ : Curve} {N : Set ℤ} (he : Θ=Ψ)
    (S : StrictSymbol Θ N) : (transportStrictSymbol he S).symbol.lags=S.symbol.lags := by
  subst Ψ
  rfl

theorem weak_phase_of_dip_empty (q : Tuning) (hd : dip (tuningCurve q)=∅) :
    ∀ω : Frequency,(ω:ℝ)/2≤q.angle ω := by
  intro ω
  apply le_of_not_gt
  intro hh
  have hm : ω∈dip (tuningCurve q):=hh
  rw [hd] at hm
  exact hm

theorem nonperiodic_tangency_certificate (q : Tuning) {ω : Frequency}
    (hweak : ∀η : Frequency,(η:ℝ)/2≤q.angle η)
    (hcontact : q.angle ω=(ω:ℝ)/2)
    (hgrid : ∀K : ℕ,∀hK : 3≤K,ω≠firstFrequency K (by omega)) :
    ∃K : ℕ,2≤K ∧ InWindow K ω ∧
      ∃S : StrictSymbol (tuningCurve q) nonzeroLags,
        S.symbol.lags={1,-(K:ℤ)} ∧ q.rate<1 := by
  have hc : ω∈closedDip (tuningCurve q):=hcontact.le
  have hi:=closedDip_interior_frequency _ hc
  obtain ⟨K,hK,hw⟩:=exists_window hi.1 hi.2 hgrid
  obtain ⟨S,hS,_,_⟩:=strict_symbol_of_nonperiodic_contact q 0 hK
    (by simpa only [shiftedCurve_zero,tuningCurve_apply] using hweak)
    (by simpa only [shiftedCurve_zero,tuningCurve_apply] using hcontact) hw.1 hw.2
  let T:=transportStrictSymbol (shiftedCurve_zero q) S
  have hT : T.symbol.lags={1,-(K:ℤ)}:=(transportStrictSymbol_lags _ S).trans hS
  exact ⟨K,hK,hw,T,hT,(rate_lt_one_iff_strictSymbol q).mpr ⟨T⟩⟩

theorem singleton_closedDip_boundary (q : Tuning) {ω : Frequency}
    (hc : closedDip (tuningCurve q)={ω}) :
    (∀η : Frequency,(η:ℝ)/2≤q.angle η) ∧ q.angle ω=(ω:ℝ)/2 ∧
      q∈frontier {p:Tuning | Regions.OmegaOne p} := by
  have hd : dip (tuningCurve q)=∅:=by
    have hh:=dip_empty_of_closedDip_singleton q 0 (by simpa only [shiftedCurve_zero] using hc)
    simpa only [shiftedCurve_zero] using hh
  have hw:=weak_phase_of_dip_empty q hd
  have hm : ω∈closedDip (tuningCurve q):=by rw [hc]; exact mem_singleton ω
  have he : q.angle ω=(ω:ℝ)/2:=le_antisymm hm (hw ω)
  have hi:=closedDip_interior_frequency _ hm
  refine ⟨hw,he,weak_contact_mem_frontier q ?_ ⟨hi.1,hi.2.le⟩ he⟩
  intro η hη
  exact hw ⟨η,hη.1.le,hη.2⟩

/-- The alternatives are exhaustive with a unique gap index; the singleton
alternative has a strict two-lag symbol, while the interior alternative is
exactly in the source gap and has nonempty relative interior. -/
theorem levelZero_complete (q : Tuning) :
    (closedDip (tuningCurve q)=∅ ∧ Regions.OmegaOne q ∧ q.rate<1) ∨
    (∃K : ℕ,∃hK : 3≤K,
      firstFrequency K (by omega)∈closedDip (tuningCurve q) ∧
      ProgramSolution (tuningCurve q) nonzeroLags
        (MeasureTheory.Measure.dirac (firstFrequency K (by omega))) ∧ 1≤q.rate) ∨
    (∃K : ℕ,2≤K ∧ (∀ω∈closedDip (tuningCurve q),InWindow K ω) ∧
      (∀L : ℕ,2≤L→(∀ω∈closedDip (tuningCurve q),InWindow L ω)→L=K) ∧
      ((∃ω : Frequency,closedDip (tuningCurve q)={ω} ∧
        q∈frontier {p:Tuning | Regions.OmegaOne p} ∧ q.rate<1) ∨
       (Gap K q ∧ (interior (closedDip (tuningCurve q))).Nonempty))) := by
  rcases levelZero_geometric_trichotomy q with he|hg|⟨hne,K,hK,hu⟩
  · exact Or.inl ⟨he,levelZero_empty_converges q he⟩
  · right; left
    obtain ⟨K,hK,hm⟩:=hg
    have hh:=levelZero_grid_atom q hK hm
    exact ⟨K,hK,hm,hh.2⟩
  · right; right
    refine ⟨K,hK.1,hK.2,fun L hL hwin=>hu L ⟨hL,hwin⟩,?_⟩
    by_cases hd : dip (tuningCurve q)=∅
    · left
      obtain ⟨ω,hω⟩:=closedDip_singleton_of_dip_empty q 0
        (by simpa only [shiftedCurve_zero] using hne) (by simpa only [shiftedCurve_zero] using hd)
      have hc : closedDip (tuningCurve q)={ω}:=by simpa only [shiftedCurve_zero] using hω
      obtain ⟨hw,he,hb⟩:=singleton_closedDip_boundary q hc
      have hn : ¬FP (tuningCurve q):=by
        obtain ⟨S,_,_,_⟩:=strict_symbol_of_nonperiodic_contact q 0 hK.1
          (by simpa only [shiftedCurve_zero,tuningCurve_apply] using hw)
          (by simpa only [shiftedCurve_zero,tuningCurve_apply] using he)
          (hK.2 ω (by rw [hc]; exact mem_singleton ω)).1
          (hK.2 ω (by rw [hc]; exact mem_singleton ω)).2
        simpa only [shiftedCurve_zero,FP] using S.not_fpOn
      exact ⟨ω,hc,hb,(rate_lt_one_iff_infeasible q).mpr hn⟩
    · right
      have hdp : (dip (tuningCurve q)).Nonempty:=Set.nonempty_iff_ne_empty.mpr hd
      refine ⟨gap_of_closedDip_window q hK.1 hdp hK.2,?_⟩
      simpa only [shiftedCurve_zero] using
        (show (interior (closedDip (shiftedCurve q 0))).Nonempty from by
          rw [interior_closedDip]
          simpa only [shiftedCurve_zero] using hdp)

/-- The exact boundary intersection with the divergence set: a boundary
point has rate at least one precisely at a first-harmonic contact. -/
theorem frontier_divergence_iff_phase_locked (q : Tuning)
    (hq : q∈frontier {p:Tuning | Regions.OmegaOne p}) :
    1≤q.rate ↔ ∃K : ℕ,∃_hK : 3≤K,q.angle (2*Real.pi/K)=Real.pi/K := by
  constructor
  · intro hr
    by_contra hn
    obtain ⟨hi,he,_⟩:=Regions.frontier_tangency_angle hq
    let ω:Frequency:=⟨Real.arccos (Regions.vertex q),hi.1.le,hi.2.le⟩
    have hw : ∀η : Frequency,(η:ℝ)/2≤q.angle η := by
      intro η
      by_cases hz : (η:ℝ)=0
      · rw [hz,q.angle_zero]
        linarith [Real.pi_pos]
      · exact Regions.weak_omegaOne_angle_ge q
          (Regions.closure_omegaOne_subset_weak (frontier_subset_closure hq))
          ⟨lt_of_le_of_ne η.property.1 (Ne.symm hz),η.property.2⟩
    have hgrid : ∀K : ℕ,∀hK : 3≤K,ω≠firstFrequency K (by omega) := by
      intro K hK heq
      apply hn
      refine ⟨K,hK,?_⟩
      have hc : q.angle ω=(ω:ℝ)/2:=he
      rw [heq] at hc
      change q.angle (2*Real.pi/K)=(2*Real.pi/K)/2 at hc
      convert hc using 1
      ring
    have heω : q.angle ω=(ω:ℝ)/2:=he
    obtain ⟨K,hK,hwin,S,hS,hlt⟩:=nonperiodic_tangency_certificate q (ω:=ω) hw heω hgrid
    exact (not_lt_of_ge hr) hlt
  · rintro ⟨K,hK,he⟩
    have hc : firstFrequency K (by omega)∈closedDip (tuningCurve q) := by
      change q.angle (2*Real.pi/K)≤(2*Real.pi/K)/2
      rw [he]
      exact le_of_eq (by ring)
    exact (levelZero_grid_atom q hK hc).2.2

theorem phase_locked_boundary_rate_eq_one (q : Tuning)
    (hq : q∈frontier {p:Tuning | Regions.OmegaOne p})
    (hlocked : ∃K : ℕ,∃_hK : 3≤K,q.angle (2*Real.pi/K)=Real.pi/K) : q.rate=1 :=
  le_antisymm (Regions.closure_omegaOne_rate_le_one q (frontier_subset_closure hq))
    ((frontier_divergence_iff_phase_locked q hq).mpr hlocked)

end polyak.Levels.Geometry
