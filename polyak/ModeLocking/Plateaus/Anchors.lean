import polyak.ModeLocking.Plateaus.Definitions
import polyak.ModeLocking.TwoLag.ExactBoundary

/-! The unique-window-atom conclusion concerns actual positive atom
masses of every extremal, not merely points in a plotted support. -/
noncomputable section
namespace polyak.ModeLocking.Plateaus
open General Levels Geometry MeasureTheory Set Filter

theorem unique_anchor_of_finite_carrier {q : Tuning} {K : ℕ}
    (hgap : Gap K q) {w : Measure Frequency}
    (hw : ProgramSolution (tuningCurve q) nonzeroLags w)
    {S : Set Frequency} (hS : S.Finite) (hcar : ∀ᵐω∂w,ω∈S) {star : Frequency}
    (honly : ∀ω∈S,InWindow K ω→ω=star) :
    ∀ω : Frequency,Farey.Anchor q w ω ↔ ω=star := by
  have hforward (ω : Frequency) (hω : Farey.Anchor q w ω) : ω=star :=
    honly ω (atom_mem_of_carried hcar hω.1) (Farey.gap_closedDip_window hgap ω hω.2)
  have hp := full_solution_closedDip_mass_pos hw
  have he : w (closedDip (tuningCurve q))=w (S∩closedDip (tuningCurve q)) := by
    apply measure_congr
    filter_upwards [hcar] with ω hω
    simp only [mem_inter_iff,hω,true_and]
  rw [he] at hp
  obtain ⟨v,hv,hpos⟩ := Farey.finite_positive_mass_has_atom (hS.inter_of_left _) hp
  have hstar : Farey.Anchor q w star := by
    have ha : Farey.Anchor q w v := ⟨hpos,hv.2⟩
    rwa [←hforward v ha]
  intro ω
  exact ⟨hforward ω,fun heq=>heq ▸ hstar⟩

/-- Applied at an exact point this already proves the anchor statement for
all actual full-program extremals; the same finite-carrier lemma applies
at every point of its plateau. -/
theorem exact_unique_anchor {q : Tuning} {K L : ℕ} (D : TwoLag.ExactData q 0 K L)
    (hwin : InWindow K (D.u 0)) (hbelow : (D.u 1 : ℝ)<2*Real.pi/((K : ℝ)+1))
    {w : Measure Frequency} (hw : ProgramSolution (tuningCurve q) nonzeroLags w) :
    ∀ω : Frequency,Farey.Anchor q w ω ↔ ω=D.u 0 := by
  obtain ⟨R,hS,hN⟩ := D.exists_regularData
  have hsol : ProgramSolution (Geometry.shiftedCurve q 0) nonzeroLags w := by
    simpa only [Geometry.shiftedCurve_zero] using hw
  have hcar := R.program_carried (N':=nonzeroLags) (fun n hn=>R.lags_nonzero n hn) hsol
  have hc : ∀ᵐω∂w,ω∈({frequencyZero}∪Set.range D.u : Set Frequency) := by
    filter_upwards [hcar] with ω hω
    rcases hω with rfl|⟨i,rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (hS ▸ ⟨i,rfl⟩)
  apply unique_anchor_of_finite_carrier (D.gap_of_first_contact_window hwin) hw
    ((finite_singleton frequencyZero).union (finite_range D.u)) hc
  intro ω hω hωwin
  rcases hω with h0|⟨i,rfl⟩
  · have heq : ω=frequencyZero := h0
    rw [heq] at hωwin
    have hlow := hωwin.1
    change 2*Real.pi/((K : ℝ)+1)<0 at hlow
    have hpos : 0<2*Real.pi/((K : ℝ)+1) := by positivity
    linarith
  · fin_cases i
    · rfl
    · have hlow := hωwin.1
      change 2*Real.pi/((K : ℝ)+1)<(D.u 1 : ℝ) at hlow
      linarith

end polyak.ModeLocking.Plateaus
