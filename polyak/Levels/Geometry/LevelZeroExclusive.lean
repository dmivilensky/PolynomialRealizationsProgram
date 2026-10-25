import polyak.Levels.Geometry.LevelZeroFull

/-! The mutually exclusive, exhaustive source classification, with all
rate, boundary, tongue, atom and unique-window conclusions retained. -/
noncomputable section
namespace polyak.Levels.Geometry
open General Set

 theorem firstFrequency_not_in_window {K L : ℕ} (hK : 2≤K) (hL : 3≤L) :
    ¬InWindow K (firstFrequency L (by omega)) := by
  intro hw
  have hk : (0:ℝ)<K:=by positivity
  have hl : (0:ℝ)<L:=by positivity
  have hk1 : (0:ℝ)<(K:ℝ)+1:=by positivity
  change 2*Real.pi/((K:ℝ)+1)<2*Real.pi/L ∧ 2*Real.pi/L<2*Real.pi/K at hw
  have ha := (div_lt_div_iff₀ hk1 hl).mp hw.1
  have hb := (div_lt_div_iff₀ hl hk).mp hw.2
  have hKL : (K:ℝ)<L := by nlinarith [Real.pi_pos]
  have hLK : (L:ℝ)<K+1 := by nlinarith [Real.pi_pos]
  have hKL' : K<L:=by exact_mod_cast hKL
  have hLK' : L<K+1:=by exact_mod_cast hLK
  omega

inductive LevelZeroClass where
  | emptyDip
  | periodic
  | window
  deriving DecidableEq

/-- The phase-locked boundary points of Theorem A(iii). -/
def PhaseLockedContact (q : Tuning) : Prop :=
  ∃K : ℕ,∃_hK : 3≤K,q.angle (2*Real.pi/K)=Real.pi/K

/-- The three complete alternatives of the article's level-zero theorem.
The window alternative also records which of its two subcases holds. -/
def LevelZeroAlternative (q : Tuning) : LevelZeroClass→Prop
  | .emptyDip => closedDip (tuningCurve q)=∅ ∧ Regions.OmegaOne q ∧ q.rate<1
  | .periodic => ∃K : ℕ,∃hK : 3≤K,
      firstFrequency K (by omega)∈closedDip (tuningCurve q) ∧
      q.angle (2*Real.pi/K)≤Real.pi/K ∧
      ProgramSolution (tuningCurve q) nonzeroLags
        (MeasureTheory.Measure.dirac (firstFrequency K (by omega))) ∧ 1≤q.rate
  | .window => ∃K : ℕ,2≤K ∧
      (∀ω∈closedDip (tuningCurve q),InWindow K ω) ∧
      (∀L : ℕ,2≤L→(∀ω∈closedDip (tuningCurve q),InWindow L ω)→L=K) ∧
      ((∃ω : Frequency,closedDip (tuningCurve q)={ω} ∧
        q∈frontier {p:Tuning | Regions.OmegaOne p} ∧
        ¬PhaseLockedContact q ∧ q.rate<1) ∨
       (Gap K q ∧ (interior (closedDip (tuningCurve q))).Nonempty))

 theorem singleton_window_not_phase_locked (q : Tuning)
    (hfront : q∈frontier {p:Tuning | Regions.OmegaOne p}) (hrate : q.rate<1) :
    ¬PhaseLockedContact q := by
  intro hlocked
  have hr:=(frontier_divergence_iff_phase_locked q hfront).mpr hlocked
  exact (not_lt_of_ge hr) hrate

 theorem LevelZeroAlternative.closedDip_nonempty {q : Tuning} {c : LevelZeroClass}
    (h : LevelZeroAlternative q c) (hc : c≠.emptyDip) :
    (closedDip (tuningCurve q)).Nonempty := by
  cases c with
  | emptyDip => exact False.elim (hc rfl)
  | periodic => obtain ⟨K,hK,hm,_⟩:=h; exact ⟨_,hm⟩
  | window =>
    obtain ⟨K,hK,hw,hu,hs⟩:=h
    rcases hs with ⟨ω,hω,_⟩|⟨_,hi⟩
    · rw [hω]; exact singleton_nonempty _
    · exact hi.mono interior_subset

 theorem LevelZeroAlternative.unique {q : Tuning} {i j : LevelZeroClass}
    (hi : LevelZeroAlternative q i) (hj : LevelZeroAlternative q j) : i=j := by
  have hempty : ∀{c : LevelZeroClass},LevelZeroAlternative q .emptyDip→
      LevelZeroAlternative q c→c=.emptyDip := by
    intro c he hc
    by_contra hn
    have hne:=hc.closedDip_nonempty hn
    rw [he.1] at hne
    exact Set.not_nonempty_empty hne
  have hperiodic : ¬(LevelZeroAlternative q .periodic ∧ LevelZeroAlternative q .window) := by
    rintro ⟨⟨L,hL,hm,_⟩,K,hK,hw,_⟩
    exact firstFrequency_not_in_window hK hL (hw _ hm)
  cases i <;> cases j
  · rfl
  · exact (hempty hi hj).symm
  · exact (hempty hi hj).symm
  · exact hempty hj hi
  · rfl
  · exact False.elim (hperiodic ⟨hi,hj⟩)
  · exact hempty hj hi
  · exact False.elim (hperiodic ⟨hj,hi⟩)
  · rfl

/-- Exactly one of the full three source alternatives holds. The periodic
case includes the literal closed-tongue inequality and actual Dirac
solution; the nonperiodic point case is on the actual relative frontier
and is explicitly not phase-locked. -/
theorem levelZero_exactly_one (q : Tuning) :
    ∃!c : LevelZeroClass,LevelZeroAlternative q c := by
  have hex : ∃c : LevelZeroClass,LevelZeroAlternative q c := by
    rcases levelZero_complete q with he|hp|hw
    · exact ⟨.emptyDip,he⟩
    · obtain ⟨K,hK,hm,hsol,hrate⟩:=hp
      exact ⟨.periodic,K,hK,hm,(levelZero_grid_atom q hK hm).1,hsol,hrate⟩
    · obtain ⟨K,hK,hwin,hunique,hs⟩:=hw
      refine ⟨.window,K,hK,hwin,hunique,?_⟩
      rcases hs with ⟨ω,hω,hfront,hrate⟩|hgap
      · exact Or.inl ⟨ω,hω,hfront,singleton_window_not_phase_locked q hfront hrate,hrate⟩
      · exact Or.inr hgap
  obtain ⟨c,hc⟩:=hex
  exact ⟨c,hc,fun d hd=>LevelZeroAlternative.unique hd hc⟩

/-- The singleton and interior window subcases are mutually exclusive. -/
theorem point_window_not_gap (q : Tuning) {K : ℕ} {ω : Frequency}
    (hc : closedDip (tuningCurve q)={ω}) : ¬Gap K q := by
  intro hg
  have hd : dip (tuningCurve q)=∅ := by
    simpa only [shiftedCurve_zero] using dip_empty_of_closedDip_singleton q 0
      (by simpa only [shiftedCurve_zero] using hc)
  have hne:=hg.2.1
  rw [hd] at hne
  exact Set.not_nonempty_empty hne

/-- The literal feasibility-set version of the boundary conclusion in
Theorem tangency; no replacement of D by a rate predicate is needed. -/
theorem frontier_fp_iff_phase_locked (q : Tuning)
    (hfront : q∈frontier {p:Tuning | Regions.OmegaOne p}) :
    FP (tuningCurve q) ↔ PhaseLockedContact q := by
  constructor
  · intro hfp
    exact (frontier_divergence_iff_phase_locked q hfront).mp (fp_one_le_rate q hfp)
  · intro hlocked
    by_contra hn
    have hrate:=(rate_lt_one_iff_infeasible q).mpr hn
    have hr:=(frontier_divergence_iff_phase_locked q hfront).mpr hlocked
    exact (not_lt_of_ge hr) hrate

theorem frontier_inter_feasible_eq_phase_locked :
    {q : Tuning | q∈frontier {p:Tuning | Regions.OmegaOne p} ∧ FP (tuningCurve q)}=
    {q : Tuning | q∈frontier {p:Tuning | Regions.OmegaOne p} ∧ PhaseLockedContact q} := by
  ext q
  exact and_congr_right (fun hfront=>frontier_fp_iff_phase_locked q hfront)

end polyak.Levels.Geometry
