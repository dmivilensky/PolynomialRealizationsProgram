import polyak.ModeLocking.Boundary.RationalCarrier
import polyak.ModeLocking.Plateaus.Definitions
import polyak.ModeLocking.Periods.Least

/-! The complete source classification: kappa comparison, threshold sign,
finite witnesses, rates, and the disjoint three boundary regimes. -/
noncomputable section
namespace polyak.ModeLocking
open General Levels MeasureTheory Set

theorem regular_boundary_periodic {K : ℕ} {q : Tuning} (hq : q∈BoundaryInGap K)
    (hreg : q∈Plateaus.regularTunings) : PeriodicBoundary q := by
  obtain ⟨L,⟨D⟩⟩ := hreg
  refine ⟨L,D.period_ge,?_⟩
  simpa only [boundary_sigma_zero hq] using D.sigmaPeriodic_eq

theorem boundary_regime_trichotomy {K : ℕ} {q : Tuning} (hq : q∈BoundaryInGap K) :
    (q∈Plateaus.regularTunings ∧ PeriodicBoundary q) ∨
      (PeriodicBoundary q ∧ q∉Plateaus.regularTunings) ∨ ¬PeriodicBoundary q := by
  classical
  by_cases hr : q∈Plateaus.regularTunings
  · exact Or.inl ⟨hr,regular_boundary_periodic hq hr⟩
  · by_cases hp : PeriodicBoundary q
    · exact Or.inr (Or.inl ⟨hp,hr⟩)
    · exact Or.inr (Or.inr hp)

def BelowBoundaryCase (q : Tuning) : Prop :=
  (q.kappa:EReal)<(Global.Threshold.kappaBoundary (Global.Threshold.parameters q)).val ∧
    0<Threshold.sigma q ∧ Nonempty (StrictSymbol (tuningCurve q) nonzeroLags) ∧ q.rate<1

def AboveBoundaryCase (q : Tuning) : Prop :=
  (Global.Threshold.kappaBoundary (Global.Threshold.parameters q)).val<(q.kappa:EReal) ∧
    Threshold.sigma q<0 ∧ ∃ L : ℕ, 3≤L ∧
      (∀ m : ℕ, 1≤m → PeriodicFP (tuningCurve q) (m*L)) ∧ 1≤q.rate

def OnBoundaryCase (K : ℕ) (q : Tuning) : Prop :=
  (Global.Threshold.kappaBoundary (Global.Threshold.parameters q)).val=(q.kappa:EReal) ∧
    q∈BoundaryInGap K ∧ Threshold.sigma q=0 ∧ 1≤q.rate ∧
      ((q∈Plateaus.regularTunings ∧ PeriodicBoundary q) ∨
        (PeriodicBoundary q ∧ q∉Plateaus.regularTunings) ∨ ¬PeriodicBoundary q)

theorem belowBoundaryCase_iff (q : Tuning) : BelowBoundaryCase q ↔ 0<Threshold.sigma q := by
  constructor
  · exact fun h => h.2.1
  · intro hs
    obtain ⟨hcert,hrate⟩ := convergence_finite_witness q hs
    exact ⟨(below_boundary_iff_sigma_pos q).mpr hs,hs,hcert,hrate⟩

theorem aboveBoundaryCase_iff (q : Tuning) : AboveBoundaryCase q ↔ Threshold.sigma q<0 := by
  constructor
  · exact fun h => h.2.1
  · intro hs
    exact ⟨(above_boundary_iff_sigma_neg q).mpr hs,hs,divergence_finite_witness q hs⟩

theorem onBoundaryCase_iff {K : ℕ} {q : Tuning} (hq : Geometry.Gap K q) :
    OnBoundaryCase K q ↔ Threshold.sigma q=0 := by
  constructor
  · exact fun h => h.2.2.1
  · intro hs
    have hb := (boundaryInGap_iff K q).mpr ⟨hq,hs⟩
    exact ⟨(on_boundary_iff_sigma_zero q).mpr hs,hb,hs,boundary_rate hb,boundary_regime_trichotomy hb⟩

/-- Every gap tuning satisfies one of the three fully populated source cases. -/
theorem gap_classification {K : ℕ} {q : Tuning} (hq : Geometry.Gap K q) :
    BelowBoundaryCase q ∨ AboveBoundaryCase q ∨ OnBoundaryCase K q := by
  rcases lt_trichotomy (Threshold.sigma q) 0 with hs | hs | hs
  · exact Or.inr (Or.inl ((aboveBoundaryCase_iff q).mpr hs))
  · exact Or.inr (Or.inr ((onBoundaryCase_iff hq).mpr hs))
  · exact Or.inl ((belowBoundaryCase_iff q).mpr hs)

theorem gap_classification_disjoint {K : ℕ} {q : Tuning} :
    (¬(BelowBoundaryCase q ∧ AboveBoundaryCase q)) ∧
      (¬(BelowBoundaryCase q ∧ OnBoundaryCase K q)) ∧
      (¬(AboveBoundaryCase q ∧ OnBoundaryCase K q)) := by
  constructor
  · rintro ⟨hb,ha⟩
    have h1 := hb.2.1
    have h2 := ha.2.1
    linarith
  constructor
  · rintro ⟨hb,ho⟩
    have h1 := hb.2.1
    have h2 := ho.2.2.1
    linarith
  · rintro ⟨ha,ho⟩
    have h1 := ha.2.1
    have h2 := ho.2.2.1
    linarith

theorem boundary_regimes_disjoint {K : ℕ} {q : Tuning} (hq : q∈BoundaryInGap K) :
    (¬(q∈Plateaus.regularTunings ∧ (PeriodicBoundary q ∧ q∉Plateaus.regularTunings))) ∧
      (¬(q∈Plateaus.regularTunings ∧ ¬PeriodicBoundary q)) ∧
      (¬((PeriodicBoundary q ∧ q∉Plateaus.regularTunings) ∧ ¬PeriodicBoundary q)) := by
  exact ⟨fun h => h.2.2 h.1,fun h => h.2 (regular_boundary_periodic hq h.1),fun h => h.2 h.1.1⟩

/-- The anchor assertion holds for every feasible periodic measure in a gap,
including all finite witnesses and every boundary periodic extremal. -/
theorem gap_classification_anchor {K L : ℕ} {q : Tuning} (hq : Geometry.Gap K q)
    (hL : 0<L) {w : Measure Frequency}
    (hw : ProgramSolution (tuningCurve q) nonzeroLags w)
    (hcar : ∀ᵐω∂w,ω∈periodicGrid L) :
    ∃ (ω : Frequency) (j k : ℕ),Farey.Anchor q w ω ∧ 1≤j ∧ 2*j<k ∧ j.Coprime k ∧ k∣L ∧
      (ω:ℝ)=2*Real.pi*j/k ∧ (1/((K:ℝ)+1)<(j:ℝ)/k ∧ (j:ℝ)/k<1/(K:ℝ)) ∧
      2*K+1≤k := by
  obtain ⟨ω,j,k,hanchor,hj,hhalf,hcop,hdiv,hfreq,hwin,hden,_rest⟩ := Farey.farey_localization hq hL hw hcar
  exact ⟨ω,j,k,hanchor,hj,hhalf,hcop,hdiv,hfreq,hwin,hden⟩

end polyak.ModeLocking
