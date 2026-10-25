import polyak.General.Regions.Explicit
import polyak.General.Regions.QuadraticLower
import polyak.General.Multipliers.CubicBridge
import polyak.General.Multipliers.NearOne
import polyak.General.Multipliers.Pole

/-! Article: Theorem B(a,b), the actual interval of admissible radii and its
infimum. Infima use a nonempty, bounded-below set; the boundary cubic is a
continuous limit and is never an assumed numerical test. -/
namespace polyak.General.Regions
noncomputable section
open Set

/-- The exact set R in Theorem B(a). -/
def admissibleRadii (q : Tuning) : Set ℝ :=
  {r | q.rhoB<r ∧ r<1 ∧ ∀ c∈Icc (-1:ℝ) 1,0≤q.H r c}

/-- The source radius r1. -/
def rOne (q : Tuning) : ℝ := sInf (admissibleRadii q)

theorem admissibleRadii_bddBelow (q : Tuning) : BddBelow (admissibleRadii q) :=
  ⟨0,fun _ hr=>(rootRadius_nonneg _ _).trans hr.1.le⟩

/-- Near the unit circle there is a nonempty interval of admissible radii. -/
theorem admissibleRadii_nonempty (q : Tuning) (hq : OmegaOne q) :
    (admissibleRadii q).Nonempty := by
  obtain ⟨η,hη,hpos⟩ := Multipliers.exists_positive_inner_band q hq
  let l := max q.rhoB (1-η)
  let r := (l+1)/2
  have hl : l<1 := max_lt ((le_max_right _ _).trans_lt q.rhoQ_lt_one) (by linarith)
  have hr : q.rhoB<r := by have := le_max_left q.rhoB (1-η); dsimp [r,l] at *; linarith
  have hr1 : r<1 := by dsimp [r]; linarith
  refine ⟨r,hr,hr1,fun c hc=>(hpos r c ?_ hr1 hc).le⟩
  have := le_max_right q.rhoB (1-η)
  dsimp [r,l] at *
  linarith

/-- The interval is upward closed below its right endpoint 1. -/
theorem admissibleRadii_upward (q : Tuning) (hq : OmegaOne q) {r s : ℝ}
    (hr : r∈admissibleRadii q) (hrs : r≤s) (hs : s<1) : s∈admissibleRadii q :=
  ⟨hr.1.trans_le hrs,hs,Multipliers.source_radius_monotone q
    (fun c hc=>(hq c hc).le) hr.1 hrs hs hr.2.2⟩

/-- The nonempty admissible set is an interval in the order-theoretic sense. -/
theorem admissibleRadii_ordConnected (q : Tuning) (hq : OmegaOne q) :
    (admissibleRadii q).OrdConnected := by
  rw [ordConnected_iff]
  intro r hr s hs _ u hu
  exact admissibleRadii_upward q hq hr hu.1 (hu.2.trans_lt hs.2.1)

/-- Every point below 1 lies below some admissible radius. -/
theorem exists_admissible_gt (q : Tuning) (hq : OmegaOne q) {s : ℝ} (hs : s<1) :
    ∃ r∈admissibleRadii q,s<r := by
  obtain ⟨r,hr⟩ := admissibleRadii_nonempty q hq
  let u := (max r s+1)/2
  have hm : max r s<1 := max_lt hr.2.1 hs
  have hru : r≤u := by have := le_max_left r s; dsimp [u]; linarith
  refine ⟨u,admissibleRadii_upward q hq hr hru ?_,?_⟩
  · dsimp [u]; linarith
  · have := le_max_right r s; dsimp [u]; linarith

/-- Thus 1 is the right endpoint, with the source open-endpoint convention. -/
theorem admissibleRadii_isLUB_one (q : Tuning) (hq : OmegaOne q) :
    IsLUB (admissibleRadii q) 1 := by
  constructor
  · intro r hr; exact hr.2.1.le
  · intro s hs
    by_contra hh
    obtain ⟨r,hr,hsr⟩ := exists_admissible_gt q hq (lt_of_not_ge hh)
    exact (not_lt_of_ge (hs hr)) hsr

/-- The infimum is strictly below one and nonnegative. -/
theorem rOne_bounds (q : Tuning) (hq : OmegaOne q) : 0≤rOne q ∧ rOne q<1 := by
  obtain ⟨r,hr⟩ := admissibleRadii_nonempty q hq
  exact ⟨le_csInf ⟨r,hr⟩ (fun _ hs=>(rootRadius_nonneg _ _).trans hs.1.le),
    (csInf_le (admissibleRadii_bddBelow q) hr).trans_lt hr.2.1⟩

/-- The cubic at r1 is obtained from genuine admissible radii by continuity. -/
theorem cubic_nonnegative_at_infimum (q : Tuning) (hq : OmegaOne q) :
    ∀ c∈Icc (-1:ℝ) 1,0≤q.H (rOne q) c := by
  intro c hc
  have hclosed : IsClosed {r : ℝ | 0≤q.H r c} :=
    isClosed_le continuous_const (by unfold Tuning.H; fun_prop)
  have hs : closure (admissibleRadii q) ⊆ {r : ℝ | 0≤q.H r c} :=
    hclosed.closure_subset_iff.mpr (fun _ hr=>hr.2.2 c hc)
  exact hs (csInf_mem_closure (admissibleRadii_nonempty q hq) (admissibleRadii_bddBelow q))

/-- Theorem B(a): the exact original rate lies between rhoQ and r1<1. -/
theorem original_rate_bounds (q : Tuning) (hq : OmegaOne q) :
    q.rhoQ≤q.rate ∧ q.rate≤rOne q ∧ rOne q<1 := by
  refine ⟨rhoQ_le_rate q,?_,(rOne_bounds q hq).2⟩
  apply le_csInf (admissibleRadii_nonempty q hq)
  intro r hr
  exact Multipliers.source_rate_le_radius q hq hr.1 hr.2.1 hr.2.2

/-- The forward endpoint test in B(b), including equal endpoint radii. -/
theorem cubic_nonnegative_of_rOne_eq_rhoQ (q : Tuning) (hq : OmegaOne q)
    (he : rOne q=q.rhoQ) : ∀ c∈Icc (-1:ℝ) 1,0≤q.H q.rhoQ c := by
  rw [← he]
  exact cubic_nonnegative_at_infimum q hq

/-- The nonsingular branch of the converse includes every rhoA>rhoB tuning. -/
theorem rOne_eq_rhoQ_of_cubic_nonsingular (q : Tuning) (hq : OmegaOne q)
    (hr : q.rhoB<q.rhoQ) (hH : ∀ c∈Icc (-1:ℝ) 1,0≤q.H q.rhoQ c) :
    rOne q=q.rhoQ := by
  apply le_antisymm
  · exact csInf_le (admissibleRadii_bddBelow q) ⟨hr,q.rhoQ_lt_one,hH⟩
  · exact (original_rate_bounds q hq).1.trans (original_rate_bounds q hq).2.1

/-- Theorem B(b), including the singular negative root and equal endpoint radii. -/
theorem rOne_eq_rhoQ_iff (q : Tuning) (hq : OmegaOne q)
    (hover : Real.sqrt q.beta<q.rhoQ) :
    rOne q=q.rhoQ ↔ ∀ c∈Icc (-1:ℝ) 1,0≤q.H q.rhoQ c := by
  refine ⟨cubic_nonnegative_of_rOne_eq_rhoQ q hq,?_⟩
  intro hH
  by_cases hab : q.rhoB<q.rhoA
  · apply rOne_eq_rhoQ_of_cubic_nonsingular q hq ?_ hH
    change q.rhoB<max q.rhoA q.rhoB
    exact lt_max_iff.mpr (Or.inl hab)
  · have hab' : q.rhoA≤q.rhoB := le_of_not_gt hab
    have he : q.rhoQ=q.rhoB := max_eq_right hab'
    apply le_antisymm
    · by_contra hnot
      have hlt : q.rhoQ<rOne q := lt_of_not_ge hnot
      let r := (q.rhoQ+rOne q)/2
      have hr : q.rhoB<r := by dsimp [r]; rw [← he]; linarith
      have hr1 : r<1 := by dsimp [r]; linarith [(rOne_bounds q hq).2]
      have hh : r∈admissibleRadii q := ⟨hr,hr1,
        Multipliers.source_pole_radii q hover hab' (fun c hc=>(hq c hc).le)
          (by simpa only [he] using hH) hr hr1⟩
      have hi := csInf_le (admissibleRadii_bddBelow q) hh
      change rOne q≤r at hi
      dsimp [r] at hi
      linarith
    · exact (original_rate_bounds q hq).1.trans (original_rate_bounds q hq).2.1

/-- On the exact quadratic regime, the original nonlinear and quadratic rates coincide. -/
theorem original_rate_eq_quadratic_of_cubic (q : Tuning) (hq : OmegaOne q)
    (hover : Real.sqrt q.beta<q.rhoQ)
    (hH : ∀ c∈Icc (-1:ℝ) 1,0≤q.H q.rhoQ c) : q.rate=q.rhoQ := by
  have he := (rOne_eq_rhoQ_iff q hq hover).mpr hH
  exact le_antisymm (he ▸ (original_rate_bounds q hq).2.1) (rhoQ_le_rate q)

end
end polyak.General.Regions
