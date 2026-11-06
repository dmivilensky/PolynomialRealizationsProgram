import nesterov.Momentum.QHM
import nesterov.Momentum.Queries
import nesterov.Stationary.Execution

/-!
Article: Remark two-step methods and the usual QHM initialization in cor:B and cor:QHM.
Use: literal actual QHM iterates with d₋₁=0 have exactly the translated method's
finite-horizon query suprema and asymptotic distance factor.
-/

noncomputable section
namespace nesterov.Momentum
open Set Filter
open scoped Topology

/-- A genuine finite-dimensional objective and start, independent of either
trajectory representation. No recurrence is supplied as an assumption. -/
structure QHMInstance (μ L : ℝ) where
  Carrier : Type
  [normed : NormedAddCommGroup Carrier]
  [inner : InnerProductSpace ℝ Carrier]
  [complete : CompleteSpace Carrier]
  [finite : FiniteDimensional ℝ Carrier]
  f : Carrier → ℝ
  admissible : polyak.CenteredSmoothStronglyConvex μ L f
  initial : Carrier

attribute [instance] QHMInstance.normed QHMInstance.inner QHMInstance.complete QHMInstance.finite

/-- Ratios of actual QHM iterates with the usual zero accumulator. -/
def qhmRatios (α β ν μ L : ℝ) (n : ℕ) : Set ℝ :=
  {x | ∃ r : QHMInstance μ L, r.initial ≠ 0 ∧
    x = ‖qhmIterate (gradient r.f) α β ν r.initial n‖ / ‖r.initial‖}

def qhmEnvelope (α β ν μ L : ℝ) (n : ℕ) : ℝ := sSup (insert 0 (qhmRatios α β ν μ L n))

def qhmRate (α β ν μ L : ℝ) : ℝ :=
  limsup (fun n : ℕ => qhmEnvelope α β ν μ L n ^ ((n : ℝ)⁻¹)) atTop

/-- Query readout of every actual rest trajectory agrees with the computed
momentum executor, for arbitrary objectives and every horizon. -/
theorem fromRest_query_eq_queryIterate {β τ h μ L : ℝ} (hh : h ≠ 0)
    (r : Rates.HilbertRun (method β τ h hh) μ L) (hr : r.FromRest) (n : ℕ) :
    (method β τ h hh).query r.w n = queryIterate (gradient r.f) β τ h (r.w 0) n := by
  have he : r.w = history (gradient r.f) β τ h (r.w 0) (r.w 0) := by
    apply StationaryMethod.IsTrajectory.unique (method β τ h hh) r.trajectory
      (history_isTrajectory _ β τ h hh _ _)
    intro j
    rw [hr j]
    fin_cases j <;> rfl
  rw [he, method_query_history]
  rfl

/-- Exact equality of the actual ratio sets, retaining finite dimension and
the original curvature constants. -/
theorem qhmRatios_eq_queryRestRatios (α β ν μ L : ℝ) (hβ : β ≠ 1)
    (hh : α * (1-β) ≠ 0) (n : ℕ) :
    qhmRatios α β ν μ L n =
      queryRestRatios β (qhmExtrapolation β ν) (α*(1-β)) hh μ L n := by
  ext x
  constructor
  · rintro ⟨i, hi, hx⟩
    let r : Rates.HilbertRun (method β (qhmExtrapolation β ν) (α*(1-β)) hh) μ L :=
      ⟨i.Carrier, i.f, i.admissible,
        history (gradient i.f) β (qhmExtrapolation β ν) (α*(1-β)) i.initial i.initial,
        history_isTrajectory _ β (qhmExtrapolation β ν) (α*(1-β)) hh _ _⟩
    have hr : r.FromRest := by
      intro j
      fin_cases j <;> rfl
    refine ⟨r, inferInstance, hr, hi, ?_⟩
    rw [fromRest_query_eq_queryIterate hh r hr]
    change x = ‖queryIterate (gradient i.f) β (qhmExtrapolation β ν) (α*(1-β)) i.initial n‖ / ‖i.initial‖
    rwa [← qhmIterate_eq_queries (gradient i.f) α β ν hβ] 
  · rintro ⟨r, hfd, hr, hz, hx⟩
    let _ : FiniteDimensional ℝ r.Carrier := hfd
    let i : QHMInstance μ L := ⟨r.Carrier, r.f, r.admissible, r.w 0⟩
    refine ⟨i, hz, ?_⟩
    change x = ‖qhmIterate (gradient r.f) α β ν (r.w 0) n‖ / ‖r.w 0‖
    rw [qhmIterate_eq_queries (gradient r.f) α β ν hβ,
      ← fromRest_query_eq_queryIterate hh r hr]
    exact hx

/-- The supremum-before-limit convention is preserved exactly at every horizon. -/
theorem qhmEnvelope_eq_queryRestEnvelope (α β ν μ L : ℝ) (hβ : β ≠ 1)
    (hh : α * (1-β) ≠ 0) (n : ℕ) :
    qhmEnvelope α β ν μ L n =
      queryRestEnvelope β (qhmExtrapolation β ν) (α*(1-β)) hh μ L n := by
  unfold qhmEnvelope queryRestEnvelope
  rw [qhmRatios_eq_queryRestRatios α β ν μ L hβ hh n]

theorem qhmRatios_bddAbove (α β ν μ L : ℝ) (hβ : β ≠ 1)
    (hh : α * (1-β) ≠ 0) (n : ℕ) : BddAbove (insert 0 (qhmRatios α β ν μ L n)) := by
  rw [qhmRatios_eq_queryRestRatios α β ν μ L hβ hh n]
  exact queryRestRatios_bddAbove _ _ _ _ _ _ _

theorem qhmEnvelope_nonneg (α β ν μ L : ℝ) (hβ : β ≠ 1)
    (hh : α * (1-β) ≠ 0) (n : ℕ) : 0 ≤ qhmEnvelope α β ν μ L n := by
  rw [qhmEnvelope_eq_queryRestEnvelope α β ν μ L hβ hh n]
  exact queryRestEnvelope_nonneg _ _ _ _ _ _ _

/-- The distance factor of the actual initialized QHM implementation is the
translated method's literal from-rest query factor. -/
theorem qhmRate_eq_queryRestRate (α β ν μ L : ℝ) (hβ : β ≠ 1)
    (hh : α * (1-β) ≠ 0) :
    qhmRate α β ν μ L = queryRestRate β (qhmExtrapolation β ν) (α*(1-β)) hh μ L := by
  unfold qhmRate queryRestRate
  simp only [qhmEnvelope_eq_queryRestEnvelope α β ν μ L hβ hh]

end nesterov.Momentum
