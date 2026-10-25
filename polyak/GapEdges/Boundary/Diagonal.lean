import polyak.GapEdges.Boundary.Topology
import polyak.Levels.Chart.DiagonalFace
import polyak.Levels.Chart.GapClosure
import polyak.Levels.Realization.ThresholdSets

/-! Positivity at every nonlocked lag-one boundary point and throughout
an actual open neighborhood of every interior point of a diagonal face. -/
noncomputable section
namespace polyak.GapEdges
open General Levels Set Filter
open scoped Topology

theorem sigma_pos_iff_rate_lt_one (q : Tuning) :
    0 < Threshold.sigma q ↔ q.rate < 1 := by
  rw [rate_lt_one_iff_infeasible, Threshold.fp_iff_sigma_nonpos, not_le]

theorem sigma_pos_of_nonlocked_frontier (q : Tuning)
    (hq : q ∈ frontier {p : Tuning | Regions.OmegaOne p})
    (hn : ¬Geometry.PhaseLockedContact q) : 0 < Threshold.sigma q := by
  rw [sigma_pos_iff_rate_lt_one, ← not_le]
  exact fun hr => hn ((Geometry.frontier_divergence_iff_phase_locked q hq).mp hr)

theorem nonlocked_frontier_neighborhood (q : Tuning)
    (hq : q ∈ frontier {p : Tuning | Regions.OmegaOne p})
    (hn : ¬Geometry.PhaseLockedContact q) :
    ∃ V : Set Tuning, IsOpen V ∧ q ∈ V ∧ V ∩ Regions.divergenceSet = ∅ := by
  refine ⟨{p | 0 < Threshold.sigma p},
    isOpen_lt continuous_const Global.Threshold.continuous_sigma,
    sigma_pos_of_nonlocked_frontier q hq hn, ?_⟩
  apply eq_empty_iff_forall_notMem.mpr
  intro p hp
  exact (not_le_of_gt hp.1) ((divergenceSet_iff_sigma_nonpos p).mp hp.2)

def positiveCoefficientSet : Set Chart.Coefficients :=
  Subtype.val '' {C : Chart.CoefficientPoint | 0 < Threshold.sigma (Chart.inverseTuning C)}

theorem positiveCoefficientSet_isOpen : IsOpen positiveCoefficientSet :=
  Chart.isOpen_coeffDomain.isOpenMap_subtype_val _
    (isOpen_lt continuous_const
      (Global.Threshold.continuous_sigma.comp Chart.continuous_inverseTuning))

def positiveRootSet : Set Chart.ParameterSpace :=
  {p | Chart.gapPolynomial p.1 p.2.1 p.2.2 ∈ positiveCoefficientSet}

theorem positiveRootSet_isOpen : IsOpen positiveRootSet :=
  positiveCoefficientSet_isOpen.preimage Chart.continuous_gapPolynomial

theorem positive_of_mem_positiveRootSet {p : Chart.ParameterSpace}
    (hp : p ∈ positiveRootSet) (q : Tuning)
    (he : Chart.coefficients q = Chart.gapPolynomial p.1 p.2.1 p.2.2) :
    0 < Threshold.sigma q := by
  obtain ⟨C, hC, heC⟩ := hp
  have hb : 0 < q.beta := (Chart.coefficient_quadratic_neg_iff q).mp (by
    rw [he, ← heC]
    exact C.property.1)
  have hq : Chart.inverseTuning C = q := Chart.coefficients_injective
    (Chart.inverseBeta_pos C) hb ((Chart.coefficients_inverseTuning C).trans (heC.trans he.symm))
  change 0 < Threshold.sigma (Chart.inverseTuning C) at hC
  rwa [hq] at hC

theorem diagonal_mem_positiveRootSet {K : ℕ} (hK : 2 ≤ K) {a r : ℝ}
    (hl : Chart.boundaryCosine K < r) (hu : r < Chart.boundaryCosine (K + 1))
    (ha : Chart.amplitudeFloor r r < a) : (a, r, r) ∈ positiveRootSet := by
  have hr : r ∈ Ioo (-1 : ℝ) 1 :=
    ⟨(Chart.boundaryCosine_ge_neg_one K).trans_lt hl,
      hu.trans (Chart.boundaryCosine_succ_lt_one hK)⟩
  let C : Chart.CoefficientPoint :=
    ⟨Chart.gapPolynomial a r r, Chart.gapPolynomial_mem_domain hr.1 le_rfl hr.2 ha⟩
  have hq := Chart.double_root_between_boundaries_strict (Chart.inverseTuning C)
    ((Chart.amplitudeFloor_pos hr.2 hr.2).trans ha) hK hl hu
    (Chart.coefficients_inverseTuning C)
  exact ⟨C, (sigma_pos_iff_rate_lt_one _).mpr hq.2.2.1, rfl⟩

theorem diagonal_positive_neighborhood {K : ℕ} (hK : 2 ≤ K) {a r : ℝ}
    (hl : Chart.boundaryCosine K < r) (hu : r < Chart.boundaryCosine (K + 1))
    (ha : Chart.amplitudeFloor r r < a) :
    ∃ U : Set Chart.ParameterSpace, IsOpen U ∧ (a, r, r) ∈ U ∧
      ∀ p ∈ U, ∀ q : Tuning,
        Chart.coefficients q = Chart.gapPolynomial p.1 p.2.1 p.2.2 →
        0 < Threshold.sigma q :=
  ⟨positiveRootSet, positiveRootSet_isOpen, diagonal_mem_positiveRootSet hK hl hu ha,
    fun _ hp q he => positive_of_mem_positiveRootSet hp q he⟩

theorem positiveGap_nonempty {K : ℕ} (hK : 2 ≤ K) : (positiveGap K).Nonempty := by
  let r := (Chart.boundaryCosine K + Chart.boundaryCosine (K + 1)) / 2
  let a := Chart.amplitudeFloor r r + 1
  have hw := Chart.boundaryCosine_lt_succ hK
  have hl : Chart.boundaryCosine K < r := by dsimp [r]; linarith
  have hu : r < Chart.boundaryCosine (K + 1) := by dsimp [r]; linarith
  have ha : Chart.amplitudeFloor r r < a := by dsimp [a]; linarith
  have hm := diagonal_mem_positiveRootSet hK hl hu ha
  have hc : (a, r, r) ∈ closure (Chart.gapParameterSet K) :=
    Chart.mem_closure_gapParameterSet hK ⟨hl.le, le_rfl, hu.le⟩ ha
  obtain ⟨p, hpp, hpg⟩ := mem_closure_iff.mp hc positiveRootSet
    positiveRootSet_isOpen hm
  let q := Chart.gapInverse hK ⟨p, hpg⟩
  exact ⟨q.val, q.property, positive_of_mem_positiveRootSet hpp q.val
    (Chart.coefficients_inverseTuning _)⟩

end polyak.GapEdges
