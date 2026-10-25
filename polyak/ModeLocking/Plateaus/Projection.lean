import polyak.ModeLocking.Plateaus.Persistence
import polyak.ModeLocking.Modelock.Boundary

/-! The actual boundary projection is open in the ambient two-dimensional
parameter plane. The source boundary function itself is analytic on the
projected regular boundary, not merely represented by a separate local graph. -/
noncomputable section
namespace polyak.ModeLocking.Plateaus
open General Levels Set Filter
open Global.Threshold
open scoped Topology

theorem finiteBoundary_beta_pos (p : finiteBoundaryDomain) : 0 < p.val.val.2 := by
  apply lt_of_le_of_ne p.val.property.1
  intro he
  have htop := kappaBoundary_top_of_beta_zero p.val he.symm
  exact p.property.ne htop

def finiteBoundaryCoordinates (p : finiteBoundaryDomain) : ℝ × ℝ := p.val.val

theorem isOpenEmbedding_finiteBoundaryCoordinates :
    Topology.IsOpenEmbedding finiteBoundaryCoordinates := by
  have he : Topology.IsEmbedding finiteBoundaryCoordinates :=
    Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
  refine ⟨he, ?_⟩
  obtain ⟨V, hV, hpre⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp finiteBoundaryDomain_isOpen
  let J : Set (ℝ × ℝ) := {p | 0 < p.2 ∧ p.2 < 1 ∧ 0 < p.1 ∧ p.1 < 2 * (1 + p.2)}
  have hJ : IsOpen J := by
    exact (isOpen_lt continuous_const continuous_snd).inter
      ((isOpen_lt continuous_snd continuous_const).inter
        ((isOpen_lt continuous_const continuous_fst).inter
          (isOpen_lt continuous_fst (continuous_const.mul (continuous_const.add continuous_snd)))))
  have hr : Set.range finiteBoundaryCoordinates = V ∩ J := by
    ext z
    constructor
    · rintro ⟨p, rfl⟩
      refine ⟨?_, finiteBoundary_beta_pos p, p.val.property.2.1,
        p.val.property.2.2.1, p.val.property.2.2.2⟩
      have hp : p.val ∈ (Subtype.val : ParameterStrip → ℝ × ℝ) ⁻¹' V :=
        (Set.ext_iff.mp hpre p.val).mpr p.property
      exact hp
    · rintro ⟨hV, hJ⟩
      let p : ParameterStrip := ⟨z, hJ.1.le, hJ.2.1, hJ.2.2.1, hJ.2.2.2⟩
      have hp : p ∈ finiteBoundaryDomain := by rw [← hpre]; exact hV
      exact ⟨⟨p, hp⟩, rfl⟩
  rw [hr]
  exact hV.inter hJ

def finiteBoundaryPlane (p : finiteBoundaryDomain) : Gradient.Plane :=
  (Homeomorph.finTwoArrow : Gradient.Plane ≃ₜ ℝ × ℝ).symm (finiteBoundaryCoordinates p)

theorem isOpenEmbedding_finiteBoundaryPlane : Topology.IsOpenEmbedding finiteBoundaryPlane :=
  (Homeomorph.finTwoArrow : Gradient.Plane ≃ₜ ℝ × ℝ).symm.isOpenEmbedding.comp
    isOpenEmbedding_finiteBoundaryCoordinates

def boundaryPlaneProjection (q : BoundaryTuning) : Gradient.Plane :=
  finiteBoundaryPlane (boundaryProjection q)

theorem boundaryPlaneProjection_eq (q : BoundaryTuning) :
    boundaryPlaneProjection q = Gradient.planeParameters q.val := by
  ext i
  fin_cases i <;> rfl

theorem isOpenEmbedding_boundaryPlaneProjection : Topology.IsOpenEmbedding boundaryPlaneProjection :=
  isOpenEmbedding_finiteBoundaryPlane.comp boundaryGraphHomeomorph.isOpenEmbedding

def projectedRegularBoundary : Set Gradient.Plane := boundaryPlaneProjection '' regularBoundary

theorem isOpen_projectedRegularBoundary : IsOpen projectedRegularBoundary :=
  isOpenEmbedding_boundaryPlaneProjection.isOpenMap _ isOpen_regularBoundary

def projectedPlateau (q : BoundaryTuning) : Set Gradient.Plane := boundaryPlaneProjection '' plateau q

theorem projectedPlateau_open (q : BoundaryTuning) : IsOpen (projectedPlateau q) :=
  isOpenEmbedding_boundaryPlaneProjection.isOpenMap _ (plateau_open q)

theorem projectedPlateau_connected {q : BoundaryTuning} (hq : q ∈ regularBoundary) :
    IsConnected (projectedPlateau q) :=
  (plateau_connected hq).image boundaryPlaneProjection
    isOpenEmbedding_boundaryPlaneProjection.continuous.continuousOn

def planeAdmissible (p : Gradient.Plane) : Prop :=
  0 ≤ p 1 ∧ p 1 < 1 ∧ 0 < p 0 ∧ p 0 < 2 * (1 + p 1)

/-- The actual extended boundary threshold converted to real values. Its
values on the projected regular boundary are finite; the extension outside
the admissible strip is immaterial to its local analyticity there. -/
def ambientKappaBoundary (p : Gradient.Plane) : ℝ := by
  classical
  exact if h : planeAdmissible p then (kappaBoundary ⟨(p 0, p 1), h⟩ : EReal).toReal else 0

theorem ambientKappaBoundary_at_frontier (q : BoundaryTuning) :
    ambientKappaBoundary (boundaryPlaneProjection q) = q.val.kappa := by
  rw [boundaryPlaneProjection_eq]
  have h : planeAdmissible (Gradient.planeParameters q.val) :=
    ⟨q.val.beta_nonneg, q.val.beta_lt_one, q.val.y_pos, q.val.y_lt⟩
  rw [ambientKappaBoundary, dite_eq_left h]
  have he := (kappaBoundary_eq_iff (parameters q.val) (conditionNumber q.val)).mpr
    (by simpa only [fixedThreshold, tuning_parameters] using sigma_eq_zero_on_frontier q.property)
  change (kappaBoundary (parameters q.val) : EReal).toReal = q.val.kappa
  rw [he, EReal.toReal_coe]
  rfl

/-- At every regular boundary point the source function kappaBoundary is
analytic in an ambient open neighborhood of its original two parameters. -/
theorem analyticAt_ambientKappaBoundary (q : BoundaryTuning) (hq : q ∈ regularBoundary) :
    AnalyticAt ℝ ambientKappaBoundary (boundaryPlaneProjection q) := by
  let R : RegularTuning := ⟨q.val, hq⟩
  let D := chosenData R
  have hz : Threshold.sigma q.val = 0 := sigma_eq_zero_on_frontier q.property
  obtain ⟨g, hg, _, U, hU, hqU, hgraph⟩ := D.analytic_divergence_boundary hz
  let p0 := boundaryProjection q
  let f : finiteBoundaryDomain → Tuning := fun p => (boundaryLift p).val
  have hf : Continuous f := continuous_subtype_val.comp boundaryGraphHomeomorph.symm.continuous
  have hbase : f p0 = q.val := congrArg Subtype.val (boundaryGraphHomeomorph.symm_apply_apply q)
  have hlim : Tendsto f (𝓝 p0) (𝓝 q.val) := by
    rw [← hbase]
    exact hf.tendsto p0
  have hnear : ∀ᶠ p in 𝓝 p0,
      g (finiteBoundaryPlane p) = ambientKappaBoundary (finiteBoundaryPlane p) := by
    filter_upwards [hlim.eventually (hU.mem_nhds hqU)] with p hp
    have h := (hgraph (f p) hp).mp (boundaryLift p).property
    have he : boundaryPlaneProjection (boundaryLift p) = finiteBoundaryPlane p := by
      change finiteBoundaryPlane (boundaryGraphHomeomorph (boundaryGraphHomeomorph.symm p)) = _
      rw [boundaryGraphHomeomorph.apply_symm_apply]
    have hc := ambientKappaBoundary_at_frontier (boundaryLift p)
    rw [he] at hc
    rw [hc]
    exact h
  have hmap : Filter.map finiteBoundaryPlane (𝓝 p0) = 𝓝 (boundaryPlaneProjection q) :=
    isOpenEmbedding_finiteBoundaryPlane.map_nhds_eq p0
  have heq : g =ᶠ[𝓝 (boundaryPlaneProjection q)] ambientKappaBoundary := by
    rw [← hmap]
    exact hnear
  have hg' : AnalyticAt ℝ g (boundaryPlaneProjection q) := by
    rw [boundaryPlaneProjection_eq]
    exact hg
  exact hg'.congr heq

theorem analyticOnNhd_ambientKappaBoundary :
    AnalyticOnNhd ℝ ambientKappaBoundary projectedRegularBoundary := by
  rintro p ⟨q, hq, rfl⟩
  exact analyticAt_ambientKappaBoundary q hq

theorem analyticOnNhd_ambientKappaBoundary_plateau (q : BoundaryTuning) :
    AnalyticOnNhd ℝ ambientKappaBoundary (projectedPlateau q) := by
  intro p hp
  apply analyticOnNhd_ambientKappaBoundary
  obtain ⟨r, hr, rfl⟩ := hp
  exact ⟨r, connectedComponentIn_subset regularBoundary q hr, rfl⟩

end polyak.ModeLocking.Plateaus
