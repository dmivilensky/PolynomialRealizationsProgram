import polyak.FareyPlateau.Plateau.SingletonTopology
import polyak.FareyPlateau.Edge.Boundary

/-! Source conclusions on the full singleton plateau: its original gap,
all finite Borel extremals, unique anchor, exact rational tongue graph,
and the open connected analytic projection in the original parameters. -/
noncomputable section
namespace polyak.FareyPlateau
open General Levels ModeLocking Plateaus Set MeasureTheory
open scoped Classical

theorem singletonPlateau_in_gap {K j k : ℕ} (hK : 2≤K)
    (hf : Chart.FractionInWindow K j k) (b : ℤ) (hb0 : 0<b) (hbk : b<k)
    (hb : b*(j:ℤ)≡1 [ZMOD (k:ℤ)]) {q : BoundaryTuning}
    (hq : q∈singletonPlateau hK hf b hb0 hbk hb) : q.val∈BoundaryInGap K := by
  obtain ⟨a,D,he,ha⟩ := (singleton_iff_roof hK hf b hb0 hbk hb q.val).mp
    ((mem_singletonPlateau_iff hK hf b hb0 hbk hb q).mp hq)
  rw [GapEdges.boundaryInGap_eq_zero]
  exact ⟨(source_edgedomain q.val hK hf he).mpr ((le_max_left _ _).trans_lt ha),
    (mem_frontier_iff_sigma_zero q.val).mp q.property⟩

theorem singletonPlateau_certificate {K j k : ℕ} (hK : 2≤K)
    (hf : Chart.FractionInWindow K j k) (b : ℤ) (hb0 : 0<b) (hbk : b<k)
    (hb : b*(j:ℤ)≡1 [ZMOD (k:ℤ)]) {q : BoundaryTuning}
    (hq : q∈singletonPlateau hK hf b hb0 hbk hb) : Nonempty (Edge.Certificate q.val 0 j k) := by
  obtain ⟨hj,hjk⟩ := Chart.fraction_window_arithmetic hK hf
  have hbinv := inverse_mod_value (by omega : 3≤k) hb
  obtain ⟨a,D,he,ha⟩ := (singleton_iff_roof hK hf b hb0 hbk hb q.val).mp
    ((mem_singletonPlateau_iff hK hf b hb0 hbk hb q).mp hq)
  obtain ⟨C,hC⟩ := (Ray.aF_lt_iff (by omega) hjk hbinv
    (LargeCurvature.sourceCertificate_nonempty hK hf b hb0 hbk hb D)).mp
      ((le_max_right _ _).trans_lt ha)
  exact ⟨C.edgeCertificate (by omega) hjk hb0 hbk hbinv q.val he hC⟩

theorem singletonPlateau_extremals {K j k : ℕ} (hK : 2≤K)
    (hf : Chart.FractionInWindow K j k) (b : ℤ) (hb0 : 0<b) (hbk : b<k)
    (hb : b*(j:ℤ)≡1 [ZMOD (k:ℤ)]) {q : BoundaryTuning}
    (hq : q∈singletonPlateau hK hf b hb0 hbk hb)
    {w : Measure Frequency} (hw : ProgramSolution (tuningCurve q.val) nonzeroLags w) :
    ∃v z : NNReal,0<v ∧ w=(v:ENNReal)•Measure.dirac
      (Edge.atom j k hf.1 (Chart.fraction_window_arithmetic hK hf).2.le)+
        (z:ENNReal)•Measure.dirac frequencyZero ∧ (z:ℝ)≤(v:ℝ)*Real.cos (Real.pi/k) := by
  obtain ⟨C⟩ := singletonPlateau_certificate hK hf b hb0 hbk hb hq
  exact C.extremal_classification (by simpa only [Geometry.shiftedCurve_zero] using hw)

theorem singletonPlateau_unique_anchor {K j k : ℕ} (hK : 2≤K)
    (hf : Chart.FractionInWindow K j k) (b : ℤ) (hb0 : 0<b) (hbk : b<k)
    (hb : b*(j:ℤ)≡1 [ZMOD (k:ℤ)]) {q : BoundaryTuning}
    (hq : q∈singletonPlateau hK hf b hb0 hbk hb)
    {w : Measure Frequency} (hw : ProgramSolution (tuningCurve q.val) nonzeroLags w) :
    ∀ω : Frequency,Farey.Anchor q.val w ω ↔
      ω=Edge.atom j k hf.1 (Chart.fraction_window_arithmetic hK hf).2.le := by
  have hs := (mem_singletonPlateau_iff hK hf b hb0 hbk hb q).mp hq
  have hqr := singleton_boundary_regular hs
  have hgap := singletonPlateau_in_gap hK hf b hb0 hbk hb hq
  rw [GapEdges.boundaryInGap_eq_zero] at hgap
  exact Edge.singleton_plateau_anchor (p:=⟨q,hqr⟩) (r:=⟨q,hqr⟩)
    (mem_connectedComponentIn hqr)
    hgap.1
    (singleton_boundary_support hs hqr) hw

theorem singletonPlateau_kappaBoundary {K j k : ℕ} (hK : 2≤K)
    (hf : Chart.FractionInWindow K j k) (b : ℤ) (hb0 : 0<b) (hbk : b<k)
    (hb : b*(j:ℤ)≡1 [ZMOD (k:ℤ)]) {q : BoundaryTuning}
    (hq : q∈singletonPlateau hK hf b hb0 hbk hb) :
    (Global.Threshold.kappaBoundary (Global.Threshold.parameters q.val):EReal)=
      Farey.rationalTongue (Global.Threshold.parameters q.val) j k := by
  obtain ⟨L,R,hS⟩ := (mem_singletonPlateau_iff hK hf b hb0 hbk hb q).mp hq
  obtain ⟨hj,hjk⟩ := Chart.fraction_window_arithmetic hK hf
  exact Edge.singleton_kappaBoundary R (by omega) (by omega) hjk b
    (inverse_mod_value (by omega) hb) hS

def ambientRationalTongue (j k : ℕ) (p : Gradient.Plane) : ℝ :=
  if h : planeAdmissible p then (Farey.rationalTongue ⟨(p 0,p 1),h⟩ j k).toReal else 0

theorem singletonPlateau_projected_graph {K j k : ℕ} (hK : 2≤K)
    (hf : Chart.FractionInWindow K j k) (b : ℤ) (hb0 : 0<b) (hbk : b<k)
    (hb : b*(j:ℤ)≡1 [ZMOD (k:ℤ)]) :
    EqOn ambientKappaBoundary (ambientRationalTongue j k)
      (boundaryPlaneProjection '' singletonPlateau hK hf b hb0 hbk hb) := by
  rintro p ⟨q,hq,rfl⟩
  rw [ambientKappaBoundary_at_frontier]
  have he := singletonPlateau_kappaBoundary hK hf b hb0 hbk hb hq
  have hzero := (mem_frontier_iff_sigma_zero q.val).mp q.property
  have hκ := (Global.Threshold.kappaBoundary_eq_iff
    (Global.Threshold.parameters q.val) (Global.Threshold.conditionNumber q.val)).mpr
    (by simpa only [Global.Threshold.fixedThreshold,Global.Threshold.tuning_parameters] using hzero)
  have h : planeAdmissible (Gradient.planeParameters q.val) :=
    ⟨q.val.beta_nonneg,q.val.beta_lt_one,q.val.y_pos,q.val.y_lt⟩
  rw [ambientRationalTongue,boundaryPlaneProjection_eq,dite_eq_left h]
  change q.val.kappa=(Farey.rationalTongue (Global.Threshold.parameters q.val) j k).toReal
  rw [←he,hκ,EReal.toReal_coe]
  rfl

theorem singletonPlateau_projected_analytic {K j k : ℕ} (hK : 2≤K)
    (hf : Chart.FractionInWindow K j k) (b : ℤ) (hb0 : 0<b) (hbk : b<k)
    (hb : b*(j:ℤ)≡1 [ZMOD (k:ℤ)]) :
    IsOpen (boundaryPlaneProjection '' singletonPlateau hK hf b hb0 hbk hb) ∧
      IsConnected (boundaryPlaneProjection '' singletonPlateau hK hf b hb0 hbk hb) ∧
      AnalyticOnNhd ℝ ambientKappaBoundary
        (boundaryPlaneProjection '' singletonPlateau hK hf b hb0 hbk hb) := by
  obtain ⟨q,hq⟩ := (singletonPlateau_connected hK hf b hb0 hbk hb).nonempty
  have hqr := singleton_boundary_regular ((mem_singletonPlateau_iff hK hf b hb0 hbk hb q).mp hq)
  rw [singletonPlateau_eq_component hK hf b hb0 hbk hb hq]
  exact ⟨projectedPlateau_open q,projectedPlateau_connected hqr,
    analyticOnNhd_ambientKappaBoundary_plateau q⟩

end polyak.FareyPlateau
