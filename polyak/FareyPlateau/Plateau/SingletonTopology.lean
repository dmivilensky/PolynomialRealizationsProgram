import polyak.FareyPlateau.Plateau.SingletonCharacterization
import polyak.FareyPlateau.Plateau.ConnectedRoof
import polyak.Levels.Chart.Continuity
import polyak.ModeLocking.Plateaus.Persistence

/-! The entire singleton region is one actual plateau component of the
regular divergence boundary. Its parameter domain is the full upper roof,
including every resonant slice; continuity of a_F is not assumed. -/
noncomputable section
namespace polyak.FareyPlateau
open General Levels ModeLocking Plateaus Set

theorem singleton_roof_connected {K j k : ℕ} (hK : 2≤K)
    (hf : Chart.FractionInWindow K j k) (b : ℤ) (hb0 : 0<b) (hbk : b<k)
    (hb : b*(j:ℤ)≡1 [ZMOD (k:ℤ)]) :
    IsConnected (upperRoof (singletonRoof K j k b)) := by
  apply bounded_roof_connected (LargeCurvature.continuous_upperMajorant K j k)
  intro D
  exact max_le (le_max_right _ _) (LargeCurvature.aF_le_upperMajorant hK hf b hb0 hbk hb D)

def singletonTuning {K j k : ℕ} (hK : 2≤K) (hf : Chart.FractionInWindow K j k)
    {b : ℤ} (p : upperRoof (singletonRoof K j k b)) : Tuning :=
  edgeTuning (rationalCosine_mem hK hf) (rationalHeight_above hK hf)
    (Chart.fraction_cosine_window hK hf).1 (Chart.fraction_cosine_window hK hf).2
    ((le_max_left _ _).trans_lt p.property)

theorem singletonTuning_coefficients {K j k : ℕ} (hK : 2≤K)
    (hf : Chart.FractionInWindow K j k) {b : ℤ}
    (p : upperRoof (singletonRoof K j k b)) :
    Chart.coefficients (singletonTuning hK hf p)=edgeCoefficients
      (Chart.rationalCosine j k) (Chart.rationalHeight j k) p.val.1 p.val.2 :=
  coefficients_edgeTuning _ _ _ _ _

theorem continuous_singletonTuning {K j k : ℕ} (hK : 2≤K)
    (hf : Chart.FractionInWindow K j k) (b : ℤ) :
    Continuous (singletonTuning hK hf (b:=b)) := by
  apply Chart.continuous_inverseTuning.comp
  apply Continuous.subtype_mk
  exact (continuous_edgeCoefficients _ _).comp continuous_subtype_val

def singletonBoundaryMap {K j k : ℕ} (hK : 2≤K) (hf : Chart.FractionInWindow K j k)
    (b : ℤ) (hb0 : 0<b) (hbk : b<k) (hb : b*(j:ℤ)≡1 [ZMOD (k:ℤ)])
    (p : upperRoof (singletonRoof K j k b)) : BoundaryTuning :=
  ⟨singletonTuning hK hf p,(mem_frontier_iff_sigma_zero _).mpr
    (singleton_of_roof hK hf b hb0 hbk hb _ (singletonTuning_coefficients hK hf p) p.property).2⟩

theorem continuous_singletonBoundaryMap {K j k : ℕ} (hK : 2≤K)
    (hf : Chart.FractionInWindow K j k) (b : ℤ) (hb0 : 0<b) (hbk : b<k)
    (hb : b*(j:ℤ)≡1 [ZMOD (k:ℤ)]) :
    Continuous (singletonBoundaryMap hK hf b hb0 hbk hb) :=
  (continuous_singletonTuning hK hf b).subtype_mk _

def singletonPlateau {K j k : ℕ} (hK : 2≤K) (hf : Chart.FractionInWindow K j k)
    (b : ℤ) (hb0 : 0<b) (hbk : b<k) (hb : b*(j:ℤ)≡1 [ZMOD (k:ℤ)]) :
    Set BoundaryTuning := Set.range (singletonBoundaryMap hK hf b hb0 hbk hb)

theorem mem_singletonPlateau_iff {K j k : ℕ} (hK : 2≤K)
    (hf : Chart.FractionInWindow K j k) (b : ℤ) (hb0 : 0<b) (hbk : b<k)
    (hb : b*(j:ℤ)≡1 [ZMOD (k:ℤ)]) (q : BoundaryTuning) :
    q∈singletonPlateau hK hf b hb0 hbk hb ↔
      RegularSingletonAt j k hf.1 (Chart.fraction_window_arithmetic hK hf).2.le q.val := by
  constructor
  · rintro ⟨p,rfl⟩
    exact (singleton_of_roof hK hf b hb0 hbk hb _
      (singletonTuning_coefficients hK hf p) p.property).1
  · intro hq
    obtain ⟨a,D,he,ha⟩ := (singleton_iff_roof hK hf b hb0 hbk hb q.val).mp hq
    let p : upperRoof (singletonRoof K j k b) := ⟨(a,D),ha⟩
    refine ⟨p,Subtype.ext ?_⟩
    exact (edgeTuning_unique q.val (rationalCosine_mem hK hf) (rationalHeight_above hK hf)
      (Chart.fraction_cosine_window hK hf).1 (Chart.fraction_cosine_window hK hf).2
      ((le_max_left _ _).trans_lt ha) he).symm

theorem singletonPlateau_connected {K j k : ℕ} (hK : 2≤K)
    (hf : Chart.FractionInWindow K j k) (b : ℤ) (hb0 : 0<b) (hbk : b<k)
    (hb : b*(j:ℤ)≡1 [ZMOD (k:ℤ)]) :
    IsConnected (singletonPlateau hK hf b hb0 hbk hb) := by
  let _ : ConnectedSpace (upperRoof (singletonRoof K j k b)) :=
    Subtype.connectedSpace (singleton_roof_connected hK hf b hb0 hbk hb)
  exact isConnected_range (continuous_singletonBoundaryMap hK hf b hb0 hbk hb)

theorem singleton_boundary_regular {j k : ℕ} {hk : 0<k} {hjk : 2*j≤k}
    {q : BoundaryTuning} (h : RegularSingletonAt j k hk hjk q.val) : q∈regularBoundary := by
  obtain ⟨L,R,_⟩ := h
  refine ⟨L,?_⟩
  change Nonempty (RegularData q.val (Threshold.sigma q.val) L)
  rw [(mem_frontier_iff_sigma_zero q.val).mp q.property]
  exact ⟨R⟩

theorem singleton_boundary_support {j k : ℕ} {hk : 0<k} {hjk : 2*j≤k}
    {q : BoundaryTuning} (h : RegularSingletonAt j k hk hjk q.val)
    (hq : q∈regularBoundary) : boundarySupport ⟨q,hq⟩={Edge.atom j k hk hjk} := by
  obtain ⟨L,R,hS⟩ := h
  have hex : ∃R' : RegularData q.val (Threshold.sigma q.val) L,
      Set.range R'.atoms={Edge.atom j k hk hjk} := by
    rw [(mem_frontier_iff_sigma_zero q.val).mp q.property]
    exact ⟨R,hS⟩
  obtain ⟨R',hS'⟩ := hex
  exact (support_eq hq R').trans hS'

theorem singletonPlateau_eq_component {K j k : ℕ} (hK : 2≤K)
    (hf : Chart.FractionInWindow K j k) (b : ℤ) (hb0 : 0<b) (hbk : b<k)
    (hb : b*(j:ℤ)≡1 [ZMOD (k:ℤ)]) {q : BoundaryTuning}
    (hq : q∈singletonPlateau hK hf b hb0 hbk hb) :
    singletonPlateau hK hf b hb0 hbk hb=plateau q := by
  have hs := (mem_singletonPlateau_iff hK hf b hb0 hbk hb q).mp hq
  have hqr := singleton_boundary_regular hs
  apply Subset.antisymm
  · apply (singletonPlateau_connected hK hf b hb0 hbk hb).isPreconnected.subset_connectedComponentIn hq
    intro r hr
    exact singleton_boundary_regular ((mem_singletonPlateau_iff hK hf b hb0 hbk hb r).mp hr)
  · intro r hr
    have hrr : r∈regularBoundary := connectedComponentIn_subset regularBoundary q hr
    have hS := (support_constant_on_plateau (q:=⟨q,hqr⟩) (r:=⟨r,hrr⟩) hr).trans
      (singleton_boundary_support hs hqr)
    apply (mem_singletonPlateau_iff hK hf b hb0 hbk hb r).mpr
    have hex : ∃L : ℕ,∃R : RegularData r.val (Threshold.sigma r.val) L,
        Set.range R.atoms={Edge.atom j k hf.1 (Chart.fraction_window_arithmetic hK hf).2.le} :=
      ⟨chosenPeriod ⟨r.val,hrr⟩,chosenData ⟨r.val,hrr⟩,hS⟩
    rwa [(mem_frontier_iff_sigma_zero r.val).mp r.property] at hex

end polyak.FareyPlateau
