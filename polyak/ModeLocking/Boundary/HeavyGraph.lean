import polyak.ModeLocking.Boundary.Support
import polyak.ModeLocking.Boundary.AtomConstraint

/-! The heavy-atom graph is closed after projection over all probability measures.
No normalization condition is imposed on a limiting measure. -/
noncomputable section
namespace polyak.ModeLocking
open General Levels MeasureTheory Set

def HeavySolutionGraph (m:ℝ) : Set (Tuning×Frequency) :=
  {p | ∃ν:ProbabilityMeasure Frequency,
    ProbabilitySolution (Geometry.shiftedCurve p.1 (Threshold.sigma p.1)) nonzeroLags ν ∧
      m≤(ν : Measure Frequency).real {p.2}}

theorem isClosed_heavySolutionGraph (m:ℝ) : IsClosed (HeavySolutionGraph m) := by
  have hqν : Continuous (fun p:(Tuning×Frequency)×ProbabilityMeasure Frequency=>(p.1.1,p.2)) :=
    continuous_fst.fst.prodMk continuous_snd
  have hνx : Continuous (fun p:(Tuning×Frequency)×ProbabilityMeasure Frequency=>(p.2,p.1.2)) :=
    continuous_snd.prodMk continuous_fst.snd
  have hsol := (Threshold.isClosed_probabilitySolution_family
    (fun q:Tuning=>Geometry.shiftedCurve q (Threshold.sigma q))
      thresholdCurve_jointContinuous nonzeroLags).preimage hqν
  have hatom := (isClosed_moving_atom_real m).preimage hνx
  have hclosed := isClosedMap_fst_of_compactSpace _ (hsol.inter hatom)
  have he : Prod.fst '' {p:(Tuning×Frequency)×ProbabilityMeasure Frequency |
      ProbabilitySolution (Geometry.shiftedCurve p.1.1 (Threshold.sigma p.1.1)) nonzeroLags p.2 ∧
        m≤(p.2 : Measure Frequency).real {p.1.2}} = HeavySolutionGraph m := by
    ext p
    constructor
    · rintro ⟨⟨q,ν⟩,h,rfl⟩
      exact ⟨ν,h⟩
    · rintro ⟨ν,h⟩
      exact ⟨(p,ν),h,rfl⟩
  rw [←he]
  exact hclosed

theorem heavySolutionGraph_iff {K:ℕ} {q:Tuning} (hq:q∈BoundaryInGap K)
    {m:ℝ} (hm:1/2<m)
    (hh:∀ν:ProbabilityMeasure Frequency,NormalizedExtremal q ν→
      ∃x:Frequency,m≤(ν : Measure Frequency).real {x})
    {r:Frequency} (hr:∀ν:ProbabilityMeasure Frequency,NormalizedExtremal q ν→
      m≤(ν : Measure Frequency).real {r}) (x:Frequency) :
    (q,x)∈HeavySolutionGraph m ↔ x=r := by
  constructor
  · rintro ⟨ν,hν,hx⟩
    rw [boundary_sigma_zero hq,Geometry.shiftedCurve_zero] at hν
    have hx0:=feasible_heavy_atom_ne_zero hν hm hx
    obtain ⟨ρ,hρ,hzero,hinc⟩:=normalize_away_zero hν
    have hρn:NormalizedExtremal q ρ:=⟨hρ,hzero⟩
    have hxρ:=hx.trans (hinc x hx0)
    exact common_heavy_atom hm
      (F:={μ|NormalizedExtremal q μ})
      (fun _ hμ _ hν _ _ hu hv huv=>normalized_extremal_mix hμ hν hu hv huv)
      (fun μ hμ=>hh μ hμ) hρn hρn hxρ (hr ρ hρn)
  · rintro rfl
    obtain ⟨ν,hν⟩:=normalized_extremals_nonempty hq
    refine ⟨ν,?_,hr ν hν⟩
    simpa only [boundary_sigma_zero hq,Geometry.shiftedCurve_zero] using hν.1

theorem continuous_heavy_position {K:ℕ} {C:Set Tuning}
    (hC:C⊆BoundaryInGap K) {m:ℝ} (hm:1/2<m)
    (hh:∀q∈C,∀ν:ProbabilityMeasure Frequency,NormalizedExtremal q ν→
      ∃x:Frequency,m≤(ν : Measure Frequency).real {x})
    (r:C→Frequency)
    (hr:∀q:C,∀ν:ProbabilityMeasure Frequency,NormalizedExtremal q ν→
      m≤(ν : Measure Frequency).real {r q}) : Continuous r := by
  apply continuous_of_isClosed_graph
  have hc : Continuous (fun p:C×Frequency=>((p.1: Tuning),p.2)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have he : r.graph=(fun p:C×Frequency=>((p.1:Tuning),p.2)) ⁻¹' HeavySolutionGraph m := by
    ext p
    exact ((heavySolutionGraph_iff (hC p.1.property) hm (hh p.1 p.1.property)
      (hr p.1) p.2).trans eq_comm).symm
  rw [he]
  exact (isClosed_heavySolutionGraph m).preimage hc

end polyak.ModeLocking
