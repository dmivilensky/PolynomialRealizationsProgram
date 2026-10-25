import polyak.GapEdges.Junction.AdjacentCurvature
import polyak.Levels.Chart.BoundaryFaces
import polyak.Levels.Chart.ClosedDip

/-! The junction is an actual stable tuning, has the full closed window
as its closed dip, and is approached by tunings inside the original gap. -/
noncomputable section
namespace polyak.GapEdges.Junction
open General Levels Set Filter
open scoped Topology

theorem boundary_cosine_mem {K : ℕ} (hK : 3≤K) :
    Chart.boundaryCosine K∈Ioo (-1:ℝ) 1 := by
  have hω := Chart.boundaryAngle_strict_mem hK
  constructor
  · have hh := Real.strictAntiOn_cos ⟨hω.1.le,hω.2.le⟩ ⟨Real.pi_pos.le,le_rfl⟩ hω.2
    simpa only [Real.cos_pi,Chart.boundaryCosine,Chart.boundaryAngle] using hh
  · have hh := Real.strictAntiOn_cos ⟨le_rfl,Real.pi_pos.le⟩ ⟨hω.1.le,hω.2.le⟩ hω.1
    simpa only [Real.cos_zero,Chart.boundaryCosine,Chart.boundaryAngle] using hh

def sourceParameters (K : ℕ) (hK : 3≤K) (a : ℝ)
    (ha : Chart.amplitudeFloor (Chart.boundaryCosine K) (Chart.boundaryCosine (K+1))<a) :
    Chart.ClosedGapParameters K :=
  ⟨(a,Chart.boundaryCosine K,Chart.boundaryCosine (K+1)),
    ⟨⟨le_rfl,(Chart.boundaryCosine_lt_succ (by omega)).le,le_rfl⟩,
      ha,(boundary_cosine_mem hK).1⟩⟩

def junctionTuning (K : ℕ) (hK : 3≤K) (a : ℝ)
    (ha : Chart.amplitudeFloor (Chart.boundaryCosine K) (Chart.boundaryCosine (K+1))<a) : Tuning :=
  Chart.closedGapInverse (by omega : 2≤K) (sourceParameters K hK a ha)

theorem junctionTuning_coefficients (K : ℕ) (hK : 3≤K) (a : ℝ)
    (ha : Chart.amplitudeFloor (Chart.boundaryCosine K) (Chart.boundaryCosine (K+1))<a) :
    Chart.coefficients (junctionTuning K hK a ha)=
      Chart.gapPolynomial a (Chart.boundaryCosine K) (Chart.boundaryCosine (K+1)) :=
  Chart.coefficients_closedGapInverse _ _

theorem junctionTuning_source_coefficients (K : ℕ) (hK : 3≤K) (a : ℝ)
    (ha : Chart.amplitudeFloor (Chart.boundaryCosine K) (Chart.boundaryCosine (K+1))<a) :
    Chart.coefficients (junctionTuning K hK a ha)=
      junctionCoefficients a (Real.cos (2*(Real.pi/(K+1)))) (Real.cos (2*Real.pi/K)) := by
  rw [junctionTuning_coefficients]
  apply Chart.Coefficients.ext <;>
    dsimp [Chart.gapPolynomial,junctionCoefficients,Chart.boundaryCosine,Chart.boundaryAngle] <;>
    push_cast <;> ring_nf

theorem junctionTuning_phase_equations (K : ℕ) (hK : 3≤K) (a : ℝ)
    (ha : Chart.amplitudeFloor (Chart.boundaryCosine K) (Chart.boundaryCosine (K+1))<a) :
    (junctionTuning K hK a ha).angle (2*Real.pi/K)=Real.pi/K ∧
      (junctionTuning K hK a ha).angle (2*Real.pi/(K+1))=Real.pi/(K+1) := by
  exact Chart.junction_phase_equations hK (sourceParameters K hK a ha) rfl rfl

theorem junctionTuning_closedDip (K : ℕ) (hK : 3≤K) (a : ℝ)
    (ha : Chart.amplitudeFloor (Chart.boundaryCosine K) (Chart.boundaryCosine (K+1))<a) :
    Geometry.closedDip (tuningCurve (junctionTuning K hK a ha))=
      {ω : Frequency | 2*Real.pi/(K+1)≤(ω:ℝ) ∧ (ω:ℝ)≤2*Real.pi/K} := by
  have hl := boundary_cosine_mem hK
  have hu := boundary_cosine_mem (show 3≤K+1 by omega)
  have hap := (Chart.amplitudeFloor_pos hl.2 hu.2).trans ha
  have hh := Chart.closedDip_interval _ hap hl.1
    (Chart.boundaryCosine_lt_succ (by omega : 2≤K)).le hu.2
    (junctionTuning_coefficients K hK a ha)
  have hω₁ := Chart.boundaryAngle_strict_mem hK
  have hω₂ := Chart.boundaryAngle_strict_mem (show 3≤K+1 by omega)
  have hc₁ : Real.arccos (Chart.boundaryCosine K)=2*Real.pi/K :=
    Real.arccos_cos hω₁.1.le hω₁.2.le
  have hc₂ : Real.arccos (Chart.boundaryCosine (K+1))=2*Real.pi/(K+1) := by
    simpa only [Chart.boundaryCosine,Chart.boundaryAngle,Nat.cast_add,Nat.cast_one] using
      Real.arccos_cos hω₂.1.le hω₂.2.le
  rw [hc₁,hc₂] at hh
  exact hh

theorem closedGapInverse_mem_closure {K : ℕ} (hK : 2≤K) (p : Chart.ClosedGapParameters K) :
    Chart.closedGapInverse hK p∈closure {q : Tuning | Geometry.Gap K q} := by
  let t : ℕ→ℝ := fun n=>1/((n:ℝ)+1)
  have ht : Tendsto t atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hmem (n : ℕ) : Chart.approachGap K p.val (t n)∈Chart.gapParameterSet K := by
    apply Chart.approachGap_mem hK p.property.1 p.property.2.1
    · exact one_div_pos.mpr (by positivity)
    · exact (div_le_one (by positivity : 0<(n:ℝ)+1)).mpr (by linarith [Nat.cast_nonneg (α:=ℝ) n])
  let C : ℕ→Chart.CoefficientPoint := fun n=>Chart.gapCoefficientPoint hK
    ⟨Chart.approachGap K p.val (t n),hmem n⟩
  have hC : Tendsto C atTop (𝓝 (Chart.closedGapCoefficientPoint hK p)) := by
    apply tendsto_subtype_rng.mpr
    exact Chart.continuous_gapPolynomial.continuousAt.tendsto.comp
      ((Chart.approachGap_tendsto p.property.1 hK).comp ht)
  apply mem_closure_of_tendsto (Chart.continuous_inverseTuning.continuousAt.tendsto.comp hC)
  exact Eventually.of_forall (fun n=>(Chart.gapInverse hK
    ⟨Chart.approachGap K p.val (t n),hmem n⟩).property)

theorem junctionTuning_mem_closure (K : ℕ) (hK : 3≤K) (a : ℝ)
    (ha : Chart.amplitudeFloor (Chart.boundaryCosine K) (Chart.boundaryCosine (K+1))<a) :
    junctionTuning K hK a ha∈closure {q : Tuning | Geometry.Gap K q} :=
  closedGapInverse_mem_closure _ _

end polyak.GapEdges.Junction
