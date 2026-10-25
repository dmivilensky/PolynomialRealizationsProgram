import polyak.ModeLocking.Boundary.AtomTopology
import polyak.Levels.Program.FiniteAlternative

/-! Convexity forces atoms heavier than one half to have a common position. -/
noncomputable section
namespace polyak.ModeLocking
open Levels MeasureTheory Set

theorem probability_two_atoms_le_one (ν : ProbabilityMeasure Frequency)
    {x y : Frequency} (hxy : x≠y) :
    (ν : Measure Frequency).real {x}+(ν : Measure Frequency).real {y}≤1 := by
  have hd : Disjoint ({x} : Set Frequency) {y} := by simpa using hxy
  rw [← measureReal_union hd (measurableSet_singleton y)]
  exact (measureReal_mono (subset_univ _)).trans_eq (by simp)

theorem probability_atom_le_one (ν : ProbabilityMeasure Frequency) (x : Frequency) :
    (ν : Measure Frequency).real {x}≤1 :=
  (measureReal_mono (subset_univ _)).trans_eq (by simp)

theorem mixAngleMeasure_real (μ ν : ProbabilityMeasure Frequency) (u v : ℝ)
    (hu : 0≤u) (hv : 0≤v) (huv : u+v=1) (A : Set Frequency) :
    (mixAngleMeasure μ ν u v hu hv huv : Measure Frequency).real A =
      u*(μ : Measure Frequency).real A+v*(ν : Measure Frequency).real A := by
  change (ENNReal.ofReal u • (μ : Measure Frequency)+
    ENNReal.ofReal v • (ν : Measure Frequency)).real A = _
  rw [measureReal_add_apply
    (by simp only [Measure.smul_apply]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
    (by simp only [Measure.smul_apply]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))]
  simp only [measureReal_ennreal_smul_apply,ENNReal.toReal_ofReal hu,ENNReal.toReal_ofReal hv]

theorem ProbabilitySolution.mix {Θ : Curve} {N : Set ℤ}
    {μ ν : ProbabilityMeasure Frequency}
    (hμ : ProbabilitySolution Θ N μ) (hν : ProbabilitySolution Θ N ν)
    {u v : ℝ} (hu : 0≤u) (hv : 0≤v) (huv : u+v=1) :
    ProbabilitySolution Θ N (mixAngleMeasure μ ν u v hu hv huv) := by
  constructor
  · have he : (∫ω,Θ.minimizer ω ∂mixAngleMeasure μ ν u v hu hv huv)=
        u*(∫ω,Θ.minimizer ω ∂μ)+v*(∫ω,Θ.minimizer ω ∂ν) :=
      integral_mixAngleMeasure μ ν u v hu hv huv ⟨Θ.minimizer,Θ.continuous_minimizer⟩
    rw [he]
    exact add_nonneg (mul_nonneg hu hμ.1) (mul_nonneg hv hν.1)
  · intro n hn
    have he : (∫ω,Θ.lag n ω ∂mixAngleMeasure μ ν u v hu hv huv)=
        u*(∫ω,Θ.lag n ω ∂μ)+v*(∫ω,Θ.lag n ω ∂ν) :=
      integral_mixAngleMeasure μ ν u v hu hv huv ⟨Θ.lag n,Θ.continuous_lag n⟩
    rw [he]
    exact add_nonneg (mul_nonneg hu (hμ.2 n hn)) (mul_nonneg hv (hν.2 n hn))

theorem common_heavy_atom {F : Set (ProbabilityMeasure Frequency)} {m : ℝ}
    (hm : 1/2<m)
    (hconv : ∀μ∈F,∀ν∈F,∀u v:ℝ,∀hu:0≤u,∀hv:0≤v,∀huv:u+v=1,
      mixAngleMeasure μ ν u v hu hv huv∈F)
    (hheavy : ∀ν∈F,∃x:Frequency,m≤(ν : Measure Frequency).real {x})
    {μ ν : ProbabilityMeasure Frequency} (hμ : μ∈F) (hν : ν∈F)
    {x y : Frequency} (hx : m≤(μ : Measure Frequency).real {x})
    (hy : m≤(ν : Measure Frequency).real {y}) : x=y := by
  by_contra hxy
  let A := (μ : Measure Frequency).real {x}
  let B := (ν : Measure Frequency).real {x}
  have hB : B<1/2 := by
    have hb:=probability_two_atoms_le_one ν hxy
    dsimp [B]
    linarith
  have hA : 1/2<A := lt_of_lt_of_le hm hx
  have hden : 0<A-B := by linarith
  let u := (1/2-B)/(A-B)
  have hu : 0≤u := (div_pos (by linarith) hden).le
  have hu1 : u≤1 := (div_le_one hden).mpr (by linarith)
  have hv : 0≤1-u := sub_nonneg.mpr hu1
  have huv : u+(1-u)=1 := by ring
  let ρ := mixAngleMeasure μ ν u (1-u) hu hv huv
  have hρ : ρ∈F := hconv μ hμ ν hν u (1-u) hu hv huv
  have hxρ : (ρ : Measure Frequency).real {x}=1/2 := by
    rw [mixAngleMeasure_real]
    change u*A+(1-u)*B=1/2
    dsimp [u]
    field_simp
    nlinarith
  obtain ⟨z,hz⟩:=hheavy ρ hρ
  by_cases hzx : z=x
  · rw [hzx,hxρ] at hz
    linarith
  · have hh:=probability_two_atoms_le_one ρ hzx
    rw [hxρ] at hh
    linarith

end polyak.ModeLocking
