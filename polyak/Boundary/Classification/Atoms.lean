import polyak.Boundary.Classification.Value
import polyak.Boundary.P5.P2Lift

/-! Article: at most two frequencies suffice on each already identified spectral regime. -/
noncomputable section
namespace polyak.Boundary.Classification
open Spectral

/-- A concrete normalized probability measure with at most two physical atoms achieves V. -/
def HasTwoAtomOptimum (t : ℝ) : Prop :=
  ∃ (p : ℝ) (hp0 : 0≤p) (hp1 : p≤1) (x y : Frequency) (C : ℝ),
    Feasible (V t) t (P5.twoAtomSpectrum p hp0 hp1 x y) C

theorem hasTwoAtomOptimum_of_dirac {t C : ℝ} (a : Frequency)
    (hf : Feasible (V t) t ⟨MeasureTheory.Measure.dirac a,by infer_instance⟩ C) :
    HasTwoAtomOptimum t := by
  refine ⟨0,le_rfl,by norm_num,a,a,C,?_⟩
  rw [P5.twoAtomSpectrum_zero]
  exact hf

theorem hasTwoAtomOptimum_p1 {t : ℝ} (hG : GW≤Real.cosh t) : HasTwoAtomOptimum t := by
  let z := 1/Real.cosh t
  have hz : z∈Set.Ioc (0 : ℝ) P1.zW := p1_parameter hG
  have hz1 : z≤3/4 := by linarith [hz.2,P1.zW_bounds.2]
  have ht : Real.cosh t=1/z := by dsimp [z]; field_simp
  let a := P1.physicalAtom hz.1 hz1 (P1.continuation_physical hz)
  apply hasTwoAtomOptimum_of_dirac a
  rw [P1.continuation_optimal hz ht]
  unfold Feasible
  rw [Real.sinh_arsinh]
  exact P1.continuation_feasible hz ht

theorem hasTwoAtomOptimum_spiral {t : ℝ} (hG : G1≤Real.cosh t) (hW : Real.cosh t≤GW) :
    HasTwoAtomOptimum t := by
  apply hasTwoAtomOptimum_of_dirac (Spiral.atom t)
  rw [spiral_optimal hG hW]
  exact Spiral.feasible t

theorem hasTwoAtomOptimum_p2 {t : ℝ} (hG : Real.cosh t∈Set.Icc P2.Ga G1) :
    HasTwoAtomOptimum t := by
  let z := p2Parameter (Real.cosh t)
  have hz : z∈Set.Icc P2.zeta1 P2.zetaA ∧ P2.G z=Real.cosh t := p2Parameter_spec hG
  have hm := P2.arc_mem_interval hz.1
  refine ⟨P2.p z,(P2.p_mem hm hz.1.1).1,(P2.p_mem hm hz.1.1).2.le,
    P2.lowerFrequency z hm,P2.upperFrequency z hm,P2.d z/Real.sinh t,?_⟩
  rw [← P5.p2Lift_spectrum hm hz.1.1]
  exact P2.spectrum_optimal hz.1 hz.2.symm

theorem hasTwoAtomOptimum_zero : HasTwoAtomOptimum 0 := by
  apply hasTwoAtomOptimum_of_dirac (Spiral.atom 0)
  rw [P5.critical_boundary_value]
  have hs := Spiral.feasible (0 : ℝ)
  norm_num [Spiral.twist,Spiral.G,Spiral.spectrum] at hs
  exact hs

end polyak.Boundary.Classification
