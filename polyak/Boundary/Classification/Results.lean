import polyak.Boundary.Classification.Atoms
import polyak.Boundary.P5.PhysicalContinuation
import polyak.Boundary.P2.SpiralStrict
import polyak.Boundary.P2.ActiveTable
import polyak.Spiral.Active
import polyak.Boundary.P1.ActiveContinuation
import polyak.Boundary.P5.ActiveContinuation
import polyak.Regularity.Continuity

/-! Article: Theorem classification and Proposition spiralsub.
All four families are identified with the actual boundary on their complete
closed physical domains. The supplied optimal measure always has at most two atoms. -/
noncomputable section
namespace polyak.Boundary.Classification
open Spectral
open scoped NNReal

/-- The complete central family, including both its exact endpoints. -/
theorem p5_formula {t : ℝ} (hG : Real.cosh t≤P2.Ga) : V t=Real.arsinh (u5 (Real.cosh t)) := by
  exact P5.continuation_optimal ⟨by linarith [Real.one_le_cosh t],by linarith⟩ (by ring)

/-- Article: V(t)=arsinh u(cosh t) for every real exponent, without a numerical premise. -/
theorem boundary_formula (t : ℝ) : V t=Real.arsinh (u (Real.cosh t)) := by
  by_cases h5 : Real.cosh t≤P2.Ga
  · rw [u,ite_eq_left h5]
    exact p5_formula h5
  · by_cases h2 : Real.cosh t≤G1
    · rw [u,ite_eq_right h5,ite_eq_left h2]
      exact p2_formula ⟨(lt_of_not_ge h5).le,h2⟩
    · by_cases hW : Real.cosh t≤GW
      · rw [u,ite_eq_right h5,ite_eq_right h2,ite_eq_left hW]
        exact spiral_optimal (lt_of_not_ge h2).le hW
      · rw [u,ite_eq_right h5,ite_eq_right h2,ite_eq_right hW]
        exact p1_formula (lt_of_not_ge hW).le

/-- Exact equality of the two independently specified families at Ga. -/
theorem u5_Ga : u5 P2.Ga=u2 P2.Ga := by
  unfold u5 u2
  rw [P5.continuation_endpoint_u]
  rw [p2Parameter_unique ⟨le_rfl,P2.Ga_lt_G1.le⟩ ⟨P2.zeta1_lt_zetaA.le,le_rfl⟩ rfl]

theorem u5_one : u5 1=1/2 := by simp [u5,P5.branchU]

/-- The source piecewise curve is exactly the actual nonnegative optimal twist. -/
theorem u_eq_sinh_V_arcosh {G : ℝ} (hG : 1≤G) : u G=Real.sinh (V (Real.arcosh G)) := by
  rw [boundary_formula,Real.cosh_arcosh hG,Real.sinh_arsinh]

/-- The source curve is continuous across all three joins, on its whole physical domain. -/
theorem u_continuousOn : ContinuousOn u (Set.Ici (1 : ℝ)) := by
  have hc : ContinuousOn (fun G : ℝ => Real.sinh (V (Real.arcosh G))) (Set.Ici 1) :=
    Real.continuous_sinh.comp_continuousOn
      (Regularity.V_continuous.comp_continuousOn Real.continuousOn_arcosh)
  apply hc.congr
  intro G hG
  exact u_eq_sinh_V_arcosh hG

/-- The actual optimum has a normalized probability measure with at most two atoms. -/
theorem hasTwoAtomOptimum (t : ℝ) : HasTwoAtomOptimum t := by
  by_cases h5 : Real.cosh t≤P2.Ga
  · by_cases ht : t=0
    · subst t
      exact hasTwoAtomOptimum_zero
    · exact P5.continuation_feasible (h:=Real.cosh t-1)
        ⟨by linarith [Real.one_lt_cosh.mpr ht],by linarith⟩ (by ring)
  · by_cases h2 : Real.cosh t≤G1
    · exact hasTwoAtomOptimum_p2 ⟨(lt_of_not_ge h5).le,h2⟩
    · by_cases hW : Real.cosh t≤GW
      · exact hasTwoAtomOptimum_spiral (lt_of_not_ge h2).le hW
      · exact hasTwoAtomOptimum_p1 (lt_of_not_ge hW).le

/-- Article: at most two frequencies suffice, in the original finite-spectrum representation. -/
theorem exists_twoAtom_optimal (t : ℝ) :
    ∃ (w : Bool → ℝ≥0) (c : Bool → Frequency) (hw : ∑ b,w b=1) (C : ℝ),
      Feasible (V t) t (Waves.finiteSpectrum w c hw) C := by
  obtain ⟨p,hp0,hp1,x,y,C,hf⟩ := hasTwoAtomOptimum t
  exact ⟨P5.twoAtomWeights p hp0 hp1,fun b => if b then y else x,
    P5.twoAtomWeights_sum p hp0 hp1,C,hf⟩

/-- Strict suboptimality of the spiral throughout the two inner noncritical regimes. -/
theorem strict_spiral_inner {t : ℝ} (hl : 1<Real.cosh t) (hu : Real.cosh t<G1) :
    Real.arsinh (1-1/(2*Real.cosh t))<V t := by
  by_cases h5 : Real.cosh t≤P2.Ga
  · exact P5.continuation_strict_spiral (h:=Real.cosh t-1) ⟨by linarith,by linarith⟩ (by ring)
  · have hp := p2Parameter_spec ⟨(lt_of_not_ge h5).le,hu.le⟩
    have h1 : P2.zeta1<p2Parameter (Real.cosh t) := by
      apply lt_of_le_of_ne hp.1.1
      intro he
      rw [← he,P2.G_zeta1] at hp
      linarith [hp.2]
    exact P2.strict_spiral (P2.arc_mem_interval hp.1) h1 hp.1.2 hp.2.symm

/-- Strict suboptimality of the spiral on the entire outer one-atom regime. -/
theorem strict_spiral_outer {t : ℝ} (hW : GW<Real.cosh t) :
    Real.arsinh (1-1/(2*Real.cosh t))<V t := by
  have hz : 1/Real.cosh t∈Set.Ioo (0 : ℝ) P1.zW := by
    refine ⟨by positivity,?_⟩
    unfold P1.zW
    exact one_div_lt_one_div_of_lt (by linarith [GW_bounds.1]) hW
  exact P1.continuation_strict_spiral hz (by field_simp)

/-- Article: the spiral is optimal exactly on its closed arc and at the critical three-cycle. -/
theorem spiral_optimal_iff (t : ℝ) :
    V t=Real.arsinh (1-1/(2*Real.cosh t)) ↔
      (G1≤Real.cosh t ∧ Real.cosh t≤GW) ∨ t=0 := by
  constructor
  · intro he
    by_cases ht : t=0
    · exact Or.inr ht
    · left
      constructor
      · by_contra hG
        exact (strict_spiral_inner (Real.one_lt_cosh.mpr ht) (lt_of_not_ge hG)).ne he.symm
      · by_contra hG
        exact (strict_spiral_outer (lt_of_not_ge hG)).ne he.symm
  · rintro (⟨h1,hW⟩ | rfl)
    · exact spiral_optimal h1 hW
    · rw [P5.critical_boundary_value]
      norm_num

end polyak.Boundary.Classification
