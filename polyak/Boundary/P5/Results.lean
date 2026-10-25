import polyak.Boundary.P5.CriticalDecoupling
import polyak.Boundary.P5.CriticalNormalizedDual
import polyak.Boundary.P5.LocalOptimal

/-!
Article: the complete critical and local P5 results of Appendix B.
Use: exact source regularization, algebraic critical data, true derivatives,
all-lag primal feasibility and primal–dual optimality are exposed together.
-/
noncomputable section
namespace polyak.Boundary.P5
open Spectral Filter
open scoped Topology goldenRatio

/-- Article: Theorem p5h0, the checked actual critical solution and both genuine Jacobian blocks. -/
theorem critical_system_verified :
    (5797/25000 : ℝ)<y₀ ∧ y₀<23189/100000 ∧
    regularSystem (0,criticalPoint)=0 ∧
    primalMatrix.det≠0 ∧ dualMatrix.det≠0 ∧
    (fderiv ℝ regularSystem (0,criticalPoint) ∘L
      ContinuousLinearMap.inr ℝ ℝ Coordinates).IsInvertible :=
  ⟨y₀_bounds.1,y₀_bounds.2,regularSystem_criticalPoint,primalMatrix_det_ne_zero,
    dualMatrix_det_ne_zero,regularSystem_partial_isInvertible⟩

/-- Article: the corresponding central spectrum at zero mass is exactly the feasible three-cycle. -/
theorem critical_spectrum_feasible (y : Frequency) :
    FeasibleU (1/2) 0
      (twoAtomSpectrum 0 (by norm_num) (by norm_num)
        ⟨-1/2,by constructor <;> norm_num⟩ y) 0 := by
  rw [twoAtomSpectrum_zero]
  have hx : (⟨-1/2,by constructor <;> norm_num⟩ : Frequency)=Spiral.atom 0 := by
    apply Subtype.ext
    norm_num [Spiral.atom]
  rw [hx]
  simpa only [Spiral.twist_zero,Spiral.valueConstant_zero,Spiral.spectrum] using Spiral.feasibleU 0

/-- Article: the actual P5 parameter tuple is feasible on one closed right interval, including h=0. -/
theorem exists_local_feasible_interval : ∃ hstar : ℝ, 0<hstar ∧
    ∀ h : ℝ, 0≤h → h≤hstar → ∃ ν : Spectrum,
      FeasibleU (branchU h (localBranch h)) (Real.arcosh (1+h)) ν
        (h*localBranch h 4/Real.sinh (Real.arcosh (1+h))) := by
  obtain ⟨hstar,hpos,hsub⟩ :=
    mem_nhdsGT_iff_exists_Ioc_subset.mp eventually_localBranch_feasible
  refine ⟨hstar,hpos,?_⟩
  intro h hh hmax
  by_cases hz : h=0
  · subst h
    refine ⟨Spiral.spectrum 0,?_⟩
    simpa [branchU] using Spiral.feasibleU 0
  · exact hsub ⟨lt_of_le_of_ne hh (Ne.symm hz),hmax⟩

/-- Article: Theorem p5local, all local analytic, uniqueness and true-boundary conclusions together. -/
theorem p5local : ∃ hstar : ℝ, 0<hstar ∧
    localBranch 0=criticalPoint ∧
    AnalyticOnNhd ℝ localBranch (Set.Ioo (-hstar) hstar) ∧
    (∀ h : ℝ, |h|≤hstar → regularSystem (h,localBranch h)=0) ∧
    (∀ᶠ p in 𝓝 ((0 : ℝ),criticalPoint),
      regularSystem p=0 ↔ localBranch p.1=p.2) ∧
    (∀ t : ℝ, Real.cosh t≤1+hstar → V t=localValue t) ∧
    (∀ h : ℝ, 0≤h → h≤hstar → ∃ ν : Spectrum,
      FeasibleU (branchU h (localBranch h)) (Real.arcosh (1+h)) ν
        (h*localBranch h 4/Real.sinh (Real.arcosh (1+h)))) ∧
    (∀ t : ℝ, V (-t)=V t) ∧ AnalyticAt ℝ V 0 ∧ V 0=Real.log φ := by
  obtain ⟨δ,hδ,han,heq,hV⟩ := central_family_local
  obtain ⟨ε,hε,hfeas⟩ := exists_local_feasible_interval
  let hstar := min δ ε
  have hδ' : hstar≤δ := min_le_left _ _
  have hε' : hstar≤ε := min_le_right _ _
  refine ⟨hstar,lt_min hδ hε,localBranch_zero,?_,?_,localBranch_unique,?_,?_,
    V_even,V_analyticAt_zero,Threshold.V_zero⟩
  · intro h hh
    exact han h ⟨by linarith [hh.1],by linarith [hh.2]⟩
  · intro h hh
    exact heq h (hh.trans hδ')
  · intro t ht
    exact hV t (by linarith)
  · intro h hh hmax
    exact hfeas h hh (hmax.trans hε')

end polyak.Boundary.P5
