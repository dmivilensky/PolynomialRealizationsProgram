import polyak.FiniteHorizon.OriginalPrefactor
import polyak.FiniteHorizon.PhysicalMemory
import polyak.FiniteHorizon.P5SourceFactors
import polyak.Boundary.P5.Derivative

/-!
Article: Theorem rate and Appendix C, the uniform constant for every κ>1.
Use: the globally checked actual P₅ continuation, P₂, spiral and P₁ source
formulas supply all physical factors. Right derivatives handle every switch.
The conclusion is the original from-rest supremum over all finite dimensions.
-/
noncomputable section
namespace polyak.FiniteHorizon
open Growth Growth.FiniteHorizon Energy Spectral Boundary Regularity Set Filter
open scoped Topology

theorem hasPhysicalFactors7_global {q : ℝ} (hq : 0<q) (t : ℝ) : HasPhysicalFactors7 q t := by
  by_cases houter : P2.Ga≤Real.cosh t
  · exact hasPhysicalFactors7_of_cosh_ge_Ga hq houter
  by_cases hz : t=0
  · subst t
    exact (eventually_hasPhysicalFactors7_p5 hq).self_of_nhds
  let h:=Real.cosh t-1
  have hh : h∈Ioc (0 : ℝ) (P2.Ga-1):=by
    dsimp [h]
    exact ⟨sub_pos.mpr (Real.one_lt_cosh.mpr hz),sub_le_sub_right (le_of_not_ge houter) 1⟩
  have hD:=P5.physicalDomain_subset ⟨hh.1.le,hh.2⟩
  have hcosh : Real.cosh t=1+h:=by dsimp [h]; ring
  exact hasPhysicalFactors7_p5_sourceRoot (P5.continuation_geometry ⟨hh.1,hD.2⟩)
    (P5.Selection.continuation_source hD) (P5.continuation_weight5_nonneg hh.1.le hh.2)
    hq hcosh (P5.continuation_prefix hD)

theorem exists_global_right_derivative (t : ℝ) :
    ∃ v' : ℝ,HasDerivWithinAt V v' (Ici t) t ∧ |v'|<1 := by
  by_cases houter : P2.Ga<Real.cosh t
  · exact exists_noncentral_right_derivative houter
  have hGa : Real.cosh t≤P2.Ga:=le_of_not_gt houter
  by_cases hz : t=0
  · subst t
    exact ⟨0,V_hasDerivAt_zero.hasDerivWithinAt,by norm_num⟩
  have hcosh : 1<Real.cosh t:=Real.one_lt_cosh.mpr hz
  by_cases ht : t<0
  · exact ⟨P5.boundaryDerivative t,P5.hasDerivWithinAt_V_right ht hGa,
      P5.abs_boundaryDerivative_lt_one hcosh hGa⟩
  by_cases hlt : Real.cosh t<P2.Ga
  · exact ⟨P5.boundaryDerivative t,(P5.hasDerivAt_V hcosh hlt).hasDerivWithinAt,
      P5.abs_boundaryDerivative_lt_one hcosh hGa⟩
  · have heq : Real.cosh t=P2.Ga:=le_antisymm hGa (le_of_not_gt hlt)
    have hd:=positive_Ga_right_derivative (le_of_not_gt ht) heq
    exact ⟨P2.boundaryDerivative P2.zetaA t,hd⟩

/-- A finite retained memory has the exact rate for every actual q∈(0,1). -/
theorem memory_rate_eq_global {q : ℝ} (hq : 0<q) (hq1 : q<1) :
    ∀ᶠ H : ℕ in atTop,growthRate 0 (2*q) (q^2) H=Real.exp (T q) := by
  obtain ⟨v',hd,hv'⟩:=exists_global_right_derivative (T q)
  exact memory_rate_eq_of_right_physical_source hq hq1 hd (abs_lt.mp hv').2
    (Eventually.of_forall (hasPhysicalFactors7_global hq))

/-- Every normalized Polyak recurrence has a uniform prefactor at its exact rate. -/
theorem exists_uniform_prefactor {q : ℝ} (hq : 0<q) (hq1 : q<1) :
    ∃ H : ℕ,7≤H ∧ ∃ C : ℝ,0<C ∧ ∀ n : ℕ,
      envelope 0 (2*q) (q^2) H n≤C*Real.exp ((n : ℝ)*T q) := by
  obtain ⟨H,hRate,hH⟩:=((memory_rate_eq_global hq hq1).and (eventually_ge_atTop 7)).exists
  obtain ⟨v',hd,hv'⟩:=exists_global_right_derivative (T q)
  have heq:=T_sub_log_eq_V hq hq1
  have hVT : 0<V (T q):=by rw [←heq]; exact actual_twist_pos hq hq1
  refine ⟨H,hH,?_⟩
  exact exists_prefactor_of_right_source_germ hq hd (abs_lt.mp hv').2 hVT heq hH hRate.le
    (Eventually.of_forall (hasPhysicalFactors7_global hq))

/-- Theorem rate: one constant controls all horizons, all dimensions and every
admissible original objective with its genuine zero-momentum initialization. -/
theorem exists_original_prefactor {μ L : ℝ} (hμ : 0<μ) (hL : μ<L) :
    ∃ C : ℝ,0<C ∧ ∀ n : ℕ,
      Dynamics.worstAll μ L (Dynamics.polyakAlpha μ L) (Dynamics.polyakBeta μ L) n≤
        C*Dynamics.rate μ L (Dynamics.polyakAlpha μ L) (Dynamics.polyakBeta μ L)^n := by
  obtain ⟨H,_,C,hC,hbound⟩:=exists_uniform_prefactor
    (Dynamics.polyakQ_pos hμ hL) (Dynamics.polyakQ_lt_one hμ hL)
  obtain ⟨K,hK,hb⟩:=original_prefactor_of_normalized hμ hL hC hbound
  refine ⟨K,hK,fun n => ?_⟩
  rw [originalRate_eq_exp_T hμ hL,←Real.exp_nat_mul]
  exact hb n

end polyak.FiniteHorizon
