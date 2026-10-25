import polyak.Regularity.Memory
import polyak.Boundary.P1.Results
import polyak.Regularity.Inverse

/-!
Article: Appendix C, rate-preserving finite memory on the actual P₁ regime.
Use: the globally checked actual source supplies the nonnegative lag-three
polynomial at every nearby exponent, and its proved strict slope supplies the gap.
-/
namespace polyak.Regularity
noncomputable section
open Growth Spectral Boundary Set Filter
open scoped Topology

/-- The actual P₁ regime has exactly the original rate with one finite memory. -/
theorem memory_rate_eq_p1 {q : ℝ} (hq : 0<q) (hq1 : q<1)
    (hG : GW<Real.cosh (T q)) :
    ∀ᶠ H : ℕ in atTop,
      Growth.FiniteHorizon.growthRate 0 (2*q) (q^2) H=Real.exp (T q) := by
  let z:=1/Real.cosh (T q)
  have hz : z∈Ioo (0 : ℝ) P1.zW :=
    ⟨one_div_pos.mpr (Real.cosh_pos _),one_div_lt_one_div_of_lt (by linarith [GW_bounds.1]) hG⟩
  have ht : Real.cosh (T q)=1/z := by simp [z]
  have ha:=P1.V_analyticAt hz ht
  apply memory_rate_eq_of_boundary (H₀:=3) hq hq1 (by omega)
    ha.differentiableAt.hasDerivAt (abs_lt.mp (P1.abs_deriv_V_lt_one hz ht)).2
  have hn : ∀ᶠ t in 𝓝 (T q),GW<Real.cosh t :=
    Real.continuous_cosh.continuousAt.eventually (lt_mem_nhds hG)
  filter_upwards [hn] with t ht
  let z:=1/Real.cosh t
  have hz : z∈Ioc (0 : ℝ) P1.zW :=
    ⟨one_div_pos.mpr (Real.cosh_pos _),one_div_le_one_div_of_le (by linarith [GW_bounds.1]) ht.le⟩
  have hzm : z≤3/4 := by linarith [hz.2,P1.zW_bounds.2]
  have he : Real.cosh t=1/z := by simp [z]
  have hp:=P1.continuation_physical hz
  have hc:=P1.regularSystem_contacts (P1.continuation_source
    ⟨hz.1.le,hz.2.trans P1.zW_bounds.2.le⟩)
  refine ⟨P1.weights,?_,Real.sinh_nonneg_iff.mpr (V_nonneg t),?_⟩
  · intro n hn
    change n∈({3} : Finset ℕ) at hn
    have hn':=Finset.mem_singleton.mp hn
    omega
  · intro c
    rw [P1.continuation_optimal hz he,Real.sinh_arsinh,he]
    exact P1.dualPolynomial_nonneg hz.1 (by nlinarith [hz.1]) (by rw [←he]; linarith [GW_bounds.1])
      hc.1 hc.2 hp.residual c

/-- The actual condition-number rate is analytic whenever its optimum lies inside P₁. -/
theorem conditionRate_analyticAt_p1 {κ : ℝ} (hκ : 1<κ)
    (hG : GW<Real.cosh (T (Dynamics.conditionQ κ))) : AnalyticAt ℝ conditionRate κ := by
  let z:=1/Real.cosh (T (Dynamics.conditionQ κ))
  have hz : z∈Ioo (0 : ℝ) P1.zW :=
    ⟨one_div_pos.mpr (Real.cosh_pos _),one_div_lt_one_div_of_lt (by linarith [GW_bounds.1]) hG⟩
  have ht : Real.cosh (T (Dynamics.conditionQ κ))=1/z := by simp [z]
  exact conditionRate_analyticAt_of_boundary hκ (P1.V_analyticAt hz ht)
    (ne_of_lt (abs_lt.mp (P1.abs_deriv_V_lt_one hz ht)).2)

end
end polyak.Regularity
