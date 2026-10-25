import polyak.Regularity.Memory

namespace polyak.Regularity
noncomputable section
open Growth Spectral Boundary Set Filter
open scoped Topology

/-- The actual central P₅ family provides bounded-lag dual witnesses on a full
neighborhood of the critical exponent, including its zero parameter. -/
theorem boundary_duals_near_zero :
    ∀ᶠ t in 𝓝 (0 : ℝ),∃ W : DualWeights,
      (∀ n∈W.lags,n ≤ 5) ∧ 0 ≤ Real.sinh (V t) ∧
      ∀ c : Frequency,0 ≤ (dualPolynomial W (Real.sinh (V t)) (Real.cosh t)).eval (c : ℝ) := by
  have hh : Tendsto (fun t : ℝ => Real.cosh t-1) (𝓝 0) (𝓝 0) := by
    have hc : ContinuousAt (fun t : ℝ => Real.cosh t-1) 0 := by fun_prop
    convert hc.tendsto using 1
    norm_num
  filter_upwards [P5.V_eventually_eq_localValue,
    hh.eventually P5.eventually_branch_dual_parameters,
    hh.eventually P5.localBranch_dual_nonneg] with t ht hw hQ
  let h:=Real.cosh t-1
  have hcosh : Real.cosh t=1+h := by dsimp only [h]; ring
  have hnon : 0 ≤ h := by dsimp only [h]; linarith [Real.one_le_cosh t]
  let W:=P5.weights235 (P5.localBranch h 5) (P5.localBranch h 6)
    hw.1.le hw.2.1.le hw.2.2.1.le
  refine ⟨W,?_,?_,?_⟩
  · intro n hn
    change n∈({2,3,5} : Finset ℕ) at hn
    simp only [Finset.mem_insert,Finset.mem_singleton] at hn
    omega
  · exact Real.sinh_nonneg_iff.mpr (V_nonneg t)
  · intro c
    rw [ht,P5.localValue,Real.sinh_arsinh,hcosh]
    change 0 ≤ (dualPolynomial (P5.weights235 _ _ _ _ _) _ _).eval (c : ℝ)
    rw [P5.dualPolynomial_eq_source_of_le (by linarith : (1 : ℝ) ≤ 1+h)]
    unfold P5.branchU
    simp only [add_sub_cancel_left]
    rw [←P5.dualReal_closed]
    exact div_nonneg (hQ hnon c) (P5.commonDenominator_pos (by linarith)).le

/-- In particular the exact threshold rate one is retained by one finite memory. -/
theorem memory_rate_eq_critical :
    ∀ᶠ H : ℕ in atTop,
      Growth.FiniteHorizon.growthRate 0 (2*Threshold.criticalQ) (Threshold.criticalQ^2) H=1 := by
  have ht : T Threshold.criticalQ=0 :=
    (T_eq_zero_iff Threshold.criticalQ_pos Threshold.criticalQ_lt_one).mpr rfl
  have hd : HasDerivAt V 0 (T Threshold.criticalQ) := by
    rw [ht]
    exact V_hasDerivAt_zero
  have hdual : ∀ᶠ t in 𝓝 (T Threshold.criticalQ),∃ W : DualWeights,
      (∀ n∈W.lags,n ≤ 5) ∧ 0 ≤ Real.sinh (V t) ∧
      ∀ c : Frequency,0 ≤ (dualPolynomial W (Real.sinh (V t)) (Real.cosh t)).eval (c : ℝ) := by
    rw [ht]
    exact boundary_duals_near_zero
  simpa only [ht,Real.exp_zero] using memory_rate_eq_of_boundary
    Threshold.criticalQ_pos Threshold.criticalQ_lt_one (by omega : 1 ≤ 5) hd (by norm_num) hdual

end
end polyak.Regularity
