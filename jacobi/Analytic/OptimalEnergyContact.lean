import jacobi.Analytic.QuadraticContact

/-!
Article: jacobi, Theorem 4.2.
The actual beta-independent Young/upper squeeze gives one quadratic
error bound for every beta. Thus the original optimum, with no assumed
order regularity or persymmetric minimizer, has derivative -13/75 at U.
Use: states genuine differentiability of the article's e(alpha,beta) as an ordinary function.
-/
namespace jacobi.Analytic
noncomputable section
open Set Filter Asymptotics jacobi.Parameter jacobi.Comparison jacobi.GelfandLevitan
open scoped Topology
set_option maxHeartbeats 1000000

/-- The original full Jacobi-fibre limiting optimum as a real function of its first order at fixed admissible second order.
Use: states genuine differentiability of the article's e(alpha,beta) as an ordinary function.
Article: jacobi, Theorem 4.2.
The zero exterior value merely totalizes the function outside alpha>-1. -/
def originalOptimalEnergy (b : ℝ) (hb : -1<b) (a : ℝ) : ℝ :=
  if ha : -1<a then realOptimalEnergy a b ha hb else 0

/-- On its admissible interval the parameter function is precisely the original full-fibre optimum.
Use: transfers the actual global source bounds and exact U value to the differentiated function.
Article: jacobi, Theorem 4.2.
Proof: select its genuine admissible branch. -/
theorem originalOptimalEnergy_eq {a b : ℝ} (hb : -1<b) (ha : -1<a) :
    originalOptimalEnergy b hb a=realOptimalEnergy a b ha hb := by
  simp only [originalOptimalEnergy,dite_eq_left ha]

/-- The original full-fibre optimum has exactly the original upper value two fifteenths at U, for every beta.
Use: compares derivatives of the same true functions at their common source value.
Article: jacobi, Theorem 4.2.
Proof: the actual Young and upper bounds coincide at their independently proved exact rational value. -/
theorem originalOptimalEnergy_U {b : ℝ} (hb : -1<b) :
    originalOptimalEnergy b hb (1/2)=originalPersymmetricEnergy (1/2) := by
  have ha : -1<(1/2:ℝ) := by norm_num
  rw [originalOptimalEnergy_eq hb ha,originalPersymmetricEnergy_eq ha,half_sine_persymmetricConstant]
  have hs := young_optimal_upper_bounds ha hb
  rw [youngLower_U,half_sine_persymmetricConstant] at hs
  exact le_antisymm hs.2 hs.1

/-- One genuine quadratic error bound controls both original full-fibre squeeze errors for all beta simultaneously near U.
Use: proves the printed uniform-in-beta approximation of the optimum by c_star and its differentiability without any regularity assumption on the optimizer.
Article: jacobi, Theorem 4.2.
Proof: take the actual analytic gap's proved Taylor bound and enlarge its coefficient to a positive constant. The original beta-independent squeeze places each of its two errors between zero and that same gap throughout a genuine common neighborhood. -/
theorem optimalEnergy_contact_uniform :
    ∃ C : ℝ,0<C ∧ ∀ᶠ a in 𝓝 (1/2:ℝ),-1<a ∧
      (0≤upperYoungGap a ∧ upperYoungGap a≤C*(a-1/2)^2) ∧
      ∀ b:ℝ,∀ hb:-1<b,
        (0≤originalPersymmetricEnergy a-originalOptimalEnergy b hb a ∧
          originalPersymmetricEnergy a-originalOptimalEnergy b hb a≤C*(a-1/2)^2) ∧
        (0≤originalOptimalEnergy b hb a-youngLower a ∧
          originalOptimalEnergy b hb a-youngLower a≤C*(a-1/2)^2) := by
  -- The neighborhood and coefficient are chosen before beta, from the actual alpha-only analytic gap.
  obtain ⟨M,hM⟩ := upperYoungGap_quadratic.bound
  refine ⟨|M|+1,by positivity,?_⟩
  filter_upwards [hM,Ioi_mem_nhds (by norm_num : -1<(1/2:ℝ))] with a hM ha
  have h0 : 0≤upperYoungGap a := by
    rw [upperYoungGap,originalPersymmetricEnergy_eq ha]
    exact upper_young_gap_nonneg ha
  have hbound : upperYoungGap a≤(|M|+1)*(a-1/2)^2 := by
    rw [Real.norm_eq_abs,abs_of_nonneg h0,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)] at hM
    exact hM.trans (mul_le_mul_of_nonneg_right (by linarith [le_abs_self M]) (sq_nonneg _))
  refine ⟨ha,⟨h0,hbound⟩,fun b hb => ?_⟩
  have hs := young_optimal_upper_bounds ha hb
  rw [originalOptimalEnergy_eq hb ha,originalPersymmetricEnergy_eq ha]
  rw [upperYoungGap,originalPersymmetricEnergy_eq ha] at hbound
  exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩

/-- The original full-fibre optimum equals the original upper function up to a genuine quadratic error at U.
Use: its error is little-o of alpha-1/2, which transfers the actual upper derivative to the possibly nonsmooth optimum.
Article: jacobi, Theorem 4.2.
Proof: specialize the stronger proved beta-uniform error bound and rewrite the absolute difference using its known nonnegative orientation. -/
theorem originalOptimalEnergy_upper_quadratic {b : ℝ} (hb : -1<b) :
    (fun a => originalOptimalEnergy b hb a-originalPersymmetricEnergy a)
      =O[𝓝 (1/2:ℝ)] (fun a => (a-1/2)^2) := by
  obtain ⟨C,_,he⟩ := optimalEnergy_contact_uniform
  apply IsBigO.of_bound C
  filter_upwards [he] with a ha
  have hh := (ha.2.2 b hb).1
  rw [norm_sub_rev,Real.norm_eq_abs,abs_of_nonneg hh.1,
    Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact hh.2

/-- The original optimal-to-upper error has one absolute quadratic bound for every beta on the same neighborhood.
Use: states the printed uniform-in-beta big-O conclusion explicitly, with its quantifiers outside the second parameter.
Article: jacobi, Theorem 4.2.
Proof: use the proved simultaneous two-error squeeze and orient the absolute difference by its genuine nonnegative upper-minus-optimal sign. -/
theorem originalOptimalEnergy_uniform_upper :
    ∃ C:ℝ,0<C ∧ ∀ᶠ a in 𝓝 (1/2:ℝ),∀ b:ℝ,∀ hb:-1<b,
      ‖originalOptimalEnergy b hb a-originalPersymmetricEnergy a‖≤C*(a-1/2)^2 := by
  obtain ⟨C,hC,he⟩ := optimalEnergy_contact_uniform
  refine ⟨C,hC,?_⟩
  filter_upwards [he] with a ha
  intro b hb
  have hh := (ha.2.2 b hb).1
  rw [norm_sub_rev,Real.norm_eq_abs,abs_of_nonneg hh.1]
  exact hh.2

/-- For every original admissible beta, the genuine full-fibre optimal energy is differentiable at U with exactly the printed rational derivative.
Use: closes the optimizer-independent derivative conclusion of Theorem 4.2, without assuming an optimal density or analytic optimizer family.
Article: jacobi, Theorem 4.2.
Proof: the proved quadratic difference from the actual analytic upper function is little-o of the first-order increment. Add it to the true upper derivative remainder; the exact common value at U gives precisely the derivative criterion for the original optimal energy. -/
theorem originalOptimalEnergy_hasDerivAt_U {b : ℝ} (hb : -1<b) :
    HasDerivAt (originalOptimalEnergy b hb) (-13/75) (1/2) := by
  -- Only a scalar squeeze is used; the original optimum is not assumed differentiable beforehand.
  have hpow : (fun a:ℝ => (a-1/2)^2)=o[𝓝 (1/2:ℝ)] (fun a => a-1/2) := by
    simpa only [Real.norm_eq_abs,sq_abs] using
      (isLittleO_pow_sub_sub (1/2:ℝ) (by norm_num : 1<2))
  have he := (originalOptimalEnergy_upper_quadratic hb).trans_isLittleO hpow
  have hu := originalPersymmetricEnergy_hasDerivAt_U.isLittleO
  apply hasDerivAt_iff_isLittleO.mpr
  have hsum : (fun a:ℝ => originalOptimalEnergy b hb a-originalOptimalEnergy b hb (1/2)-
      (a-1/2) • (-13/75:ℝ))=
      (fun a:ℝ => (originalOptimalEnergy b hb a-originalPersymmetricEnergy a)+
        (originalPersymmetricEnergy a-originalPersymmetricEnergy (1/2)-(a-1/2) • (-13/75:ℝ))) := by
    funext a
    rw [originalOptimalEnergy_U hb]
    simp only [smul_eq_mul]
    ring
  rw [hsum]
  exact he.add hu

/-- The original article's complete analyticity and U-contact theorem, with genuine full-fibre energies and a uniform second-parameter error bound.
Use: supplies all of Theorem 4.2 directly from the original article data, with no analytic continuation, optimizer regularity or derivative premises.
Article: jacobi, Theorem 4.2.
Proof: combine original upper real analyticity, the proved global Young/optimal/upper squeeze, the actual analytic quadratic contact, its stronger beta-uniform bound, and the independently proved exact derivatives of all three original functions. -/
theorem theorem_C :
    AnalyticOnNhd ℝ originalPersymmetricEnergy (Ioi (-1)) ∧
      (∀ a b:ℝ,∀ ha:-1<a,∀ hb:-1<b,
        youngLower a≤realOptimalEnergy a b ha hb ∧
          realOptimalEnergy a b ha hb≤persymmetricConstant a ha) ∧
      upperYoungGap=O[𝓝 (1/2:ℝ)] (fun a => (a-1/2)^2) ∧
      (∃ C:ℝ,0<C ∧ ∀ᶠ a in 𝓝 (1/2:ℝ),∀ b:ℝ,∀ hb:-1<b,
        ‖originalOptimalEnergy b hb a-originalPersymmetricEnergy a‖≤C*(a-1/2)^2) ∧
      HasDerivAt originalPersymmetricEnergy (-13/75) (1/2) ∧
      HasDerivAt youngLower (-13/75) (1/2) ∧
      ∀ b:ℝ,∀ hb:-1<b,HasDerivAt (originalOptimalEnergy b hb) (-13/75) (1/2) :=
  ⟨originalPersymmetricEnergy_realAnalytic,fun _ _ ha hb => young_optimal_upper_bounds ha hb,
    upperYoungGap_quadratic,originalOptimalEnergy_uniform_upper,
    originalPersymmetricEnergy_hasDerivAt_U,youngLower_hasDerivAt_U,
    fun _ hb => originalOptimalEnergy_hasDerivAt_U hb⟩

end
end jacobi.Analytic
