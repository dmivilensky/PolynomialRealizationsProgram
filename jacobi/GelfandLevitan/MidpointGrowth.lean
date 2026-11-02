import jacobi.GelfandLevitan.MidpointCharacteristics

/-!
Article: jacobi, Proposition C.2.
The actual value and derivative midpoint characteristics have the
printed entire growth bound. The genuine reference slope estimate
handles large frequencies and its proved entire frequency dependence
handles a compact disk. The genuine bounded original GL functionals
then transfer the same exponential type to the actual a and b.
Use: midpoint_growth bounds the actual halfSolution norm and original GL correction functionals at every complex frequency, including zero.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference
open scoped Topology
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] solution solutionSlope wave waveSlope transformationKernel

/-- The actual reference wave is bounded uniformly over the original half interval by its genuine midpoint exponential type.
Use: midpoint_growth bounds the actual halfSolution norm and original GL correction functionals at every complex frequency, including zero.
Article: jacobi, Proposition C.2.
Proof: the independently proved original endpoint envelope has t^gamma<=1 on the actual half interval and its actual imaginary-frequency exponential is bounded by the midpoint exponential. -/
theorem reference_half_type {a : ℝ} (ha : -1<a) :
    ∃ A : ℝ,0<A ∧ ∀ omega : ℂ,∀ t∈Icc (0:ℝ) (1/2),
      ‖wave a omega t‖≤A*Real.exp (|omega.im|/2) := by
  -- The positive original endpoint power and the actual spatial exponential are both bounded on the unchanged physical half interval.
  obtain ⟨A,hA,hbound⟩ := wave_global_endpoint_bound ha
  refine ⟨A,hA,fun omega t ht => ?_⟩
  have hg : 0≤gamma a := by linarith [(parameters ha).1]
  have hp : t^(gamma a)≤1 := Real.rpow_le_one ht.1 (by linarith [ht.2]) hg
  calc
    _ ≤ A*t^(gamma a)*Real.exp (t*|omega.im|) := hbound omega t ht
    _ ≤ A*Real.exp (t*|omega.im|) := mul_le_mul_of_nonneg_right
      (by nlinarith : A*t^(gamma a)≤A) (Real.exp_pos _).le
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
      nlinarith [mul_le_mul_of_nonneg_right ht.2 (abs_nonneg omega.im)])) hA.le

/-- The genuine reference midpoint slope has its original full-frequency growth bound, with no excluded energy branch point.
Use: midpoint_growth transfers the same true exponential type to the actual original derivative characteristic b.
Article: jacobi, Proposition C.2.
Proof: on a fixed frequency disk the independently proved actual entire slope is continuous and bounded. Outside the disk the original positive-strip slope estimate applies, and its power 1-gamma is at most the first power because gamma>0. -/
theorem reference_midpointSlope_type {a : ℝ} (ha : -1<a) :
    ∃ B : ℝ,0<B ∧ ∀ omega : ℂ,
      ‖waveSlope a omega (1/2)‖≤B*(1+‖omega‖)*Real.exp (|omega.im|/2) := by
  -- The compact disk and its complement concern the same actual original frequency slope; no square-root differentiability is used.
  obtain ⟨A,hA,hbound⟩ := waveSlope_away_bound ha (d := 1/4) (by norm_num)
  have hc : Continuous (fun omega : ℂ => waveSlope a omega (1/2)) :=
    continuous_iff_continuousAt.mpr (fun omega => (waveSlope_frequency_analytic ha (by norm_num) omega).continuousAt)
  obtain ⟨M,hM⟩ := (isCompact_closedBall (0:ℂ) 4).exists_bound_of_continuousOn hc.continuousOn
  let B := A+|M|+1
  have hB : 0<B := by dsimp [B]; positivity
  refine ⟨B,hB,fun omega => ?_⟩
  have hE : 1≤Real.exp (|omega.im|/2) := Real.one_le_exp (by positivity)
  by_cases hR : 4≤‖omega‖
  · have hb := hbound omega (by norm_num; exact hR) (1/2) (by norm_num)
    have hg : 1-gamma a≤(1:ℝ) := by linarith [(parameters ha).1]
    have hp : ‖omega‖^(1-gamma a)≤‖omega‖ := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (show 1≤‖omega‖ by linarith) hg
    have hAB : A≤B := by dsimp [B]; linarith [abs_nonneg M]
    calc
      _ ≤ A*‖omega‖^(1-gamma a)*Real.exp ((1/2)*|omega.im|) := hb
      _ ≤ B*(1+‖omega‖)*Real.exp (|omega.im|/2) := by
        rw [show (1/2)*|omega.im|=|omega.im|/2 by ring]
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact (mul_le_mul_of_nonneg_left hp hA.le).trans (by nlinarith [norm_nonneg omega])
  · have hb := hM omega (by simpa only [Metric.mem_closedBall,dist_zero_right] using (le_of_not_ge hR))
    calc
      _ ≤ M := hb
      _ ≤ B := (le_abs_self M).trans (by dsimp [B]; linarith)
      _ ≤ B*(1+‖omega‖)*Real.exp (|omega.im|/2) := by
        have hBT : B≤B*(1+‖omega‖) := le_mul_of_one_le_right hB.le (by linarith [norm_nonneg omega])
        exact hBT.trans (le_mul_of_one_le_right (by positivity) hE)

/-- The actual original midpoint value and genuine derivative characteristics satisfy precisely the printed full complex-frequency growth estimate.
Use: supplies the actual growth hypothesis for the subsequent original canonical-product and midpoint boundary-condition arguments of the general target-operator Proposition C.2.
Article: jacobi, Proposition C.2.
Proof: bound the actual original halfSolution in uniform norm using the genuine reference envelope. The actual value characteristic uses the proved original GL norm estimate. The actual derivative characteristic uses its proved reference-plus-bounded-functional identity and the independently proved original reference slope bound. -/
theorem midpoint_growth {a : ℝ} (ha : -1<a) :
    ∃ C : ℝ,0<C ∧ ∀ omega : ℂ,
      ‖midpointValue a ha ((jacobi.Jacobi.endpointCorrection a:ℂ)+omega^2)‖+
        ‖midpointSlope a ha ((jacobi.Jacobi.endpointCorrection a:ℂ)+omega^2)‖≤
      C*(1+‖omega‖)*Real.exp (|omega.im|/2) := by
  -- Every constant is a norm of the actual original inverse data or comes from the independently proved original reference estimates.
  obtain ⟨A,hA,hf⟩ := reference_half_type ha
  obtain ⟨B,hB,hb⟩ := reference_midpointSlope_type ha
  let W : ℝ := |kernelDiagonal a ha halfMidpoint|+
    ‖coefficientFunctional (midpointDerivativeVector a ha)‖
  let P : ℝ := A*(1+‖solutionRow a ha halfMidpoint‖)
  refine ⟨B+P+W*A,by dsimp [P,W]; positivity,fun omega => ?_⟩
  let z : ℂ := (jacobi.Jacobi.endpointCorrection a:ℂ)+omega^2
  let E : ℝ := Real.exp (|omega.im|/2)
  have hE : 0≤E := (Real.exp_pos _).le
  have hsol (r : ℝ) (hr : r∈Icc (0:ℝ) (1/2)) : ‖solution a z r‖≤A*E := by
    rw [solution_eq_wave a (show omega^2=z-(jacobi.Jacobi.endpointCorrection a:ℂ) by dsimp [z]; ring)]
    exact hf omega r hr
  have hnorm : ‖halfSolution a ha z‖≤A*E := by
    apply ((halfSolution a ha z).norm_le (mul_nonneg hA.le hE)).mpr
    intro r
    rw [halfSolution_apply]
    exact hsol _ (halfTime_mem r)
  have hval : ‖midpointValue a ha z‖≤P*E := by
    exact (transformedSolution_norm_le a ha halfMidpoint z (mul_nonneg hA.le hE) hsol).trans_eq (by dsimp [P]; ring)
  have hslope : ‖midpointSlope a ha z‖≤B*(1+‖omega‖)*E+W*A*E := by
    rw [midpointSlope_reference]
    have h0 : ‖solutionSlope a z (1/2)‖≤B*(1+‖omega‖)*E := by
      rw [solutionSlope_eq_wave a (by norm_num)
        (show omega^2=z-(jacobi.Jacobi.endpointCorrection a:ℂ) by dsimp [z]; ring)]
      exact hb omega
    have h1 : ‖(kernelDiagonal a ha halfMidpoint:ℂ)*solution a z (1/2)‖≤
        |kernelDiagonal a ha halfMidpoint| * (A*E) := by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hsol _ (by norm_num)) (abs_nonneg _)
    have h2 := (coefficientFunctional (midpointDerivativeVector a ha)).le_opNorm (halfSolution a ha z)
    have h2' := h2.trans (mul_le_mul_of_nonneg_left hnorm (norm_nonneg _))
    exact ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add h0 h1)) h2')).trans_eq
      (by dsimp [W]; ring)
  have hP : 0≤P+W*A := by dsimp [P,W]; positivity
  have hscale : (P+W*A)*E≤(P+W*A)*(1+‖omega‖)*E :=
    mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hP (by linarith [norm_nonneg omega])) hE
  exact (add_le_add hval hslope).trans (by dsimp [z,E] at *; nlinarith [hscale])

end
end jacobi.GelfandLevitan
