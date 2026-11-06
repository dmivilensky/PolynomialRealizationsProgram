import chebyshev1.Nonlinear.CubicSharpness
import chebyshev1.Chebyshev.DriftBudgetLimits
import Mathlib.Analysis.SumIntegralComparisons

/-! Exact prefix coefficient and its integral scaling. -/
namespace chebyshev1.Nonlinear
noncomputable section
open Polynomial Polynomial.Chebyshev Real Set MeasureTheory
open scoped BigOperators Interval

theorem prefix_leadingRadius (I : SpectralInterval) (s : ℕ) :
    leadingRadius Prefix.jacobiData I s = I.epsilon s := by
  cases s with
  | zero => simp [leadingRadius, SpectralInterval.epsilon]
  | succ s =>
    rw [leadingRadius, JacobiData.den, Prefix.jacobi_leading]
    simp only [eval_mul, eval_C, T_eval_one, mul_one]
    dsimp [SpectralInterval.epsilon, SpectralInterval.den]
    field_simp

theorem prefix_endpointProfile_zero {N : ℕ} (hN : 0 < N) :
    Prefix.jacobiData.endpointProfile N 0 = (N:ℝ) := by
  rw [JacobiData.endpointProfile, JacobiData.leading_zero,
    Prefix.jacobi_interior 1 (N-1) (by omega), Prefix.jacobi_terminal hN]
  simp only [eval_one, eval_mul, eval_C, T_eval_one, mul_one, U_eval_one, Int.cast_natCast,
    one_mul]
  have hn : ((N-1:ℕ):ℝ)+1 = (N:ℝ) := by exact_mod_cast Nat.sub_add_cancel hN
  have hp : (2:ℝ)^N = 2^(N-1)*2 := by rw [← pow_succ, Nat.sub_add_cancel hN]
  rw [hn, one_div_pow, hp]
  field_simp

theorem prefix_endpointProfile_pos {N s : ℕ} (hN : 0 < N) (hs : s < N) (hs0 : 0 < s) :
    Prefix.jacobiData.endpointProfile N s = 2*((N:ℝ)-(s:ℝ)) := by
  rw [JacobiData.endpointProfile, Prefix.jacobi_terminal hs0,
    Prefix.jacobi_interior (s+1) (N-(s+1)) (by omega), Prefix.jacobi_terminal hN]
  simp only [eval_mul, eval_C, T_eval_one, mul_one, U_eval_one, Int.cast_natCast]
  have hn : ((N-(s+1):ℕ):ℝ)+1 = (N:ℝ)-(s:ℝ) := by
    have hh : N-(s+1)+1+s=N := by omega
    have hh' : ((N-(s+1):ℕ):ℝ)+1+(s:ℝ) = (N:ℝ) := by exact_mod_cast hh
    linarith
  have hp : (2:ℝ)^N = 2^s*2^(N-(s+1))*2 := by
    rw [← pow_add, ← pow_succ]
    congr 1
    omega
  rw [hn, one_div_pow, hp]
  field_simp

/-- A finite sum requiring no asymptotic approximation. -/
theorem prefix_secondOrderCoefficient_sum (I : SpectralInterval) {N : ℕ} (hN : 0 < N) :
    secondOrderCoefficient Prefix.jacobiData I N =
      2*(∑ s ∈ Finset.range N, ((N:ℝ)-(s:ℝ))*I.epsilon s)-(N:ℝ) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  have he0 : I.epsilon 0 = 1 := by simp [SpectralInterval.epsilon]
  rw [secondOrderCoefficient, Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [prefix_endpointProfile_zero (Nat.succ_pos n), prefix_leadingRadius,
    he0, mul_one, Nat.cast_zero, sub_zero]
  have he : (∑ s ∈ Finset.range n,
      Prefix.jacobiData.endpointProfile (n+1) (s+1)*I.epsilon (s+1)) =
      2*∑ s ∈ Finset.range n, (((n+1:ℕ):ℝ)-(s+1:ℝ))*I.epsilon (s+1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    rw [prefix_endpointProfile_pos (Nat.succ_pos n) (by have := Finset.mem_range.mp hs; omega)
      (Nat.succ_pos s)]
    push_cast
    ring
  rw [he]
  push_cast
  ring

/-- The integral profile in the simultaneous horizon/condition-number scaling. -/
def prefixSecondOrderIntegrand (a t : ℝ) : ℝ := (1-t)/cosh (a*t)

def prefixSecondOrderIntegral (a : ℝ) : ℝ := ∫ t in (0:ℝ)..1, prefixSecondOrderIntegrand a t

def prefixSecondOrderRiemann (a : ℝ) (N : ℕ) : ℝ :=
  (∑ s ∈ Finset.range N, prefixSecondOrderIntegrand a ((s:ℝ)/N))/(N:ℝ)

theorem prefixSecondOrderIntegrand_antitone {a : ℝ} (ha : 0 ≤ a) :
    AntitoneOn (prefixSecondOrderIntegrand a) (Icc 0 1) := by
  intro x hx y hy hxy
  have hc : cosh (a*x) ≤ cosh (a*y) := by
    apply cosh_le_cosh.mpr
    rw [abs_of_nonneg (mul_nonneg ha hx.1), abs_of_nonneg (mul_nonneg ha hy.1)]
    exact mul_le_mul_of_nonneg_left hxy ha
  exact (div_le_div_of_nonneg_left (sub_nonneg.mpr hy.2) (cosh_pos _) hc).trans
    (div_le_div_of_nonneg_right (by linarith : 1-y ≤ 1-x) (cosh_pos _).le)

/-- The left Riemann sum has an error at most one mesh width, uniformly in the
nonnegative scale parameter. -/
theorem prefixSecondOrderRiemann_error {a : ℝ} (ha : 0 ≤ a) {N : ℕ} (hN : 0 < N) :
    0 ≤ prefixSecondOrderRiemann a N-prefixSecondOrderIntegral a ∧
      prefixSecondOrderRiemann a N-prefixSecondOrderIntegral a ≤ 1/(N:ℝ) := by
  have hN' : 0 < (N:ℝ) := Nat.cast_pos.mpr hN
  let F := fun x : ℝ => prefixSecondOrderIntegrand a (x/(N:ℝ))
  have hanti : AntitoneOn F (Icc 0 (N:ℝ)) := by
    intro x hx y hy hxy
    apply prefixSecondOrderIntegrand_antitone ha
    · exact ⟨div_nonneg hx.1 hN'.le, (div_le_one hN').mpr hx.2⟩
    · exact ⟨div_nonneg hy.1 hN'.le, (div_le_one hN').mpr hy.2⟩
    · exact div_le_div_of_nonneg_right hxy hN'.le
  have hupper := AntitoneOn.integral_le_sum (a := N) (x₀ := 0) (by simpa using hanti)
  have hlower := AntitoneOn.sum_le_integral (a := N) (x₀ := 0) (by simpa using hanti)
  simp only [zero_add] at hupper hlower
  have hInt : (∫ x in (0:ℝ)..(N:ℝ), F x) =
      (N:ℝ)*prefixSecondOrderIntegral a := by
    rw [intervalIntegral.integral_comp_div _ hN'.ne']
    simp only [zero_div, div_self hN'.ne', smul_eq_mul, prefixSecondOrderIntegral]
  have hF0 : F 0 = 1 := by simp [F, prefixSecondOrderIntegrand]
  have hFN : F N = 0 := by simp [F, prefixSecondOrderIntegrand, hN'.ne']
  have hsum : (∑ s ∈ Finset.range N, F ((s+1:ℕ):ℝ)) =
      (∑ s ∈ Finset.range N, F (s:ℝ))-1 := by
    have hleft := Finset.sum_range_succ' (fun s : ℕ => F (s:ℝ)) N
    have hright := Finset.sum_range_succ (fun s : ℕ => F (s:ℝ)) N
    simp only [Nat.cast_zero] at hleft
    rw [hF0] at hleft
    rw [hFN] at hright
    linarith
  rw [hInt] at hupper hlower
  rw [hsum] at hlower
  change 0 ≤ (∑ s ∈ Finset.range N, F (s:ℝ))/(N:ℝ)-prefixSecondOrderIntegral a ∧
    (∑ s ∈ Finset.range N, F (s:ℝ))/(N:ℝ)-prefixSecondOrderIntegral a ≤ 1/(N:ℝ)
  constructor
  · apply sub_nonneg.mpr
    exact (le_div_iff₀ hN').mpr (by simpa only [mul_comm] using hupper)
  · apply (le_div_iff₀ hN').mpr
    field_simp
    nlinarith

theorem prefixSecondOrderIntegral_continuous : Continuous prefixSecondOrderIntegral := by
  have hc : Continuous (Function.uncurry prefixSecondOrderIntegrand) :=
    (continuous_const.sub continuous_snd).div
      (continuous_cosh.comp (continuous_fst.mul continuous_snd)) (fun p => (cosh_pos (p.1*p.2)).ne')
  have hi := continuous_parametric_integral_of_continuous (μ := volume) hc
    (isCompact_Icc : IsCompact (Icc (0:ℝ) 1))
  have he : prefixSecondOrderIntegral = fun a : ℝ =>
      ∫ t in Icc (0:ℝ) 1, prefixSecondOrderIntegrand a t := by
    funext a
    rw [prefixSecondOrderIntegral, intervalIntegral.integral_of_le (by norm_num),
      ← integral_Icc_eq_integral_Ioc]
  rw [he]
  exact hi

theorem prefixSecondOrderRiemann_limit {α : Type*} {l : Filter α}
    {a : α → ℝ} {N : α → ℕ} {a0 : ℝ}
    (ha : ∀ j, 0 ≤ a j) (hN : Filter.Tendsto N l Filter.atTop)
    (ha0 : Filter.Tendsto a l (nhds a0)) :
    Filter.Tendsto (fun j => prefixSecondOrderRiemann (a j) (N j)) l
      (nhds (prefixSecondOrderIntegral a0)) := by
  have hI := (prefixSecondOrderIntegral_continuous.tendsto a0).comp ha0
  have hmesh := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hN
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hI (by simpa using hI.add hmesh)
  · filter_upwards [hN.eventually (Filter.eventually_gt_atTop 0)] with j hj
    exact sub_nonneg.mp (prefixSecondOrderRiemann_error (ha j) hj).1
  · filter_upwards [hN.eventually (Filter.eventually_gt_atTop 0)] with j hj
    simpa only [add_comm, one_div] using
      (sub_le_iff_le_add).mp (prefixSecondOrderRiemann_error (ha j) hj).2

theorem prefix_secondOrderCoefficient_scaled (I : SpectralInterval) {N : ℕ} (hN : 0 < N) :
    secondOrderCoefficient Prefix.jacobiData I N / ((N:ℝ)*sqrt I.kappa) =
      2*((N:ℝ)/sqrt I.kappa)*prefixSecondOrderRiemann ((N:ℝ)*arcosh I.eta) N-
        1/sqrt I.kappa := by
  have hn : (N:ℝ) ≠ 0 := (Nat.cast_pos.mpr hN).ne'
  have hk : sqrt I.kappa ≠ 0 := (sqrt_pos.mpr (lt_trans zero_lt_one I.kappa_gt_one)).ne'
  have hterm (s : ℕ) : ((N:ℝ)-(s:ℝ))*I.epsilon s =
      (N:ℝ)*prefixSecondOrderIntegrand ((N:ℝ)*arcosh I.eta) ((s:ℝ)/N) := by
    dsimp [prefixSecondOrderIntegrand, SpectralInterval.epsilon]
    rw [I.den_cosh_arcosh]
    rw [show (N:ℝ)*arcosh I.eta*((s:ℝ)/N) = (s:ℝ)*arcosh I.eta by field_simp]
    field_simp
  rw [prefix_secondOrderCoefficient_sum I hN]
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  dsimp [prefixSecondOrderRiemann]
  field_simp

/-- Simultaneous large-condition and finite scaled-horizon asymptotics. -/
theorem prefix_secondOrderCoefficient_limit {α : Type*} {l : Filter α}
    {I : α → SpectralInterval} {N : α → ℕ} {tau : ℝ} (htau : 0 < tau)
    (hK : Filter.Tendsto (fun j => (I j).kappa) l Filter.atTop)
    (hscale : Filter.Tendsto (fun j => (N j:ℝ)/sqrt (I j).kappa) l (nhds tau)) :
    Filter.Tendsto (fun j => secondOrderCoefficient Prefix.jacobiData (I j) (N j) /
      ((N j:ℝ)*sqrt (I j).kappa)) l
      (nhds (2*tau*prefixSecondOrderIntegral (2*tau))) := by
  have hsqrt := tendsto_sqrt_atTop.comp hK
  have hnreal : Filter.Tendsto (fun j => (N j:ℝ)) l Filter.atTop := by
    apply (hscale.pos_mul_atTop htau hsqrt).congr
    intro j
    exact div_mul_cancel₀ _ (sqrt_pos.mpr (lt_trans zero_lt_one (I j).kappa_gt_one)).ne'
  have hN : Filter.Tendsto N l Filter.atTop := by
    apply Filter.tendsto_atTop.mpr
    intro b
    filter_upwards [hnreal.eventually_ge_atTop (b:ℝ)] with j hj
    exact_mod_cast hj
  have harg : Filter.Tendsto (fun j => (N j:ℝ)*arcosh (I j).eta) l (nhds (2*tau)) := by
    have hh := hscale.mul (SpectralInterval.arcosh_eta_scaled_limit hK)
    simp only [mul_comm tau 2] at hh
    apply hh.congr
    intro j
    field_simp [(sqrt_pos.mpr (lt_trans zero_lt_one (I j).kappa_gt_one)).ne']
  have hR := prefixSecondOrderRiemann_limit
    (fun j => mul_nonneg (Nat.cast_nonneg _) (arcosh_nonneg (I j).eta_gt_one.le)) hN harg
  have hzero : Filter.Tendsto (fun j => 1/sqrt (I j).kappa) l (nhds 0) :=
    tendsto_const_nhds.div_atTop hsqrt
  have hh := ((hscale.const_mul 2).mul hR).sub hzero
  simp only [sub_zero] at hh
  apply hh.congr'
  filter_upwards [hN.eventually_gt_atTop 0] with j hj
  exact (prefix_secondOrderCoefficient_scaled (I j) hj).symm

end
end chebyshev1.Nonlinear
