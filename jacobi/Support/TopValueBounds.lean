import jacobi.Support.Volterra
import jacobi.Support.TopScaleBounds
import jacobi.Support.SineProductBounds

/-!
Article: jacobi, Appendix C.3 (top-node polynomials).
The genuine original top-node support polynomial has the full positive
two-sided power bound (m+1)^gamma on the printed growing range. The
proof uses the same actual spectral polynomial, its exact original
sine-product factorization and the complete uniform sine-product lemma.
Use: topValue_bounds takes its actual positive square root and supplies the reference-solution bounds for the genuine support Volterra kernel.
-/
namespace jacobi.Support
noncomputable section
open Real Filter jacobi.Reference
open scoped Topology

/-- The genuine original squared top-node support value has the printed uniform two-sided power growth on the full original growing half chain.
Use: topValue_bounds takes its actual positive square root and supplies the reference-solution bounds for the genuine support Volterra kernel.
Article: jacobi, Appendix C.3 (top-node polynomials).
Proof: multiply the proved original linear sine-scale bound, both original endpoint sine-product power bounds and the original total-exponent sine-product bound. Their exact exponent sum is 2*gamma_alpha. Every factor and denominator is genuinely positive. -/
theorem topValue_sq_bounds {a b : ℝ} (ha:-1<a) (hb:-1<b) :
    ∃c C:ℝ,0<c ∧ 0<C ∧ ∀ᶠn:ℕ in atTop,∀m:ℕ,2*m≤n+6→
      c*((m:ℝ)+1)^(2*gamma a)≤(topValue a b ha hb n m)^2 ∧
      (topValue a b ha hb n m)^2≤C*((m:ℝ)+1)^(2*gamma a) := by
  -- The actual finite dimension is n+1; the shared degree threshold is shifted exactly once for all original sine-product estimates.
  have hg := parameter_pos ha hb
  obtain ⟨c₀,C₀,hc₀,hC₀,h₀⟩ := topScale_bounds ha hb
  obtain ⟨c₁,C₁,hc₁,hC₁,h₁⟩ := support_sineProduct_bounds a b (show 0<gamma a+1/2 by linarith [hg.1])
  obtain ⟨c₂,C₂,hc₂,hC₂,h₂⟩ := support_sineProduct_bounds a b (show 0<gamma b+1/2 by linarith [hg.2.1])
  obtain ⟨c₃,C₃,hc₃,hC₃,h₃⟩ := support_sineProduct_bounds a b (show 0<2*averageGamma a b by linarith [hg.2.2])
  refine ⟨c₀*c₁*c₃/C₂,C₀*C₁*C₃/c₂,by positivity,by positivity,?_⟩
  filter_upwards [(tendsto_add_atTop_nat 1).eventually h₀,(tendsto_add_atTop_nat 1).eventually h₁,
    (tendsto_add_atTop_nat 1).eventually h₂,(tendsto_add_atTop_nat 1).eventually h₃,
    eventually_ge_atTop (6:ℕ)] with n hn₀ hn₁ hn₂ hn₃ hlarge
  intro m hm
  have hm' : m≤n := by omega
  have hmn : 2*m≤n+1+6 := by omega
  obtain ⟨hl₀,hu₀⟩ := hn₀ m hmn
  obtain ⟨hl₁,hu₁⟩ := hn₁.1 m hmn
  obtain ⟨hl₂,hu₂⟩ := hn₂.1 m hmn
  obtain ⟨hl₃,hu₃⟩ := hn₃.1 m hmn
  let x : ℝ := (m:ℝ)+1
  have hx : 0<x := by dsimp [x]; positivity
  have hs₀ : 0≤sin (((m:ℝ)+averageGamma a b)*step a b (n+1))/sin (averageGamma a b*step a b (n+1)) :=
    (by positivity : 0≤c₀*x).trans hl₀
  have hs₁ : 0<sineProduct (step a b (n+1)) (gamma a+1/2) m := lt_of_lt_of_le (by positivity) hl₁
  have hs₂ : 0<sineProduct (step a b (n+1)) (gamma b+1/2) m := lt_of_lt_of_le (by positivity) hl₂
  have hs₃ : 0<sineProduct (step a b (n+1)) (2*averageGamma a b) m := lt_of_lt_of_le (by positivity) hl₃
  have hrl := div_le_div₀ hs₁.le hl₁ hs₂ hu₂
  have hru := div_le_div₀ (by positivity : 0≤C₁*x^(gamma a+1/2-1)) hu₁ (by positivity : 0<c₂*x^(gamma b+1/2-1)) hl₂
  have hlo := mul_le_mul (mul_le_mul hl₀ hrl (by positivity) hs₀) hl₃ (by positivity) (mul_nonneg hs₀ (div_pos hs₁ hs₂).le)
  have hhi := mul_le_mul (mul_le_mul hu₀ hru (div_pos hs₁ hs₂).le (by positivity)) hu₃ hs₃.le (by positivity)
  have hexp : x*(x^(gamma a+1/2-1)/x^(gamma b+1/2-1))*x^(2*averageGamma a b-1)=x^(2*gamma a) := by
    rw [← Real.rpow_sub hx]
    calc
      _ = x^(1:ℝ)*x^((gamma a+1/2-1)-(gamma b+1/2-1))*x^(2*averageGamma a b-1) := by rw [Real.rpow_one]
      _ = x^(1+((gamma a+1/2-1)-(gamma b+1/2-1))+(2*averageGamma a b-1)) := by
        rw [Real.rpow_add hx,Real.rpow_add hx]
      _ = _ := by congr 1; dsimp [averageGamma]; ring
  rw [show topValue a b ha hb n m^2=
    (sin (((m:ℝ)+averageGamma a b)*step a b (n+1))/sin (averageGamma a b*step a b (n+1)))*
      (sineProduct (step a b (n+1)) (gamma a+1/2) m/sineProduct (step a b (n+1)) (gamma b+1/2) m)*
      sineProduct (step a b (n+1)) (2*averageGamma a b) m from naturalPolynomial_top_sineProducts ha hb hm']
  constructor
  · calc
      _ = c₀*c₁*c₃/C₂*(x*(x^(gamma a+1/2-1)/x^(gamma b+1/2-1))*x^(2*averageGamma a b-1)) := by rw [hexp]
      _ = (c₀*x)*(c₁*x^(gamma a+1/2-1)/(C₂*x^(gamma b+1/2-1)))*(c₃*x^(2*averageGamma a b-1)) := by ring
      _ ≤ _ := hlo
  · calc
      _ ≤ (C₀*x)*(C₁*x^(gamma a+1/2-1)/(c₂*x^(gamma b+1/2-1)))*(C₃*x^(2*averageGamma a b-1)) := hhi
      _ = C₀*C₁*C₃/c₂*(x*(x^(gamma a+1/2-1)/x^(gamma b+1/2-1))*x^(2*averageGamma a b-1)) := by ring
      _ = _ := by rw [hexp]

/-- The actual positive support top-node polynomial has the full printed uniform two-sided power bounds, including every small original index.
Use: the genuine reduction-of-order Volterra kernel, its factorial iteration bounds and support edge convergence all use this same original positive reference solution.
Article: jacobi, Appendix C.3 (top-node polynomials).
Proof: the original top-node values are genuinely positive and their squares have the proved original power bounds. The positive square roots of those constants and the exact identity ((m+1)^gamma)^2=(m+1)^(2*gamma) give both inequalities. -/
theorem topValue_bounds {a b : ℝ} (ha:-1<a) (hb:-1<b) :
    ∃c C:ℝ,0<c ∧ 0<C ∧ ∀ᶠn:ℕ in atTop,∀m:ℕ,2*m≤n+6→
      c*((m:ℝ)+1)^(gamma a)≤topValue a b ha hb n m ∧
      topValue a b ha hb n m≤C*((m:ℝ)+1)^(gamma a) := by
  -- The genuine positive branch is fixed by the original recurrence value, rather than inferred from an unsigned square formula.
  obtain ⟨c,C,hc,hC,hbound⟩ := topValue_sq_bounds ha hb
  refine ⟨sqrt c,sqrt C,sqrt_pos.mpr hc,sqrt_pos.mpr hC,?_⟩
  filter_upwards [hbound,eventually_ge_atTop (6:ℕ)] with n hn hlarge
  intro m hm
  have hm' : m≤n := by omega
  have hp := (naturalPolynomial_top_pos ha hb hm').le
  have hx : 0<(m:ℝ)+1 := by positivity
  have hpow : (((m:ℝ)+1)^gamma a)^2=((m:ℝ)+1)^(2*gamma a) := by
    rw [pow_two,← Real.rpow_add hx]
    congr 1
    ring
  constructor
  · apply (sq_le_sq₀ (by positivity) hp).mp
    rw [mul_pow,Real.sq_sqrt hc.le,hpow]
    exact (hn m hm).1
  · apply (sq_le_sq₀ hp (by positivity)).mp
    rw [mul_pow,Real.sq_sqrt hC.le,hpow]
    exact (hn m hm).2

end
end jacobi.Support
