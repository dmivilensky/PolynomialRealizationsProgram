import krylov.Design.HyperbolicLambert

/-!
Article: main_krylov, apC:lem:poisson, actual dual hyperbolic sums.
Use: identify the genuine sampled sech and weighted csch series with their
convergent Lambert expressions, then prove both printed exponential dual-tail
coefficients independently of any assumed Poisson identity.
Source: elementary exponential formulas for cosh and sinh and geometric-series
estimates. This module does not assume a Fourier transform formula.
-/

namespace krylov.Design
noncomputable section
open Real Filter jacobi.Young
open scoped Topology

/-- The actual positive sampled hyperbolic secant sum.
Article: main_krylov, apC:lem:poisson. -/
def sampledSech (θ : ℝ) : ℝ := ∑' n : ℕ, sech (((n : ℝ) + 1) * θ)

/-- The actual linearly weighted sampled hyperbolic cosecant sum.
Article: main_krylov, apC:lem:poisson. -/
def sampledWeightedCsch (θ : ℝ) : ℝ := ∑' n : ℕ, ((n : ℝ) + 1) / sinh (((n : ℝ) + 1) * θ)

/-- The exact exponential-nome formula for hyperbolic secant.
Article: main_krylov, apC:lem:poisson. -/
theorem sech_exp_nome (x : ℝ) : sech x = 2 * exp (-x) / (1 + exp (-x) ^ 2) := by
  rw [sech, Real.cosh_eq, Real.exp_neg]
  field_simp

/-- The exact exponential-nome formula for hyperbolic cosecant at a positive point.
Article: main_krylov, apC:lem:poisson. -/
theorem csch_exp_nome {x : ℝ} (hx : 0 < x) : (sinh x)⁻¹ = 2 * exp (-x) / (1 - exp (-x) ^ 2) := by
  have he : exp x ≠ 0 := (exp_pos x).ne'
  have hp : exp x ^ 2 - 1 ≠ 0 := by
    have h := Real.one_lt_exp_iff.mpr hx
    nlinarith
  rw [Real.sinh_eq, Real.exp_neg]
  field_simp

/-- Sampled hyperbolic secant is exactly twice the convergent Lambert series at exp(-theta).
Article: main_krylov, apC:lem:poisson, the actual nome dictionary. -/
theorem sampledSech_eq_lambert (θ : ℝ) : sampledSech θ = 2 * sechLambert (exp (-θ)) := by
  unfold sampledSech sechLambert
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [sech_exp_nome]
  have he : exp (-(((n : ℝ) + 1) * θ)) = exp (-θ) ^ (n + 1) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [he, ← pow_mul]
  rw [Nat.mul_comm (n + 1) 2]
  ring

/-- The actual sampled hyperbolic secant series is summable for every positive spacing.
Article: main_krylov, apC:lem:poisson. -/
theorem sampledSech_summable {θ : ℝ} (hθ : 0 < θ) :
    Summable (fun n : ℕ => sech (((n : ℝ) + 1) * θ)) := by
  have hq₁ : exp (-θ) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hs := (sechLambert_summable (exp_pos (-θ)).le hq₁).mul_left 2
  convert! hs using 1
  funext n
  rw [sech_exp_nome]
  have he : exp (-(((n : ℝ) + 1) * θ)) = exp (-θ) ^ (n + 1) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [he]
  have hpow : (exp (-θ) ^ (n + 1)) ^ 2 = exp (-θ) ^ (2 * (n + 1)) := by rw [← pow_mul]; congr 1; omega
  rw [hpow]
  ring

/-- Each actual weighted hyperbolic cosecant sample has its exact nome expression.
Article: main_krylov, apC:lem:poisson. -/
theorem sampledWeightedCsch_term {θ : ℝ} (hθ : 0 < θ) (n : ℕ) :
    ((n : ℝ) + 1) / sinh (((n : ℝ) + 1) * θ) =
      2 * (((n : ℝ) + 1) * exp (-θ) ^ (n + 1) / (1 - exp (-θ) ^ (2 * (n + 1)))) := by
  have hx : 0 < ((n : ℝ) + 1) * θ := mul_pos (by positivity) hθ
  rw [div_eq_mul_inv, csch_exp_nome hx]
  have he : exp (-(((n : ℝ) + 1) * θ)) = exp (-θ) ^ (n + 1) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [he]
  have hpow : (exp (-θ) ^ (n + 1)) ^ 2 = exp (-θ) ^ (2 * (n + 1)) := by rw [← pow_mul]; congr 1; omega
  rw [hpow]
  ring

/-- The actual weighted hyperbolic cosecant sum is twice its convergent Lambert series.
Article: main_krylov, apC:lem:poisson. -/
theorem sampledWeightedCsch_eq_lambert {θ : ℝ} (hθ : 0 < θ) :
    sampledWeightedCsch θ = 2 * cschLambert (exp (-θ)) := by
  unfold sampledWeightedCsch cschLambert
  rw [← tsum_mul_left]
  exact tsum_congr (sampledWeightedCsch_term hθ)

/-- The genuine weighted hyperbolic cosecant series is summable for every positive spacing.
Article: main_krylov, apC:lem:poisson. -/
theorem sampledWeightedCsch_summable {θ : ℝ} (hθ : 0 < θ) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) / sinh (((n : ℝ) + 1) * θ)) := by
  have hq₁ : exp (-θ) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hs := (cschLambert_summable (exp_pos (-θ)).le hq₁).mul_left 2
  exact hs.congr (fun n => (sampledWeightedCsch_term hθ n).symm)

/-- The genuine sampled secant sum has the exact leading exponential coefficient two.
Article: main_krylov, apC:lem:poisson, first dual tail.
Proof: transport the proved Lambert ratio limit along the actual positive nome exp(-theta). -/
theorem sampledSech_exponential_asymptotic :
    Tendsto (fun θ : ℝ => sampledSech θ / (2 * exp (-θ))) atTop (𝓝 1) := by
  have hq : Tendsto (fun θ : ℝ => exp (-θ)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨Real.tendsto_exp_neg_atTop_nhds_zero,
      Eventually.of_forall (fun θ => exp_pos (-θ))⟩
  have h := sechLambert_ratio_tendsto_one.comp hq
  convert! h using 1
  funext θ
  simp only [Function.comp_def]
  rw [sampledSech_eq_lambert]
  ring

/-- The genuine weighted cosecant sum has the exact leading exponential coefficient two.
Article: main_krylov, apC:lem:poisson, second dual tail. -/
theorem sampledWeightedCsch_exponential_asymptotic :
    Tendsto (fun θ : ℝ => sampledWeightedCsch θ / (2 * exp (-θ))) atTop (𝓝 1) := by
  have hq : Tendsto (fun θ : ℝ => exp (-θ)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨Real.tendsto_exp_neg_atTop_nhds_zero,
      Eventually.of_forall (fun θ => exp_pos (-θ))⟩
  have h := cschLambert_ratio_tendsto_one.comp hq
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with θ hθ
  simp only [Function.comp_def]
  rw [sampledWeightedCsch_eq_lambert hθ]
  ring

end
end krylov.Design
