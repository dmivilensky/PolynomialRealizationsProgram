import «2610.05164v2».Continuum.Transport

/-!
Article: 2610.05164v2, Lemma 4.
Lemma 4(v) for every finite positive coupling, including infinite transport cost.
Result: `«2610.05164v2».Continuum.measureOperator_transport_extended` supplies the stated article
conclusion.
-/
namespace «2610.05164v2».Continuum
noncomputable section
open MeasureTheory Real Set
open scoped ENNReal

/--
Lemma 4(v) for every finite positive coupling, including infinite transport cost. The
nonnegative integral and bound live in ENNReal.

The stated quantitative bound `nuclearNorm (measureOperator (μ.map Prod.fst)-measureOperator
(μ.map Prod.snd)) ≤ ENNReal.ofReal 2 * (ENNReal.ofReal 2 * μ univ * ∫⁻ z, ENNReal.ofReal
|z.1-z.2| ∂μ)^(1/2 : ℝ)`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2610.05164v2, Lemma 4.

Proof: Separate `cost = ⊤` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem measureOperator_transport_extended (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] :
    nuclearNorm (measureOperator (μ.map Prod.fst)-measureOperator (μ.map Prod.snd)) ≤
      ENNReal.ofReal 2 * (ENNReal.ofReal 2 * μ univ *
        ∫⁻ z, ENNReal.ofReal |z.1-z.2| ∂μ)^(1/2 : ℝ) := by
  -- Separate `cost = ⊤` from its negation; prove the goal under each of these mutually
  -- exclusive hypotheses.
  let cost : ℝ≥0∞ := ∫⁻ z, ENNReal.ofReal |z.1-z.2| ∂μ
  by_cases hc : cost = ⊤
  · have hm : μ univ ≠ 0 := by
      intro h
      have hz : μ = 0 := Measure.measure_univ_eq_zero.mp h
      simp [cost, hz] at hc
    have htwo : ENNReal.ofReal (2 : ℝ) ≠ 0 := by norm_num
    change _ ≤ ENNReal.ofReal 2*(ENNReal.ofReal 2*μ univ*cost)^(1/2 : ℝ)
    rw [hc, ENNReal.mul_top (mul_ne_zero htwo hm), ENNReal.top_rpow_of_pos (by norm_num),
      ENNReal.mul_top htwo]
    exact le_top
  · have hpos : 0 ≤ᵐ[μ] (fun z : ℝ × ℝ => |z.1-z.2|) :=
      Filter.Eventually.of_forall (fun _ => abs_nonneg _)
    have hmeas : AEStronglyMeasurable (fun z : ℝ × ℝ => |z.1-z.2|) μ :=
      (continuous_fst.sub continuous_snd).abs.aestronglyMeasurable
    -- Establish hi as the integrability justification for the later integral estimates or
    -- changes of order.
    have hi : Integrable (fun z : ℝ × ℝ => |z.1-z.2|) μ :=
      ⟨hmeas, (hasFiniteIntegral_iff_ofReal hpos).mpr (lt_top_iff_ne_top.mpr hc)⟩
    have hcEq : ENNReal.ofReal (∫ z, |z.1-z.2| ∂μ) = cost := by
      rw [integral_eq_lintegral_of_nonneg_ae hpos hmeas]
      exact ENNReal.ofReal_toReal hc
    have hmEq : ENNReal.ofReal (μ.real univ) = μ univ :=
      ENNReal.ofReal_toReal (measure_ne_top μ univ)
    have hn : 0 ≤ ∫ z, |z.1-z.2| ∂μ := integral_nonneg (fun _ => abs_nonneg _)
    have h := nuclearNorm_le_of_traceBound (measureOperator_transport μ hi)
    change _ ≤ ENNReal.ofReal 2*(ENNReal.ofReal 2*μ univ*cost)^(1/2 : ℝ)
    rw [← hmEq, ← hcEq, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
      ← Real.sqrt_eq_rpow, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact h

end
end «2610.05164v2».Continuum
