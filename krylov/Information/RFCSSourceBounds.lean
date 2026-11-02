import krylov.Correction.RFCSProbeWitness
import krylov.Information.KnownBaseRFCLower
import krylov.Information.MinimaxBound

/-!
Article: main_krylov, thm:RFCS, sharp actual finite-source probe bound.
Use: one real quadratic remainder tube covers every original finite
increment and independent probe-defect scenario; actual final isotropic
probe witnesses attain the sharp first-order coefficient.
Source: genuine independent-probe execution and full terminal expansion,
actual finite symmetric source coordinates and original spectral budgets.
-/

namespace krylov.Information
noncomputable section
open Matrix Filter Asymptotics Topology krylov.Methods krylov.Reference krylov.Stability krylov.LinearAlgebra krylov.Envelope krylov.Variation krylov.Correction krylov.Secant
open scoped Matrix.Norms.L2Operator InnerProductSpace
variable {k : ℕ}

/-- The genuinely returned RFC-S residual in the original inverse-base metric divided by its true final preterminal CG error norm.
Use: compare the actual source risk in precisely the theorem's original normalization.
Article: main_krylov, thm:RFCS, actual own-base normalized output. -/
def rfcsScenarioRatio (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (g : EuclideanSpace ℝ (Fin (k+1))) (Θ : symmetricScenarios (k+1) (k+1)) : ℝ :=
  ‖cgOperator (metricRoot base)⁻¹ (rfcsScenarioOutput base g Θ)‖/‖cgCanonicalError base g k‖

/-- The true worst normalized physical RFC-S output over all original finite symmetric source scenarios with given largest and final-probe budgets.
Use: the sharp source coefficient bounds a genuine complete scenario supremum.
Article: main_krylov, thm:RFCS, actual source supremal risk. -/
def rfcsWorstOutputRatio (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (g : EuclideanSpace ℝ (Fin (k+1))) (μ p : ℝ) : ENNReal :=
  ⨆ Θ : {Θ : symmetricScenarios (k+1) (k+1) // ‖Θ‖≤μ ∧ ‖matrixSequenceExtension (k+1) Θ.val.2 k‖≤p},
    ENNReal.ofReal (rfcsScenarioRatio base g Θ.val)


/-- Every actual finite RFC-S source scenario obeys the sharp last-probe normalized upper bound, and the genuine final isotropic probe witness attains the same coefficient with a common quadratic loss.
Use: the coefficient is exactly the original final-probe budget, regardless of all earlier independent probes and increments, including every degenerate profile.
Article: main_krylov, thm:RFCS, actual all-source sharp coefficient and attaining witness.
Proof: the genuine joint source tube bounds the actual output minus its
true final-probe leading vector. The original spectral budget bounds that
vector by the actual last CG error times the final-probe budget. For the
real admissible last-isotropic-probe witness its leading norm is exactly
that value; reverse norm comparison gives the matching lower endpoint.
The true positive terminal CG step scale gives the original normalization. -/
theorem rfcs_source_sharp_bounds (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (k+1))) (hN : k+1≤referenceAtomCount base hb g) (hk : 0<k) :
    ∃ δ C : ℝ, 0<δ ∧ 0<C ∧ ∀ μ p : ℝ, 0≤p → p≤μ → μ≤δ →
      (∀ Θ : symmetricScenarios (k+1) (k+1), ‖Θ‖≤μ → ‖matrixSequenceExtension (k+1) Θ.val.2 k‖≤p →
        rfcsScenarioRatio base g Θ≤p+C*μ^2) ∧
      p-C*μ^2≤rfcsScenarioRatio base g (rfcsLastProbeScenario k p) := by
  -- Fix the actual joint source tube before both original budgets and every genuine perturbation scenario.
  obtain ⟨δ,C₀,hδ,hC₀,htube⟩ := rfcs_scenario_quadratic_tube base hb g hN hk
  let φ := ‖canonicalCGStep base g k‖
  have hφ : 0<φ := norm_pos_iff.mpr (canonicalCGStep_ne_zero base hb g k
    (fun i hi => cg_nonstagnation base hb g i (hi.trans_lt (Nat.lt_succ_self k) |>.trans_le hN)))
  have hf : ‖canonicalCGUnitStep base g k‖=1 := by
    simpa only [Nat.add_sub_cancel] using terminal_unit_norm base hb g hN (Nat.succ_pos k)
  refine ⟨δ,C₀/φ,hδ,by positivity,?_⟩
  intro μ p hp hpμ hμδ
  have hμ : 0≤μ := hp.trans hpμ
  have hscale : (C₀/φ)*φ=C₀ := div_mul_cancel₀ C₀ hφ.ne'
  have hnorm (Θ : symmetricScenarios (k+1) (k+1)) (hΘ : ‖Θ‖≤μ) :
      ‖cgOperator (metricRoot base)⁻¹ (rfcsScenarioOutput base g Θ)-
        φ • cgOperator (matrixSequenceExtension (k+1) Θ.val.2 k) (canonicalCGUnitStep base g k)‖≤C₀*μ^2 :=
    (htube Θ (hΘ.trans hμδ)).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hΘ 2) hC₀.le)
  constructor
  · intro Θ hΘ hlast
    let y := cgOperator (metricRoot base)⁻¹ (rfcsScenarioOutput base g Θ)
    let v := φ • cgOperator (matrixSequenceExtension (k+1) Θ.val.2 k) (canonicalCGUnitStep base g k)
    have hv : ‖v‖≤φ*p := by
      rw [norm_smul,Real.norm_of_nonneg hφ.le]
      apply mul_le_mul_of_nonneg_left _ hφ.le
      have hi := (cgOperator (matrixSequenceExtension (k+1) Θ.val.2 k)).le_opNorm (canonicalCGUnitStep base g k)
      rw [hf,mul_one] at hi
      exact hi.trans (by simpa only [cgOperator,Matrix.l2_opNorm_toEuclideanCLM] using hlast)
    have hy : ‖y‖≤C₀*μ^2+φ*p := by
      calc
        ‖y‖=‖(y-v)+v‖ := congrArg norm (by abel)
        _ ≤ ‖y-v‖+‖v‖ := norm_add_le _ _
        _ ≤ _ := add_le_add (hnorm Θ hΘ) hv
    change ‖y‖/‖cgCanonicalError base g k‖≤_
    rw [terminal_step_error_norm base hb g hN]
    apply (div_le_iff₀ hφ).mpr
    nlinarith only [hy,congrArg (fun t : ℝ => t*μ^2) hscale]
  · -- The original last isotropic probe attains the exact true leading norm.
    let Θ := rfcsLastProbeScenario k p
    have hΘ : ‖Θ‖≤μ := (rfcsLastProbeScenario_spec k p).1.trans (by simpa only [abs_of_nonneg hp] using hpμ)
    have ht := hnorm Θ hΘ
    rw [(rfcsLastProbeScenario_spec k p).2] at ht
    simp only [cgOperator,map_smul,_root_.smul_apply,map_one,one_apply_eq_self,smul_smul] at ht
    let y := cgOperator (metricRoot base)⁻¹ (rfcsScenarioOutput base g Θ)
    let v := (φ*p) • canonicalCGUnitStep base g k
    have hv : ‖v‖=φ*p := by rw [norm_smul,hf,mul_one,Real.norm_of_nonneg (mul_nonneg hφ.le hp)]
    have hy : φ*p≤C₀*μ^2+‖y‖ := by
      have ht' : ‖y+(-v)‖≤C₀*μ^2 := by change ‖y-v‖≤_ at ht; simpa only [sub_eq_add_neg] using ht
      simpa only [norm_neg,hv] using norm_lower_of_add_bound y (-v) (C₀*μ^2) ht'
    change _≤‖y‖/‖cgCanonicalError base g k‖
    rw [terminal_step_error_norm base hb g hN]
    apply (le_div_iff₀ hφ).mpr
    nlinarith only [hy,congrArg (fun t : ℝ => t*μ^2) hscale]




end
end krylov.Information
