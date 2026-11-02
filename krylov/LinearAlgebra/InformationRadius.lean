import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Seminorm.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Basic.ENNReal.Real
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Article: main_krylov, Appendix A, apA:galerkin(d), information-radius inequalities.
Use: equal observed data force a common correction; these inequalities bound
its error on two indistinguishable scenarios before any method is constructed.
Source: the parallelogram identity and the triangle inequality in mathlib.
-/

namespace krylov.LinearAlgebra
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E]

/-- Opposite scenarios retain their entire squared uncertainty after any common shift.
Use: the sharp two-scenario lower bound for adaptive information arguments.
Article: main_krylov, apA:galerkin(d), max_± ‖a±b‖² ≥ ‖a‖²+‖b‖².
Source: mathlib parallelogram_law_with_norm.
Proof: the larger squared norm is at least half their parallelogram sum. -/
theorem two_scenario_sq [InnerProductSpace ℝ E] (a b : E) :
    ‖a‖^2 + ‖b‖^2 ≤ max (‖a + b‖^2) (‖a - b‖^2) := by
  have h := parallelogram_law_with_norm ℝ a b
  have hp := le_max_left (‖a + b‖^2) (‖a - b‖^2)
  have hm := le_max_right (‖a + b‖^2) (‖a - b‖^2)
  linarith

/-- Two residuals separated by a fixed vector have radius at least half their distance.
Use: every common update is subject to the same information obstruction.
Article: main_krylov, apA:galerkin(d), the half-distance bound.
Proof: cancel the common update inside the difference and apply the triangle inequality. -/
theorem two_scenario_distance (a b u : E) :
    ‖a - b‖ / 2 ≤ max ‖a + u‖ ‖b + u‖ := by
  have h := norm_sub_le (a + u) (b + u)
  have he : a + u - (b + u) = a - b := by abel
  rw [he] at h
  have hp := le_max_left ‖a + u‖ ‖b + u‖
  have hm := le_max_right ‖a + u‖ ‖b + u‖
  linarith

/-- Reflection about the information centre forces its seminorm radius at any other centre.
Use: pointwise form of the reflected-fibre minimax principle, with no boundedness premise.
Article: main_krylov, apA:galerkin(d), reflected information sets.
Proof: twice the centred point is the difference of the two residuals at the
new centre; seminorm homogeneity and the triangle inequality give the bound. -/
theorem reflected_seminorm [Module ℝ E] (ν : Seminorm ℝ E) (B J K : E) :
    ν (B - J) ≤ max (ν (B - K)) (ν ((2 : ℝ) • J - B - K)) := by
  have he : (2 : ℝ) • (B - J) = (B - K) - ((2 : ℝ) • J - B - K) := by
    simp only [two_smul]
    abel
  have h := map_sub_le_add ν (B - K) ((2 : ℝ) • J - B - K)
  rw [← he, map_smul_eq_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at h
  have hp := le_max_left (ν (B - K)) (ν ((2 : ℝ) • J - B - K))
  have hm := le_max_right (ν (B - K)) (ν ((2 : ℝ) • J - B - K))
  linarith

/-- Reflection forces the full supremal seminorm radius, also for unbounded fibres.
Use: the article's information-set assertion with no hidden boundedness assumption.
Article: main_krylov, apA:galerkin(d), reflected-fibre supremum inequality.
Proof: each original point and its reflected partner belong to the larger fibre;
their pointwise lower bound is dominated by that fibre's extended supremum. -/
theorem reflected_fibre_radius [Module ℝ E] (ν : Seminorm ℝ E)
    (F F0 : Set E) (J K : E) (hsub : F0 ⊆ F)
    (href : ∀ B ∈ F0, (2 : ℝ) • J - B ∈ F) :
    (⨆ B : F0, ENNReal.ofReal (ν (B.val - J))) ≤
      ⨆ B : F, ENNReal.ofReal (ν (B.val - K)) := by
  apply iSup_le
  intro B
  -- Both reflected observations are compared with the same arbitrary decision K.
  have hp := le_iSup (fun C : F => ENNReal.ofReal (ν (C.val - K))) ⟨B.val, hsub B.property⟩
  have hm := le_iSup (fun C : F => ENNReal.ofReal (ν (C.val - K)))
    ⟨(2 : ℝ) • J - B.val, href B.val B.property⟩
  exact (ENNReal.ofReal_le_ofReal (reflected_seminorm ν B.val J K)).trans
    (by rw [ENNReal.ofReal_max]; exact max_le hp hm)

/-- The norm-scaled two-scenario lower bound before changing physical coordinates.
Use: obtain the printed robust least-squares bound with K=ΔG⁻¹.
Article: main_krylov, apA:galerkin(d), the two-sided robust correction bound.
Proof: the parallelogram bounds the squared mean and difference; Cauchy--Schwarz
then bounds Kρ by their joint energy without discarding their correlation. -/
theorem two_scenario_operator_lower [InnerProductSpace ℝ E]
    (K : E →L[ℝ] E) (ρ u : E) :
    ‖K ρ‖ / Real.sqrt (1 + ‖K‖^2) ≤ max ‖ρ + u + K u‖ ‖ρ + u - K u‖ := by
  -- The common mean and signed unknown action are bounded together by the parallelogram.
  let a := ρ + u
  let b := K u
  let M := max ‖a + b‖ ‖a - b‖
  have hM : 0 ≤ M := (norm_nonneg (a + b)).trans (le_max_left _ _)
  have he : ‖a‖^2 + ‖b‖^2 ≤ M^2 := by
    have h := two_scenario_sq a b
    have hp := (sq_le_sq₀ (norm_nonneg _) hM).mpr (le_max_left ‖a + b‖ ‖a - b‖)
    have hm := (sq_le_sq₀ (norm_nonneg _) hM).mpr (le_max_right ‖a + b‖ ‖a - b‖)
    exact h.trans (max_le hp hm)
  have hv : K ρ = K a - b := by simp only [a, b, map_add, add_sub_cancel_right]
  have hn : ‖K ρ‖ ≤ ‖K‖ * ‖a‖ + ‖b‖ := by
    rw [hv]
    exact (norm_sub_le _ _).trans (add_le_add (K.le_opNorm a) le_rfl)
  have hc : ‖K ρ‖^2 ≤ (1 + ‖K‖^2) * M^2 := by
    have hs := (sq_le_sq₀ (norm_nonneg _) (add_nonneg
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _))).mpr hn
    have he' := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 1 + ‖K‖^2)
    nlinarith [sq_nonneg (‖a‖ - ‖K‖ * ‖b‖)]
  have hp : 0 < Real.sqrt (1 + ‖K‖^2) := Real.sqrt_pos.mpr (by positivity)
  apply (div_le_iff₀ hp).mpr
  have hs := Real.sq_sqrt (by positivity : 0 ≤ 1 + ‖K‖^2)
  have hprod : 0 ≤ Real.sqrt (1 + ‖K‖^2) * M := mul_nonneg hp.le hM
  nlinarith [norm_nonneg (K ρ)]

/-- The actual infimum of the two-scenario robust residual objective.
Use: keep the information lower bound separate from any particular algorithm.
Article: main_krylov, apA:galerkin(d), inf_v max_± ‖ρ+(G±Δ)v‖. -/
noncomputable def twoScenarioValue [NormedSpace ℝ E] (G Δ : E →L[ℝ] E) (ρ : E) : ℝ :=
  sInf (Set.range fun v : E => max ‖ρ + G v + Δ v‖ ‖ρ + G v - Δ v‖)

/-- The two robust least-squares information bounds for every invertible physical model.
Use: the centre correction gives the upper bound, and every correction obeys the lower one.
Article: main_krylov, apA:galerkin(d), both displayed infimum inequalities.
Proof: substitute u=Gv into the proved pointwise estimate; for the upper bound
take the actual centre update v=−G⁻¹ρ and cancel the two mean terms. -/
theorem two_scenario_value_bounds [InnerProductSpace ℝ E]
    (G : E ≃L[ℝ] E) (Δ : E →L[ℝ] E) (ρ : E) :
    let K := Δ.comp G.symm.toContinuousLinearMap
    (‖K ρ‖ / Real.sqrt (1 + ‖K‖^2) ≤ twoScenarioValue G.toContinuousLinearMap Δ ρ) ∧
    (twoScenarioValue G.toContinuousLinearMap Δ ρ ≤ ‖K ρ‖) := by
  -- Bound every member of the objective range, then test the explicit inverse-model update.
  let K := Δ.comp G.symm.toContinuousLinearMap
  have hb : BddBelow (Set.range fun v : E => max ‖ρ + G v + Δ v‖ ‖ρ + G v - Δ v‖) :=
    ⟨0, by rintro r ⟨v, rfl⟩; exact (norm_nonneg _).trans (le_max_left _ _)⟩
  constructor
  · apply le_csInf (Set.range_nonempty _)
    rintro r ⟨v, rfl⟩
    have h := two_scenario_operator_lower K ρ (G v)
    simpa only [K, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply] using h
  · have h := csInf_le hb (Set.mem_range_self (-(G.symm ρ)))
    simpa only [twoScenarioValue, map_neg, ContinuousLinearEquiv.apply_symm_apply,
      add_neg_cancel, zero_add, zero_sub, norm_neg, max_self, K,
      ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe] using h

end krylov.LinearAlgebra
