import polyak.FiniteHorizon.ClosedGa
import polyak.FiniteHorizon.Critical
import polyak.Spectral.Optimal

/-!
Article: Theorem rate, the actual from-rest upper bound.
Use: the original finite-horizon supremum quantifies all admissible functions
and dimensions. Polyak normalization and the exact proved rate convert the
finite-memory bound without any additional trajectory or certificate premise.
-/
noncomputable section
namespace polyak.FiniteHorizon
open Growth Growth.FiniteHorizon Spectral Boundary Set Filter
open scoped Topology

theorem original_prefactor_of_normalized {μ L C T : ℝ} {H : ℕ}
    (hμ : 0<μ) (hL : μ<L) (hC : 0<C)
    (hbound : ∀ n : ℕ,envelope 0 (2*Dynamics.polyakQ μ L) (Dynamics.polyakQ μ L^2) H n≤
      C*Real.exp ((n : ℝ)*T)) :
    ∃ K : ℝ,0<K ∧ ∀ n : ℕ,
      Dynamics.worstAll μ L (Dynamics.polyakAlpha μ L) (Dynamics.polyakBeta μ L) n≤
        K*Real.exp ((n : ℝ)*T) := by
  refine ⟨Real.sqrt 2*C,by positivity,fun n => ?_⟩
  have hh:=Growth.worstAll_le_envelope μ L (Dynamics.polyakAlpha μ L) (Dynamics.polyakBeta μ L) n
  rw [Dynamics.polyak_normalizedA hμ hL,Dynamics.polyak_normalizedB hμ hL] at hh
  change _≤Real.sqrt 2*Growth.envelope 0 (2*Dynamics.polyakQ μ L) (Dynamics.polyakQ μ L^2) n at hh
  have hf:=full_envelope_le 0 (2*Dynamics.polyakQ μ L) (Dynamics.polyakQ μ L^2) H n
  have hb:=mul_le_mul_of_nonneg_left (hf.trans (hbound n)) (Real.sqrt_nonneg 2)
  nlinarith

/-- The complete noncentral open-at-Ga regime, with both closed internal switches. -/
theorem exists_original_prefactor_noncentral {μ L : ℝ} (hμ : 0<μ) (hL : μ<L)
    (ha : P2.Ga<Real.cosh (T (Dynamics.polyakQ μ L))) :
    ∃ K : ℝ,0<K ∧ ∀ n : ℕ,
      Dynamics.worstAll μ L (Dynamics.polyakAlpha μ L) (Dynamics.polyakBeta μ L) n≤
        K*Dynamics.rate μ L (Dynamics.polyakAlpha μ L) (Dynamics.polyakBeta μ L)^n := by
  obtain ⟨H,_,C,hC,hbound⟩:=exists_uniform_prefactor_noncentral
    (Dynamics.polyakQ_pos hμ hL) (Dynamics.polyakQ_lt_one hμ hL) ha
  obtain ⟨K,hK,hb⟩:=original_prefactor_of_normalized hμ hL hC hbound
  refine ⟨K,hK,fun n => ?_⟩
  rw [originalRate_eq_exp_T hμ hL,←Real.exp_nat_mul]
  exact hb n

/-- The positive exponent at the P₂-to-P₅ switch is covered by the closed P₂ germ. -/
theorem exists_original_prefactor_positive_Ga {μ L : ℝ} (hμ : 0<μ) (hL : μ<L)
    (ht : 0≤T (Dynamics.polyakQ μ L)) (ha : Real.cosh (T (Dynamics.polyakQ μ L))=P2.Ga) :
    ∃ K : ℝ,0<K ∧ ∀ n : ℕ,
      Dynamics.worstAll μ L (Dynamics.polyakAlpha μ L) (Dynamics.polyakBeta μ L) n≤
        K*Dynamics.rate μ L (Dynamics.polyakAlpha μ L) (Dynamics.polyakBeta μ L)^n := by
  obtain ⟨H,_,C,hC,hbound⟩:=exists_uniform_prefactor_positive_Ga
    (Dynamics.polyakQ_pos hμ hL) (Dynamics.polyakQ_lt_one hμ hL) ht ha
  obtain ⟨K,hK,hb⟩:=original_prefactor_of_normalized hμ hL hC hbound
  refine ⟨K,hK,fun n => ?_⟩
  rw [originalRate_eq_exp_T hμ hL,←Real.exp_nat_mul]
  exact hb n

/-- The critical parameter has one uniform bound for the genuine original executor. -/
theorem exists_original_prefactor_critical {μ L : ℝ} (hμ : 0<μ) (hL : μ<L)
    (hq : Dynamics.polyakQ μ L=Threshold.criticalQ) :
    ∃ K : ℝ,0<K ∧ ∀ n : ℕ,
      Dynamics.worstAll μ L (Dynamics.polyakAlpha μ L) (Dynamics.polyakBeta μ L) n≤K := by
  obtain ⟨H,_,C,hC,hbound⟩:=exists_uniform_prefactor_critical
  have hb : ∀ n : ℕ,envelope 0 (2*Dynamics.polyakQ μ L) (Dynamics.polyakQ μ L^2) H n≤
      C*Real.exp ((n : ℝ)*0):=by simpa only [hq,mul_zero,Real.exp_zero,mul_one] using hbound
  obtain ⟨K,hK,hKbound⟩:=original_prefactor_of_normalized hμ hL hC hb
  exact ⟨K,hK,by simpa only [mul_zero,Real.exp_zero,mul_one] using hKbound⟩

/-- The P₁ endpoint GW is included, with either sign of the optimal exponent. -/
theorem exists_original_prefactor_p1 {μ L : ℝ} (hμ : 0<μ) (hL : μ<L)
    (hW : GW≤Real.cosh (T (Dynamics.polyakQ μ L))) :
    ∃ K : ℝ,0<K ∧ ∀ n : ℕ,
      Dynamics.worstAll μ L (Dynamics.polyakAlpha μ L) (Dynamics.polyakBeta μ L) n≤
        K*Dynamics.rate μ L (Dynamics.polyakAlpha μ L) (Dynamics.polyakBeta μ L)^n := by
  exact exists_original_prefactor_noncentral hμ hL ((P2.Ga_lt_G1.trans G1_lt_GW).trans_le hW)

/-- Both switches bounding the exact spiral arc are included. -/
theorem exists_original_prefactor_spiral {μ L : ℝ} (hμ : 0<μ) (hL : μ<L)
    (h₁ : G1≤Real.cosh (T (Dynamics.polyakQ μ L))) :
    ∃ K : ℝ,0<K ∧ ∀ n : ℕ,
      Dynamics.worstAll μ L (Dynamics.polyakAlpha μ L) (Dynamics.polyakBeta μ L) n≤
        K*Dynamics.rate μ L (Dynamics.polyakAlpha μ L) (Dynamics.polyakBeta μ L)^n := by
  exact exists_original_prefactor_noncentral hμ hL (P2.Ga_lt_G1.trans_le h₁)

/-- The condition-number expression is identical to the original curvature
tuning, so the hypothesis can be stated entirely in κ=L/μ. -/
theorem exists_original_prefactor_of_condition {μ L : ℝ} (hμ : 0<μ) (hL : μ<L)
    (ha : P2.Ga<Real.cosh (T (Dynamics.conditionQ (L/μ)))) :
    ∃ K : ℝ,0<K ∧ ∀ n : ℕ,
      Dynamics.worstAll μ L (Dynamics.polyakAlpha μ L) (Dynamics.polyakBeta μ L) n≤
        K*Dynamics.rate μ L (Dynamics.polyakAlpha μ L) (Dynamics.polyakBeta μ L)^n := by
  apply exists_original_prefactor_noncentral hμ hL
  rwa [Dynamics.polyakQ_eq_conditionQ hμ hL]

end polyak.FiniteHorizon
