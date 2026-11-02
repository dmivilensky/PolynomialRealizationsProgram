import krylov.Correction.GatedUniformCycle
import krylov.Correction.GatedHomogeneousDomains

/-!
Article: main_krylov, thm:UCg(i,ii), complete actual uniform metric bounds.
Use: Remove the initial-gradient normalization and include zero perturbation
budgets in the true full-memory spectral-gated cycle theorem.
Source: proved genuine whole-class cycle estimates, exact real domain/query
homogeneity and the elementary vanishing characterization of quadratic bounds.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator

/-- A genuine nonnegative scalar bounded by one common quadratic allowance at every sufficiently small positive radius is exactly zero.
Use: Supply the original complete spectral-gated RFC bounds with their true initial-gradient scale and boundary cases.
Article: main_krylov, thm:UCg(i,ii), complete genuine uniform cycle bounds.
Proof: Choose a real positive radius controlled by the original radius, one and the proposed positive scalar. Its quadratic upper bound is strictly smaller than that scalar, giving a contradiction.
-/
theorem nonnegative_quadratic_vanish {F C δ : ℝ} (hF : 0≤F) (hC : 0≤C) (hδ : 0<δ)
    (hbound : ∀ ε : ℝ, 0<ε → ε<δ → F≤C*ε^2) : F=0 := by
  have hFle : F≤0 := by
    by_contra hf
    have hFp : 0<F := lt_of_not_ge hf
    let t := min (δ/2) (min 1 (F/(2*(C+1))))
    have ht : 0<t := lt_min (by positivity) (lt_min zero_lt_one (div_pos hFp (by positivity)))
    have htd : t<δ := (min_le_left _ _).trans_lt (by linarith)
    have ht1 : t≤1 := (min_le_right _ _).trans (min_le_left _ _)
    have htF : t*(2*(C+1))≤F := (le_div_iff₀ (by positivity : 0<2*(C+1))).mp
      ((min_le_right _ _).trans (min_le_right _ _))
    have hsq := mul_le_mul_of_nonneg_left ht1 (mul_nonneg hC ht.le)
    have hfbound := hbound t ht htd
    nlinarith
  exact le_antisymm hFle hF

/-- The actual normalized whole spectral-class gated-RFC cycle bounds hold also at zero operator perturbation budget with the same genuine constant.
Use: Supply the original complete spectral-gated RFC bounds with their true initial-gradient scale and boundary cases.
Article: main_krylov, thm:UCg(i,ii), complete genuine uniform cycle bounds.
Proof: Positive budgets use the completed actual cycle theorem. For zero budget, the original fixed operators satisfy every smaller positive allowance; the proved scalar vanishing criterion forces the true returned gradient to be exactly zero. The actual performed-last-query refinement follows as well.
-/
theorem gated_uniform_cycle_nonnegative_normalized (n : ℕ) (hn : 2≤n) (κ γ : ℝ)
    (hκ : 1≤κ) (hγ : 0<γ) (hγ1 : γ<1) :
    ∃ ε₀ C : ℝ, 0<ε₀ ∧ 0<C ∧
      ∀ (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (μ : ℝ), 0<μ →
      (∀ i, μ≤hb.1.eigenvalues i) → ‖cgOperator base‖≤κ*μ →
      ∀ (A B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (g : EuclideanSpace ℝ (Fin n)) (ε : ℝ), 0≤ε → ε<ε₀ → gatedFullRunDefined γ A B g n →
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ g‖≤1 →
      (∀ i<n, ‖canonicalOperator base (A i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤ε) →
      (∀ i<n, ‖canonicalOperator base (B i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤ε) →
      let m := gatedMethod fullMemory γ (E := EuclideanSpace ℝ (Fin n))
      let J := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
      ‖J (probedGradient m A B g n)‖≤C*ε^2 ∧
        ((probedPhase m A B g (n-1)).trace≠[] →
          ‖J (probedGradient m A B g n)‖≤C*(ε^2*‖J (probedGradient m A B g (n-1))‖+ε^3)) := by
  obtain ⟨δ,C,hδ,hC,hbound⟩ := gated_uniform_cycle_normalized n hn κ γ hκ hγ hγ1
  refine ⟨δ,C,hδ,hC,?_⟩
  intro base hb μ hμ hspec hnorm A B g ε hε he hdefined hinit hA hB
  by_cases hpos : 0<ε
  · exact hbound base hb μ hμ hspec hnorm A B g ε hpos he hdefined hinit hA hB
  · have heq : ε=0 := le_antisymm (by linarith) hε
    subst ε
    let m := gatedMethod fullMemory γ (E := EuclideanSpace ℝ (Fin n))
    let J := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
    have hz : ‖J (probedGradient m A B g n)‖=0 := nonnegative_quadratic_vanish
      (norm_nonneg _) hC.le hδ (by
        intro t ht htd
        exact (hbound base hb μ hμ hspec hnorm A B g t ht htd hdefined hinit
          (fun i hi => (hA i hi).trans ht.le) (fun i hi => (hB i hi).trans ht.le)).1)
    dsimp only
    change ‖J (probedGradient m A B g n)‖≤C*(0 : ℝ)^2 ∧
      ((probedPhase m A B g (n-1)).trace≠[] → ‖J (probedGradient m A B g n)‖≤
        C*((0 : ℝ)^2*‖J (probedGradient m A B g (n-1))‖+(0 : ℝ)^3))
    refine ⟨?_,?_⟩
    · simp only [hz,zero_pow (by decide : (2 : ℕ)≠0),mul_zero,le_refl]
    · intro _
      simp only [hz,zero_pow (by decide : (2 : ℕ)≠0),zero_pow (by decide : (3 : ℕ)≠0),
        zero_mul,add_zero,mul_zero,le_refl]

/-- Every genuinely defined full-memory gated-RFC cycle satisfies both printed whole spectral-class metric-gradient bounds for arbitrary actual initial data and all sufficiently small nonnegative operator perturbation budgets.
Use: Supply the original complete spectral-gated RFC bounds with their true initial-gradient scale and boundary cases.
Article: main_krylov, thm:UCg(i,ii), complete genuine uniform cycle bounds.
Proof: Choose the common radius and constant before every real reference and run. Genuine defined first curvature makes the actual initial metric gradient nonzero. Its exact normalization preserves every real solve and query condition. Apply the true normalized theorem, including zero budget, then restore both the actual terminal and penultimate gradient factors by the proved exact field and performed-query homogeneity.
-/
theorem gated_uniform_cycle (n : ℕ) (hn : 2≤n) (κ γ : ℝ)
    (hκ : 1≤κ) (hγ : 0<γ) (hγ1 : γ<1) :
    ∃ ε₀ C : ℝ, 0<ε₀ ∧ 0<C ∧
      ∀ (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (μ : ℝ), 0<μ →
      (∀ i, μ≤hb.1.eigenvalues i) → ‖cgOperator base‖≤κ*μ →
      ∀ (A B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (g : EuclideanSpace ℝ (Fin n)) (ε : ℝ), 0≤ε → ε≤ε₀ → gatedFullRunDefined γ A B g n →
      (∀ i<n, ‖canonicalOperator base (A i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤ε) →
      (∀ i<n, ‖canonicalOperator base (B i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤ε) →
      let m := gatedMethod fullMemory γ (E := EuclideanSpace ℝ (Fin n))
      let J := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
      ‖J (probedGradient m A B g n)‖≤C*ε^2*‖J g‖ ∧
        ((probedPhase m A B g (n-1)).trace≠[] →
          ‖J (probedGradient m A B g n)‖≤C*(ε^2*‖J (probedGradient m A B g (n-1))‖+ε^3*‖J g‖)) := by
  obtain ⟨δ,C,hδ,hC,hbound⟩ := gated_uniform_cycle_nonnegative_normalized n hn κ γ hκ hγ hγ1
  refine ⟨δ/2,C,half_pos hδ,hC,?_⟩
  intro base hb μ hμ hspec hnorm A B g ε hε he hdefined hA hB
  let m := gatedMethod fullMemory γ (E := EuclideanSpace ℝ (Fin n))
  let J := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
  let r := ‖J g‖
  let g₁ := r⁻¹ • g
  have hr : 0<r := gated_defined_initial_metric_pos base hb γ A B g n (by omega) hdefined
  have hc : r⁻¹≠0 := inv_ne_zero hr.ne'
  have hdom := gatedFullRunDefined_scalar γ A B g r⁻¹ hc n hdefined
  have hinit : ‖J g₁‖≤1 := by
    dsimp only [g₁]
    rw [map_smul,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
    change r⁻¹*r≤1
    rw [inv_mul_cancel₀ hr.ne']
  have heδ : ε<δ := he.trans_lt (by linarith)
  have hb' := hbound base hb μ hμ hspec hnorm A B g₁ ε hε heδ hdom hinit hA hB
  have hscaled i : ‖J (probedGradient m A B g₁ i)‖=r⁻¹*‖J (probedGradient m A B g i)‖ := by
    dsimp only [g₁]
    rw [(gated_scalar fullMemory γ A B g r⁻¹ hc i).1,map_smul,norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
  dsimp only
  refine ⟨?_,?_⟩
  · have ht := hb'.1
    rw [hscaled] at ht
    have hdiv : ‖J (probedGradient m A B g n)‖/r≤C*ε^2 := by simpa only [div_eq_inv_mul] using ht
    exact (div_le_iff₀ hr).mp hdiv
  · intro htrace
    have htrace' := (gated_scalar_trace_nonempty fullMemory γ A B g r⁻¹ hc (n-1)).mpr htrace
    have ht := hb'.2 htrace'
    rw [hscaled,hscaled] at ht
    have hdiv : ‖J (probedGradient m A B g n)‖/r≤
        C*(ε^2*(r⁻¹*‖J (probedGradient m A B g (n-1))‖)+ε^3) := by
      simpa only [div_eq_inv_mul] using ht
    have hm := (div_le_iff₀ hr).mp hdiv
    apply hm.trans_eq
    calc
      _ = C*(ε^2*‖J (probedGradient m A B g (n-1))‖*(r*r⁻¹)+ε^3*r) := by ring
      _ = _ := by rw [mul_inv_cancel₀ hr.ne',mul_one]

end
end krylov.Correction
