import krylov.Correction.JointRemainder
import krylov.Stability.AnalyticFlatness
import krylov.Stability.SmoothMetricCompact

/-!
Article: main_krylov, thm:C and lem:U, compact-uniform original-scenario bounds.
Use: choose the actual cubic radius and constant before every reference in
the given compact and before every original finite symmetric budget profile.
Source: genuine joint native remainder analyticity, proved pointwise cubic
order, actual Taylor-jet uniqueness and the existing weighted compact tube.
-/

namespace krylov.Correction
noncomputable section
open Matrix Filter Asymptotics Topology Finset krylov.Reference krylov.Variation krylov.Envelope
  krylov.Methods krylov.Secant krylov.Stability krylov.LinearAlgebra
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X]

/-- Individual original finite source budgets control exactly the norm used by the common cubic tube.
Use: the common scenario radius includes arbitrary independent intermediate and terminal defects and every zero-budget coordinate.
Article: main_krylov, thm:C and lem:U, largest-budget control in original scenario variables.
Proof: the actual symmetric-scenario norm is its inherited finite product
norm, hence the maximum of the individual true spectral matrix norms. -/
theorem symmetricScenario_norm_le {n N : ℕ} (Θ : symmetricScenarios n N) {s : ℝ} (hs : 0≤s)
    (hE : ∀ i, ‖Θ.val.1 i‖≤s) (hF : ∀ i, ‖Θ.val.2 i‖≤s) : ‖Θ‖≤s := by
  change max ‖Θ.val.1‖ ‖Θ.val.2‖≤s
  exact max_le ((pi_norm_le_iff_of_nonneg hs).mpr hE) ((pi_norm_le_iff_of_nonneg hs).mpr hF)

/-- The actual full RFC canonical cubic remainder has a common weighted bound over compact varying references and every original symmetric scenario.
Use: both constants precede all actual references, perturbation directions and budget profiles.
Article: main_krylov, thm:C and lem:U, genuine compact-uniform O(ω³) remainder.
Proof: the actual native remainder is jointly analytic in the original
reference/scenario variables and has proved cubic order on each reference
fibre. Analytic uniqueness derives its vanishing true Taylor jet, so the
weighted compact tube applies with no jet or uniform-remainder premise.
The native coefficient is exactly the article's genuine canonical coefficient.
-/
theorem compact_scenario_cubic_tube {k : ℕ}
    (base : X → Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (g : X → EuclideanSpace ℝ (Fin (k+1))) (K : Set X) (hK : IsCompact K)
    (hb : ∀ x∈K, AnalyticAt ℝ base x)
    (hpos : ∀ x∈K, ∀ᶠ y in 𝓝 x, (base y).PosDef)
    (hg : ∀ x∈K, AnalyticAt ℝ g x)
    (hN : ∀ x (hx : x∈K), k+1≤referenceAtomCount (base x) (hpos x hx).self_of_nhds (g x))
    (hk : 0<k) :
    ∃ δ C : ℝ, 0<δ ∧ 0≤C ∧ ∀ x∈K, ∀ Θ : symmetricScenarios (k+1) (k+1), ‖Θ‖≤δ →
      ‖cgOperator (metricRoot (base x))⁻¹
        (probedGradient (rfcMethod fullMemory 1) (scenarioProbe (base x) Θ.val)
          (scenarioCorrection (base x) Θ.val) (g x) (k+1))+
        ‖canonicalCGStep (base x) (g x) k‖ • staircaseOperator (base x) (g x)
          (matrixSequenceExtension k Θ.val.1) (matrixSequenceExtension (k+1) Θ.val.2 k) (k+1)
          (freshDefect (base x) (g x) (matrixSequenceExtension k Θ.val.1) (k+1))‖≤
            C*‖Θ‖^3*‖cgOperator (metricRoot (base x))⁻¹ (g x)‖ := by
  -- The reference weight is derived from true positive data before the common tube is chosen.
  let f := fun p : X × symmetricScenarios (k+1) (k+1) =>
    nativeScenarioRemainder (base p.1) (g p.1) p.2
  have hp (x : X) (hx : x∈K) : (base x).PosDef := (hpos x hx).self_of_nhds
  have he : ContinuousOn (fun x => ‖cgOperator (metricRoot (base x))⁻¹ (g x)‖) K :=
    canonical_error_continuousOn base g K (fun x hx => (hb x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hg x hx).continuousAt.continuousWithinAt) hp
  have hepos (x : X) (hx : x∈K) : 0<‖cgOperator (metricRoot (base x))⁻¹ (g x)‖ :=
    canonical_error_pos (base x) (hp x hx) (g x)
      (cg_nonstagnation _ (hp x hx) _ 0 (by have := hN x hx; omega))
  obtain ⟨δ,C,hδ,hC,hT⟩ := compact_analytic_flat_weighted_fibres f K hK 3 (by omega)
    (fun x hx => nativeScenarioRemainder_analyticAt base g x (hb x hx) (hpos x hx) (hg x hx) (hN x hx))
    (fun x hx => nativeScenarioRemainder_order (base x) (hp x hx) (g x) (hN x hx) hk) _ he hepos
  refine ⟨δ,C,hδ,hC,?_⟩
  intro x hx Θ hΘ
  have ht := hT x hx Θ hΘ
  rw [show f (x,Θ)=_ from nativeScenarioRemainder_eq (base x) (hp x hx) (g x) (hN x hx) Θ] at ht
  exact ht

/-- The sharp actual RFC spectral bound has a single cubic remainder constant over compact varying references and every original budget profile.
Use: establish the uniform upper half of the unknown-base minimax comparison with the true initial-error weight.
Article: main_krylov, thm:C, compact-uniform all-profile sharp upper bound.
Proof: the common actual cubic tube is chosen before both the reference and
the budget profile. The sharp genuine-CG compression bound controls its
leading vector; the true full-CG step/error identity and norm triangle
inequality give the actual output estimate on that same common tube.
-/
theorem compact_scenario_spectral_upper {k : ℕ}
    (base : X → Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (g : X → EuclideanSpace ℝ (Fin (k+1))) (K : Set X) (hK : IsCompact K)
    (hb : ∀ x∈K, AnalyticAt ℝ base x)
    (hpos : ∀ x∈K, ∀ᶠ y in 𝓝 x, (base y).PosDef)
    (hg : ∀ x∈K, AnalyticAt ℝ g x)
    (hN : ∀ x (hx : x∈K), k+1≤referenceAtomCount (base x) (hpos x hx).self_of_nhds (g x))
    (hk : 0<k) :
    ∃ δ C : ℝ, 0<δ ∧ 0≤C ∧ ∀ x∈K, ∀ Θ : symmetricScenarios (k+1) (k+1), ‖Θ‖≤δ →
      ∀ (ω : ℕ → ℝ) (w : ℝ),
      (∀ i∈range k, ‖matrixSequenceExtension k Θ.val.1 i‖≤ω i) →
      ‖matrixSequenceExtension (k+1) Θ.val.2 k‖≤w →
      ‖cgOperator (metricRoot (base x))⁻¹
        (probedGradient (rfcMethod fullMemory 1) (scenarioProbe (base x) Θ.val)
          (scenarioCorrection (base x) Θ.val) (g x) (k+1))‖≤
        ‖cgCanonicalError (base x) (g x) k‖*sharpConstant (∑ i∈range k, ω i) w+
          C*‖Θ‖^3*‖cgOperator (metricRoot (base x))⁻¹ (g x)‖ := by
  -- Use precisely the same actual reference/scenario tube for every norm budget profile.
  obtain ⟨δ,C,hδ,hC,hT⟩ := compact_scenario_cubic_tube base g K hK hb hpos hg hN hk
  refine ⟨δ,C,hδ,hC,?_⟩
  intro x hx Θ hΘ ω w hω hw
  have hp : (base x).PosDef := (hpos x hx).self_of_nhds
  have hbound := reference_second_order_bound (base x) hp (g x) (hN x hx) (by omega : 0<k+1)
    (matrixSequenceExtension k Θ.val.1) (fun i _ => symmetricScenario_increment_symm Θ i)
    (matrixSequenceExtension (k+1) Θ.val.2 k) ω hω hw
  simp only [Nat.add_sub_cancel] at hbound
  let v := ‖canonicalCGStep (base x) (g x) k‖ • staircaseOperator (base x) (g x)
    (matrixSequenceExtension k Θ.val.1) (matrixSequenceExtension (k+1) Θ.val.2 k) (k+1)
    (freshDefect (base x) (g x) (matrixSequenceExtension k Θ.val.1) (k+1))
  have hv : ‖v‖≤‖cgCanonicalError (base x) (g x) k‖*sharpConstant (∑ i∈range k, ω i) w := by
    rw [norm_smul,Real.norm_of_nonneg (norm_nonneg _),← terminal_step_error_norm (base x) hp (g x) (hN x hx)]
    exact mul_le_mul_of_nonneg_left hbound (norm_nonneg _)
  have ht := hT x hx Θ hΘ
  let u := cgOperator (metricRoot (base x))⁻¹
    (probedGradient (rfcMethod fullMemory 1) (scenarioProbe (base x) Θ.val)
      (scenarioCorrection (base x) Θ.val) (g x) (k+1))
  calc
    ‖u‖ = ‖(u+v)-v‖ := by rw [add_sub_cancel_right]
    _ ≤ ‖u+v‖+‖v‖ := norm_sub_le _ _
    _ ≤ _ := (add_le_add ht hv).trans_eq (add_comm _ _)

/-- The improved actual RFC Frobenius bound has a single cubic remainder constant over compact varying references and every original budget profile.
Use: establish the uniform upper half of the unknown-base minimax comparison with the true initial-error weight and its square-root-two improvement.
Article: main_krylov, thm:C2(a), compact-uniform all-profile Frobenius upper bound.
Proof: the common actual cubic tube is chosen before both the reference and
the budget profile. The sharp genuine-CG compression bound controls its
leading vector; the true full-CG step/error identity and norm triangle
inequality give the improved actual output estimate on that same common tube.
-/
theorem compact_scenario_frobenius_upper {k : ℕ}
    (base : X → Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (g : X → EuclideanSpace ℝ (Fin (k+1))) (K : Set X) (hK : IsCompact K)
    (hb : ∀ x∈K, AnalyticAt ℝ base x)
    (hpos : ∀ x∈K, ∀ᶠ y in 𝓝 x, (base y).PosDef)
    (hg : ∀ x∈K, AnalyticAt ℝ g x)
    (hN : ∀ x (hx : x∈K), k+1≤referenceAtomCount (base x) (hpos x hx).self_of_nhds (g x))
    (hk : 0<k) :
    ∃ δ C : ℝ, 0<δ ∧ 0≤C ∧ ∀ x∈K, ∀ Θ : symmetricScenarios (k+1) (k+1), ‖Θ‖≤δ →
      ∀ (ω : ℕ → ℝ) (w : ℝ),
      (∀ i∈range k, chebyshev1.hsNorm (matrixSequenceExtension k Θ.val.1 i)≤ω i) →
      chebyshev1.hsNorm (matrixSequenceExtension (k+1) Θ.val.2 k)≤w →
      ‖cgOperator (metricRoot (base x))⁻¹
        (probedGradient (rfcMethod fullMemory 1) (scenarioProbe (base x) Θ.val)
          (scenarioCorrection (base x) Θ.val) (g x) (k+1))‖≤
        ‖cgCanonicalError (base x) (g x) k‖*(sharpConstant (∑ i∈range k, ω i) w/Real.sqrt 2)+
          C*‖Θ‖^3*‖cgOperator (metricRoot (base x))⁻¹ (g x)‖ := by
  -- Use precisely the same actual reference/scenario tube for every norm budget profile.
  obtain ⟨δ,C,hδ,hC,hT⟩ := compact_scenario_cubic_tube base g K hK hb hpos hg hN hk
  refine ⟨δ,C,hδ,hC,?_⟩
  intro x hx Θ hΘ ω w hω hw
  have hp : (base x).PosDef := (hpos x hx).self_of_nhds
  have hbound := reference_frobenius_second_order_bound (base x) hp (g x) (hN x hx) (by omega : 0<k+1)
    (matrixSequenceExtension k Θ.val.1) (fun i _ => symmetricScenario_increment_symm Θ i)
    (matrixSequenceExtension (k+1) Θ.val.2 k) ω hω hw
  simp only [Nat.add_sub_cancel] at hbound
  have hbound' : ‖staircaseOperator (base x) (g x)
      (matrixSequenceExtension k Θ.val.1) (matrixSequenceExtension (k+1) Θ.val.2 k) (k+1)
      (freshDefect (base x) (g x) (matrixSequenceExtension k Θ.val.1) (k+1))‖≤
        sharpConstant (∑ i∈range k, ω i) w/Real.sqrt 2 := by
    apply (le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ)<2))).mpr
    simpa only [mul_comm] using hbound
  let v := ‖canonicalCGStep (base x) (g x) k‖ • staircaseOperator (base x) (g x)
    (matrixSequenceExtension k Θ.val.1) (matrixSequenceExtension (k+1) Θ.val.2 k) (k+1)
    (freshDefect (base x) (g x) (matrixSequenceExtension k Θ.val.1) (k+1))
  have hv : ‖v‖≤‖cgCanonicalError (base x) (g x) k‖*(sharpConstant (∑ i∈range k, ω i) w/Real.sqrt 2) := by
    rw [norm_smul,Real.norm_of_nonneg (norm_nonneg _),← terminal_step_error_norm (base x) hp (g x) (hN x hx)]
    exact mul_le_mul_of_nonneg_left hbound' (norm_nonneg _)
  have ht := hT x hx Θ hΘ
  let u := cgOperator (metricRoot (base x))⁻¹
    (probedGradient (rfcMethod fullMemory 1) (scenarioProbe (base x) Θ.val)
      (scenarioCorrection (base x) Θ.val) (g x) (k+1))
  calc
    ‖u‖ = ‖(u+v)-v‖ := by rw [add_sub_cancel_right]
    _ ≤ ‖u+v‖+‖v‖ := norm_sub_le _ _
    _ ≤ _ := (add_le_add ht hv).trans_eq (add_comm _ _)

end
end krylov.Correction
