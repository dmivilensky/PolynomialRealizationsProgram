import krylov.Design.DirectionalDerivative
import Mathlib.SetTheory.Cardinal.Embedding

/-!
Article: main_krylov, thm:B, the necessary and sufficient sensitivity criterion.
Use: prove necessity from the actual one-sided directional derivative and
sufficiency from the established global tangent certificate. The input domain
is justified by actual support points, not a supplied envelope formula.
Source: Kiefer--Wolfowitz (1960), Kiefer (1974), Pukelsheim (1993).
-/

namespace krylov.Design
noncomputable section
open Polynomial MeasureTheory Matrix Set Filter
open scoped BigOperators Topology

/-- Every genuine directional sensitivity mean of an optimal nonsingular design is bounded by its objective.
Article: main_krylov, thm:B, necessity of the equivalence criterion.
Proof: the actual probability segment has a one-sided maximum at zero; its
proved directional derivative is therefore nonpositive in the positive tangent direction. -/
theorem optimal_interval_integral_sensitivity_le (I : chebyshev1.SpectralInterval)
    (M : ℕ) (w : Fin M → ℝ) {γ : ℝ} (hγ : 0 < γ)
    (ν : ProbabilityMeasure (Spectrum I))
    (hG : ∀ i : Fin M, (momentGram I (i.val + 1) ν).PosDef)
    (hopt : ∀ η, intervalObjective I M w γ η ≤ intervalObjective I M w γ ν)
    (η : ProbabilityMeasure (Spectrum I)) :
    (∫ t, sensitivity M w γ 0 (spectralCoordinate I) ν (momentCompetitors I M ν hG) t ∂η) ≤
      intervalObjective I M w γ ν := by
  have hd := intervalObjective_measureSegment_hasDerivWithinAt I M w γ ν η hG
  have hmax : IsMaxOn (fun s : ℝ => intervalObjective I M w γ (measureSegment ν η s))
      (Icc (0 : ℝ) 1) 0 := by
    intro s _
    change intervalObjective I M w γ (measureSegment ν η s) ≤
      intervalObjective I M w γ (measureSegment ν η 0)
    rw [measureSegment_zero]
    exact hopt _
  have hcone : (1 : ℝ) ∈ posTangentConeAt (Icc (0 : ℝ) 1) 0 := by
    simpa only [sub_zero] using sub_mem_posTangentConeAt_of_segment_subset
      (s := Icc (0 : ℝ) 1) (x := (0 : ℝ)) (y := 1)
      (segment_eq_Icc (by norm_num : (0 : ℝ) ≤ 1) ▸ Set.Subset.rfl)
  have hn := hmax.isLocalMaxOn.hasFDerivWithinAt_nonpos hd hcone
  have hb : γ * ((∫ t, sensitivity M w γ 0 (spectralCoordinate I) ν
      (momentCompetitors I M ν hG) t ∂η) - intervalObjective I M w γ ν) ≤ 0 := by
    simpa only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, one_mul] using! hn
  nlinarith

/-- Test the actual directional derivative with each point mass to obtain the necessary pointwise sensitivity bound.
Article: main_krylov, thm:B. -/
theorem sensitivity_le_of_optimal_interval (I : chebyshev1.SpectralInterval)
    (M : ℕ) (w : Fin M → ℝ) {γ : ℝ} (hγ : 0 < γ)
    (ν : ProbabilityMeasure (Spectrum I))
    (hG : ∀ i : Fin M, (momentGram I (i.val + 1) ν).PosDef)
    (hopt : ∀ η, intervalObjective I M w γ η ≤ intervalObjective I M w γ ν) :
    ∀ t : Spectrum I, sensitivity M w γ 0 (spectralCoordinate I) ν
      (momentCompetitors I M ν hG) t ≤ intervalObjective I M w γ ν := by
  intro t
  let η : ProbabilityMeasure (Spectrum I) := ⟨Measure.dirac t, inferInstance⟩
  have hi := optimal_interval_integral_sensitivity_le I M w hγ ν hG hopt η
  change (∫ u, sensitivity M w γ 0 (spectralCoordinate I) ν
    (momentCompetitors I M ν hG) u ∂Measure.dirac t) ≤ _ at hi
  simpa only [integral_dirac] using hi

/-- The complete necessary and sufficient equivalence criterion on the nonsingular moment domain.
Article: main_krylov, thm:B.
Proof: necessity uses the proved genuine directional derivative; sufficiency uses the global concave power tangent. -/
theorem intervalObjective_optimal_iff_sensitivity (I : chebyshev1.SpectralInterval)
    (M : ℕ) (w : Fin M → ℝ) (hw : ∀ i, 0 ≤ w i) {γ : ℝ} (hγ₀ : 0 < γ) (hγ₁ : γ ≤ 1)
    (ν : ProbabilityMeasure (Spectrum I))
    (hG : ∀ i : Fin M, (momentGram I (i.val + 1) ν).PosDef) :
    (∀ η, intervalObjective I M w γ η ≤ intervalObjective I M w γ ν) ↔
      ∀ t : Spectrum I, sensitivity M w γ 0 (spectralCoordinate I) ν
        (momentCompetitors I M ν hG) t ≤ intervalObjective I M w γ ν := by
  constructor
  · exact sensitivity_le_of_optimal_interval I M w hγ₀ ν hG
  · intro hB
    apply mixedObjective_optimal_of_sensitivity M w hw hγ₀.le hγ₁ 0 (spectralCoordinate I)
      ν (momentCompetitors I M ν hG) _ hB
    intro i
    rw [christoffel_eq_moment_inverse I _ ν (hG i)]
    exact inv_pos.mpr (hG i).inv.diag_pos

/-- A full physical support prefix supplies every positive moment matrix needed by the equivalence theorem.
Article: main_krylov, thm:B, the stated at-least-M+1 support hypothesis.
Proof: restrict the genuine support embedding to the required smaller degree. -/
theorem momentGram_posDef_of_support_prefix (I : chebyshev1.SpectralInterval) (M m : ℕ)
    (hm : m ≤ M) (ν : ProbabilityMeasure (Spectrum I))
    (z : Fin (M + 1) → Spectrum I) (hz : Function.Injective z)
    (hs : ∀ i, z i ∈ (ν : Measure (Spectrum I)).support) : (momentGram I m ν).PosDef := by
  let zp : Fin (m + 1) → Spectrum I := fun i => z (i.castLE (by omega))
  apply momentGram_posDef I m ν zp
  · intro i j hij
    apply Fin.ext
    exact congrArg (fun a : Fin (M + 1) => a.val) (hz hij)
  · intro i
    exact hs _

/-- At least M+1 actual support points supply the article's entire nonsingular moment domain.
Article: main_krylov, thm:B.
Proof: realize the support cardinal lower bound by a finite embedding and use the support-prefix theorem. -/
theorem exists_positive_moments_of_support_card (I : chebyshev1.SpectralInterval) (M : ℕ)
    (ν : ProbabilityMeasure (Spectrum I))
    (hcard : (M + 1 : ℕ∞) ≤ (ν : Measure (Spectrum I)).support.encard) :
    ∀ i : Fin M, (momentGram I (i.val + 1) ν).PosDef := by
  obtain ⟨z, _⟩ := Fin.Embedding.exists_embedding_disjoint_range_of_add_le_ENat_card
    (α := (ν : Measure (Spectrum I)).support) (n := M + 1) (s := ∅)
    (by simpa only [Set.ncard_empty, Nat.cast_zero, zero_add, ENat.card_coe_set_eq,
      Nat.cast_add, Nat.cast_one] using hcard)
  intro i
  apply momentGram_posDef_of_support_prefix I M (i.val + 1) (by omega) ν
    (fun j => (z j).val)
  · intro a b hab
    exact z.injective (Subtype.ext hab)
  · intro j
    exact (z j).property

end
end krylov.Design
