import krylov.Design.MomentSegment
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
Article: main_krylov, thm:B, apC:eq:dirder.
Use: differentiate the genuine Christoffel and mixed design objectives along
actual probability-measure segments, without an assumed envelope derivative.
Source: inverse-moment calculus and the classical equivalence-theorem proof
of Kiefer--Wolfowitz (1960), Kiefer (1974), Pukelsheim (1993).
-/

namespace krylov.Design
noncomputable section
open Polynomial MeasureTheory Matrix Set Filter
open scoped BigOperators Topology

/-- The actual Christoffel directional derivative is the energy of its minimizer in the new measure minus its old energy.
Article: main_krylov, thm:B, the component of apC:eq:dirder.
Proof: differentiate the proved inverse-moment formula on the genuine measure segment. -/
theorem christoffel_measureSegment_hasDerivWithinAt (I : chebyshev1.SpectralInterval) (m : ℕ)
    (ν η : ProbabilityMeasure (Spectrum I)) (hG : (momentGram I m ν).PosDef) :
    HasDerivWithinAt (fun s : ℝ => christoffel m 0 (spectralCoordinate I) (measureSegment ν η s))
      (polynomialEnergy (spectralCoordinate I) η (momentPolynomial I m ν) -
        christoffel m 0 (spectralCoordinate I) ν) (Icc (0 : ℝ) 1) 0 := by
  have hd := inverseInformation_hasDerivAt (momentGram I m ν)
    (momentGram I m η - momentGram I m ν) hG 0
  have hvalue : normalizedInverseColumn (momentGram I m ν) 0 ⬝ᵥ
      ((momentGram I m η - momentGram I m ν) *ᵥ normalizedInverseColumn (momentGram I m ν) 0) =
      polynomialEnergy (spectralCoordinate I) η (momentPolynomial I m ν) -
        christoffel m 0 (spectralCoordinate I) ν := by
    rw [Matrix.sub_mulVec, dotProduct_sub, ← polynomialEnergy_eq_momentGram,
      ← polynomialEnergy_eq_momentGram]
    change polynomialEnergy (spectralCoordinate I) η (momentPolynomial I m ν) -
      polynomialEnergy (spectralCoordinate I) ν (momentPolynomial I m ν) = _
    rw [momentPolynomial_attains I m ν hG]
  rw [hvalue] at hd
  have hlt : ∀ᶠ s : ℝ in 𝓝[Icc (0 : ℝ) 1] 0, s < 1 :=
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  have heq : (fun s : ℝ => christoffel m 0 (spectralCoordinate I) (measureSegment ν η s)) =ᶠ[
      𝓝[Icc (0 : ℝ) 1] 0]
      (fun s : ℝ => (((momentGram I m ν + s • (momentGram I m η - momentGram I m ν))⁻¹) 0 0)⁻¹) := by
    filter_upwards [self_mem_nhdsWithin, hlt] with s hs hs1
    rw [christoffel_eq_moment_inverse I m _ (momentGram_measureSegment_posDef I m ν η hG hs hs1),
      momentGram_measureSegment I m ν η hs]
  apply hd.hasDerivWithinAt.congr_of_eventuallyEq heq
  rw [measureSegment_zero, zero_smul, add_zero, christoffel_eq_moment_inverse I m ν hG]

/-- The genuine minimizing competitors used by the article's sensitivity function.
Article: main_krylov, thm:B. -/
def momentCompetitors (I : chebyshev1.SpectralInterval) (M : ℕ)
    (ν : ProbabilityMeasure (Spectrum I))
    (hG : ∀ i : Fin M, (momentGram I (i.val + 1) ν).PosDef) :
    ∀ i : Fin M, Competitor (i.val + 1) 0 :=
  fun i => ⟨momentPolynomial I (i.val + 1) ν, momentPolynomial_admissible I _ ν (hG i)⟩

/-- The genuine mixed objective has exactly the sensitivity directional derivative printed in the article.
Article: main_krylov, thm:B, apC:eq:dirder.
Proof: differentiate every actual positive Christoffel information and real power,
then integrate the actual minimizing sensitivity polynomial. -/
theorem intervalObjective_measureSegment_hasDerivWithinAt (I : chebyshev1.SpectralInterval)
    (M : ℕ) (w : Fin M → ℝ) (γ : ℝ) (ν η : ProbabilityMeasure (Spectrum I))
    (hG : ∀ i : Fin M, (momentGram I (i.val + 1) ν).PosDef) :
    HasDerivWithinAt (fun s : ℝ => intervalObjective I M w γ (measureSegment ν η s))
      (γ * ((∫ t, sensitivity M w γ 0 (spectralCoordinate I) ν (momentCompetitors I M ν hG) t ∂η) -
        intervalObjective I M w γ ν)) (Icc (0 : ℝ) 1) 0 := by
  have hpos (i : Fin M) : 0 < christoffel (i.val + 1) 0 (spectralCoordinate I) ν := by
    rw [christoffel_eq_moment_inverse I _ ν (hG i)]
    exact inv_pos.mpr (hG i).inv.diag_pos
  have ht (i : Fin M) :=
    ((christoffel_measureSegment_hasDerivWithinAt I (i.val + 1) ν η (hG i)).rpow_const
      (p := γ) (Or.inl (by rw [measureSegment_zero]; exact (hpos i).ne'))).const_mul (w i)
  have hd := HasDerivWithinAt.sum (u := Finset.univ) (fun i _ => ht i)
  convert! hd using 1
  · funext s
    simp only [intervalObjective, mixedObjective, Finset.sum_apply]
  · rw [integral_sensitivity]
    unfold intervalObjective mixedObjective
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [measureSegment_zero, momentCompetitors]
    have hp : (christoffel (i.val + 1) 0 (spectralCoordinate I) ν) ^ (γ - 1) *
        christoffel (i.val + 1) 0 (spectralCoordinate I) ν =
        (christoffel (i.val + 1) 0 (spectralCoordinate I) ν) ^ γ := by
      nth_rw 2 [← Real.rpow_one (christoffel (i.val + 1) 0 (spectralCoordinate I) ν)]
      rw [← Real.rpow_add (hpos i)]
      congr 1
      ring
    rw [← hp]
    ring

end
end krylov.Design
