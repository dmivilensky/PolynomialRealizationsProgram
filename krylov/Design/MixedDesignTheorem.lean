import krylov.Design.PrescribedAtoms

/-!
Article: main_krylov, thm:B and apC:lem:natoms, assembled original-domain statements.
Use: expose the sharp all-maximizers support count, the exact attained-maximum
equivalence criterion on the stated support domain, and the same actual
sensitivity certificate. All moment positivity is derived from genuine support.
Source: Kiefer--Wolfowitz (1960), Kiefer (1974), Pukelsheim (1993); the sharp
support proof uses double interior polynomial contacts instead of a separate
Gaussian reduction, preserving all conclusions of the mixed-design theorem.
-/

namespace krylov.Design
noncomputable section
open MeasureTheory Set
open scoped BigOperators

/-- With a positive last weight and gamma<1, every optimizer has exactly M+1 support points.
Article: main_krylov, thm:B, combining its lower and upper support conclusions.
Proof: the genuine singular-design perturbation gives the lower bound; the
nonpositive sensitivity polynomial contact count gives the matching upper bound. -/
theorem optimal_interval_support_card_eq (I : chebyshev1.SpectralInterval) (M : ℕ)
    (w : Fin (M + 1) → ℝ) (hw : ∀ i, 0 ≤ w i) {γ : ℝ} (hγ₀ : 0 < γ) (hγ₁ : γ < 1)
    (ν : ProbabilityMeasure (Spectrum I))
    (hopt : ∀ η, intervalObjective I (M + 1) w γ η ≤ intervalObjective I (M + 1) w γ ν)
    (hlast : 0 < w (Fin.last M)) :
    (ν : Measure (Spectrum I)).support.Finite ∧ (ν : Measure (Spectrum I)).support.ncard = M + 2 := by
  have hb := optimal_interval_support_bound I (M + 1) w hw hγ₀ hγ₁.le ν hopt (Fin.last M) hlast
  have hl := optimal_interval_support_card I M w hw hγ₀ hγ₁ ν hopt hlast
  exact ⟨hb.1, le_antisymm hb.2 (hl.resolve_left hb.1.not_infinite)⟩

/-- The article's support-cardinal hypothesis gives the complete optimality equivalence and equality on the actual support.
Article: main_krylov, thm:B, the original-domain equivalence theorem.
Proof: derive every positive moment matrix from actual support points before
applying the proved directional derivative and global tangent certificate. -/
theorem intervalObjective_equivalence_of_support_card (I : chebyshev1.SpectralInterval)
    (M : ℕ) (w : Fin M → ℝ) (hw : ∀ i, 0 ≤ w i) {γ : ℝ} (hγ₀ : 0 < γ) (hγ₁ : γ ≤ 1)
    (ν : ProbabilityMeasure (Spectrum I))
    (hcard : (M + 1 : ℕ∞) ≤ (ν : Measure (Spectrum I)).support.encard) :
    let hG := exists_positive_moments_of_support_card I M ν hcard
    let p := momentCompetitors I M ν hG
    ((∀ η, intervalObjective I M w γ η ≤ intervalObjective I M w γ ν) ↔
      ∀ t : Spectrum I, sensitivity M w γ 0 (spectralCoordinate I) ν p t ≤ intervalObjective I M w γ ν) ∧
    ((∀ η, intervalObjective I M w γ η ≤ intervalObjective I M w γ ν) →
      ∀ t ∈ (ν : Measure (Spectrum I)).support,
        sensitivity M w γ 0 (spectralCoordinate I) ν p t = intervalObjective I M w γ ν) := by
  dsimp only
  let hG := exists_positive_moments_of_support_card I M ν hcard
  refine ⟨intervalObjective_optimal_iff_sensitivity I M w hw hγ₀ hγ₁ ν hG, ?_⟩
  intro hopt
  apply sensitivity_eq_on_support_of_certificate M w hw γ 0 (spectralCoordinate I) ν _ _
    (sensitivity_le_of_optimal_interval I M w hγ₀ ν hG hopt)
  intro i
  rw [christoffel_eq_moment_inverse I _ ν (hG i)]
  exact inv_pos.mpr (hG i).inv.diag_pos

/-- The exact optimality test uses a genuine attained maximum of the sensitivity, and the same maximum gives the universal upper certificate.
Article: main_krylov, thm:B, the printed maximum formulation and certificate.
Proof: continuous compact maximization, the proved pointwise equivalence theorem,
and the original global tangent bound, all on the full support-cardinal domain. -/
theorem intervalObjective_maximum_sensitivity_equivalence (I : chebyshev1.SpectralInterval)
    (M : ℕ) (w : Fin M → ℝ) (hw : ∀ i, 0 ≤ w i) {γ : ℝ} (hγ₀ : 0 < γ) (hγ₁ : γ ≤ 1)
    (ν : ProbabilityMeasure (Spectrum I))
    (hcard : (M + 1 : ℕ∞) ≤ (ν : Measure (Spectrum I)).support.encard) :
    let hG := exists_positive_moments_of_support_card I M ν hcard
    let p := momentCompetitors I M ν hG
    ∃ t : Spectrum I,
      (∀ u, sensitivity M w γ 0 (spectralCoordinate I) ν p u ≤ sensitivity M w γ 0 (spectralCoordinate I) ν p t) ∧
      ((∀ η, intervalObjective I M w γ η ≤ intervalObjective I M w γ ν) ↔
        sensitivity M w γ 0 (spectralCoordinate I) ν p t ≤ intervalObjective I M w γ ν) ∧
      ∀ η, intervalObjective I M w γ η ≤ intervalObjective I M w γ ν + γ *
        (sensitivity M w γ 0 (spectralCoordinate I) ν p t - intervalObjective I M w γ ν) := by
  dsimp only
  let hG := exists_positive_moments_of_support_card I M ν hcard
  let p := momentCompetitors I M ν hG
  have : Nonempty (Spectrum I) := ⟨⟨I.mu, le_rfl, I.mu_lt_L.le⟩⟩
  have hpos (i : Fin M) : 0 < christoffel (i.val + 1) 0 (spectralCoordinate I) ν := by
    rw [christoffel_eq_moment_inverse I _ ν (hG i)]
    exact inv_pos.mpr (hG i).inv.diag_pos
  obtain ⟨t, ht, hcert⟩ := exists_maximum_sensitivity_certificate M w hw hγ₀.le hγ₁
    0 (spectralCoordinate I) ν p hpos
  refine ⟨t, ht, ?_, hcert⟩
  rw [intervalObjective_optimal_iff_sensitivity I M w hw hγ₀ hγ₁ ν hG]
  exact ⟨fun h => h t, fun h u => (ht u).trans h⟩

end
end krylov.Design
