import krylov.Design.SupportExclusion

/-!
Article: main_krylov, thm:B, support equality and the actual maximum certificate.
Use: finish the support conclusions of the proved sufficient sensitivity
criterion and realize the certificate bound as the maximum of the genuine
continuous sensitivity on the compact spectral space.
Source: Kiefer--Wolfowitz (1960), Kiefer (1974), Pukelsheim (1993).
-/

namespace krylov.Design
noncomputable section
open Set MeasureTheory Polynomial
open scoped BigOperators
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]

omit [CompactSpace X] [BorelSpace X] in
/-- The sensitivity is a genuine continuous function of the physical spectral point.
Article: main_krylov, thm:B. -/
theorem continuous_sensitivity (M : ℕ) (w : Fin M → ℝ) (γ a : ℝ) (x : C(X, ℝ))
    (ν : ProbabilityMeasure X) (p : ∀ i : Fin M, Competitor (i.val + 1) a) :
    Continuous (sensitivity M w γ a x ν p) := by
  unfold sensitivity
  fun_prop

/-- Every collection of admissible polynomials has sensitivity mean at least its design value.
Article: main_krylov, thm:B.
Proof: each genuine competitor energy dominates its Christoffel infimum. -/
theorem mixedObjective_le_integral_sensitivity (M : ℕ) (w : Fin M → ℝ)
    (hw : ∀ i, 0 ≤ w i) (γ a : ℝ) (x : C(X, ℝ)) (ν : ProbabilityMeasure X)
    (p : ∀ i : Fin M, Competitor (i.val + 1) a)
    (hpos : ∀ i : Fin M, 0 < christoffel (i.val + 1) a x ν) :
    mixedObjective M w γ a x ν ≤ ∫ t, sensitivity M w γ a x ν p t ∂ν := by
  rw [integral_sensitivity]
  apply Finset.sum_le_sum
  intro i _
  have hscale : (christoffel (i.val + 1) a x ν) ^ (γ - 1) *
      christoffel (i.val + 1) a x ν = (christoffel (i.val + 1) a x ν) ^ γ := by
    nth_rw 2 [← Real.rpow_one (christoffel (i.val + 1) a x ν)]
    rw [← Real.rpow_add (hpos i)]
    congr 1
    ring
  have hb := mul_le_mul_of_nonneg_left (christoffel_le (i.val + 1) a x ν (p i))
    (mul_nonneg (hw i) (Real.rpow_nonneg (hpos i).le (γ - 1)))
  simpa only [mul_assoc, hscale] using hb

/-- A tight pointwise sensitivity certificate has exactly the claimed average.
Article: main_krylov, thm:B.
Proof: the variational lower bound and the pointwise integral upper bound coincide. -/
theorem integral_sensitivity_eq_of_certificate (M : ℕ) (w : Fin M → ℝ)
    (hw : ∀ i, 0 ≤ w i) (γ a : ℝ) (x : C(X, ℝ)) (ν : ProbabilityMeasure X)
    (p : ∀ i : Fin M, Competitor (i.val + 1) a)
    (hpos : ∀ i : Fin M, 0 < christoffel (i.val + 1) a x ν)
    (hB : ∀ t, sensitivity M w γ a x ν p t ≤ mixedObjective M w γ a x ν) :
    (∫ t, sensitivity M w γ a x ν p t ∂ν) = mixedObjective M w γ a x ν := by
  apply le_antisymm
  · have hi := (continuous_sensitivity M w γ a x ν p).integrable_of_hasCompactSupport
      (μ := (ν : Measure X)) (HasCompactSupport.of_compactSpace _)
    simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using
      integral_mono hi (integrable_const (mixedObjective M w γ a x ν)) hB
  · exact mixedObjective_le_integral_sensitivity M w hw γ a x ν p hpos

/-- The sensitivity equals the objective at every point of the actual topological support.
Article: main_krylov, thm:B, equality on support.
Proof: the continuous nonnegative certificate gap has zero integral, hence
vanishes almost everywhere and on the whole measure support. This even holds
for arbitrary admissible competitors satisfying the tight certificate. -/
theorem sensitivity_eq_on_support_of_certificate (M : ℕ) (w : Fin M → ℝ)
    (hw : ∀ i, 0 ≤ w i) (γ a : ℝ) (x : C(X, ℝ)) (ν : ProbabilityMeasure X)
    (p : ∀ i : Fin M, Competitor (i.val + 1) a)
    (hpos : ∀ i : Fin M, 0 < christoffel (i.val + 1) a x ν)
    (hB : ∀ t, sensitivity M w γ a x ν p t ≤ mixedObjective M w γ a x ν) :
    ∀ t ∈ (ν : Measure X).support,
      sensitivity M w γ a x ν p t = mixedObjective M w γ a x ν := by
  let F : X → ℝ := fun t => mixedObjective M w γ a x ν - sensitivity M w γ a x ν p t
  have hc : Continuous F := continuous_const.sub (continuous_sensitivity M w γ a x ν p)
  have hi := hc.integrable_of_hasCompactSupport (μ := (ν : Measure X))
    (HasCompactSupport.of_compactSpace _)
  have he : (∫ t, F t ∂ν) = 0 := by
    rw [show F = (fun t => mixedObjective M w γ a x ν - sensitivity M w γ a x ν p t)
      from rfl]
    rw [integral_sub (integrable_const _)
      ((continuous_sensitivity M w γ a x ν p).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)),
      integral_sensitivity_eq_of_certificate M w hw γ a x ν p hpos hB]
    simp
  have hae : F =ᵐ[(ν : Measure X)] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun t => sub_nonneg.mpr (hB t)) hi).mp he
  have hs : (ν : Measure X).support ⊆ {t | F t = 0} :=
    Measure.support_subset_of_isClosed (isClosed_eq hc continuous_const) hae
  intro t ht
  exact sub_eq_zero.mp (hs ht) |>.symm

/-- The quantitative certificate uses an actual attained maximum of the sensitivity.
Article: main_krylov, thm:B, the displayed maximum-sensitivity certificate.
Proof: extreme-value theorem on the compact spectral space and the proved global tangent inequality. -/
theorem exists_maximum_sensitivity_certificate [Nonempty X] (M : ℕ) (w : Fin M → ℝ)
    (hw : ∀ i, 0 ≤ w i) {γ : ℝ} (hγ₀ : 0 ≤ γ) (hγ₁ : γ ≤ 1)
    (a : ℝ) (x : C(X, ℝ)) (ν : ProbabilityMeasure X)
    (p : ∀ i : Fin M, Competitor (i.val + 1) a)
    (hpos : ∀ i : Fin M, 0 < christoffel (i.val + 1) a x ν) :
    ∃ t : X, (∀ u, sensitivity M w γ a x ν p u ≤ sensitivity M w γ a x ν p t) ∧
      ∀ η : ProbabilityMeasure X, mixedObjective M w γ a x η ≤
        mixedObjective M w γ a x ν + γ *
          (sensitivity M w γ a x ν p t - mixedObjective M w γ a x ν) := by
  obtain ⟨t, _, ht⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty
    (continuous_sensitivity M w γ a x ν p).continuousOn
  have hb : ∀ u, sensitivity M w γ a x ν p u ≤ sensitivity M w γ a x ν p t :=
    fun u => ht (Set.mem_univ u)
  exact ⟨t, hb, mixedObjective_certificate M w hw hγ₀ hγ₁ a x ν p hpos _ hb⟩

end
end krylov.Design
