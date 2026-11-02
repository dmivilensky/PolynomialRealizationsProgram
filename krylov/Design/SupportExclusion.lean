import krylov.Design.SharpLobatto
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Data.Set.Card

/-!
Article: main_krylov, thm:B, support-size lower bound for every maximizer.
Use: exclude any singular design whose positively weighted highest information
vanishes, then apply an explicit annihilating polynomial to arbitrary finitely
supported probability measures.
Source: the standard singular-design perturbation argument for concave
c-information criteria (Pukelsheim, 1993). The gain is of order s^gamma and the
loss is at most linear; both estimates are proved for the actual objective.
-/

namespace krylov.Design
noncomputable section
open Polynomial MeasureTheory Filter
open scoped BigOperators Topology NNReal

/-- A positive fractional-power gain strictly dominates a bounded linear loss near zero.
Article: main_krylov, thm:B, singular-design perturbation.
Proof: choose an explicit positive mixing mass using the reciprocal exponent. -/
theorem exists_fractional_gain {A c γ : ℝ} (hA : 0 ≤ A) (hc : 0 < c)
    (hγ₁ : γ < 1) :
    ∃ s : ℝ, 0 < s ∧ s < 1 ∧ A < (1 - s) * A + c * s ^ γ := by
  let t : ℝ := min (1 / 2) (c / (2 * (A + 1)))
  have ht : 0 < t := lt_min (by norm_num) (div_pos hc (by positivity))
  have ht1 : t < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have htc : t * (A + 1) < c := by
    have h := min_le_right (1 / 2 : ℝ) (c / (2 * (A + 1)))
    have he : c / (2 * (A + 1)) * (A + 1) = c / 2 := by field_simp
    have hb := mul_le_mul_of_nonneg_right h (by positivity : 0 ≤ A + 1)
    rw [he] at hb
    dsimp [t]
    linarith
  let s : ℝ := t ^ (1 / (1 - γ))
  have hs : 0 < s := Real.rpow_pos_of_pos ht _
  have hs1 : s < 1 := by
    simpa only [Real.one_rpow] using
      Real.rpow_lt_rpow ht.le ht1 (by positivity : 0 < 1 / (1 - γ))
  have hpow : s ^ (1 - γ) = t := by
    dsimp [s]
    rw [← Real.rpow_mul ht.le]
    have he : 1 / (1 - γ) * (1 - γ) = 1 := by field_simp [ne_of_gt (sub_pos.mpr hγ₁)]
    rw [he, Real.rpow_one]
  have hsplit : s = s ^ γ * t := by
    rw [← hpow, ← Real.rpow_add hs]
    simp
  have hAt : A * t < c := by nlinarith
  have hgain : A * s < c * s ^ γ := by
    nth_rw 1 [hsplit]
    nlinarith [mul_pos (Real.rpow_pos_of_pos hs γ) (sub_pos.mpr hAt)]
  exact ⟨s, hs, hs1, by nlinarith⟩

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [CompactSpace X] [BorelSpace X]

/-- Adding a positive design to a singular positively weighted component gives a strict improvement.
Article: main_krylov, thm:B, exclusion of singular maximizers.
Proof: all components lose at most their linear mixing fraction, while the zero
component gains its full fractional power. No differentiability at rank loss is assumed. -/
theorem mixedObjective_strict_improvement_of_zero (M : ℕ) (w : Fin M → ℝ)
    (hw : ∀ i, 0 ≤ w i) {γ : ℝ} (hγ₀ : 0 < γ) (hγ₁ : γ < 1)
    (a : ℝ) (x : C(X, ℝ)) (ν η : ProbabilityMeasure X) (j : Fin M)
    (hwj : 0 < w j) (hz : christoffel (j.val + 1) a x ν = 0)
    (hpos : 0 < christoffel (j.val + 1) a x η) :
    ∃ μ : ProbabilityMeasure X, mixedObjective M w γ a x ν < mixedObjective M w γ a x μ := by
  let A := mixedObjective M w γ a x ν
  let c := w j * (christoffel (j.val + 1) a x η) ^ γ
  have hc : 0 < c := mul_pos hwj (Real.rpow_pos_of_pos hpos γ)
  obtain ⟨s, hs, hs1, hgain⟩ := exists_fractional_gain
    (mixedObjective_nonneg M w hw γ a x ν) hc hγ₁
  let α : ℝ≥0 := ⟨1 - s, by linarith⟩
  let β : ℝ≥0 := ⟨s, hs.le⟩
  have hab : α + β = 1 := by ext; change (1 - s) + s = 1; ring
  let μ := mixture ν η α β hab
  have hregular (i : Fin M) :
      (1 - s) * (w i * (christoffel (i.val + 1) a x ν) ^ γ) ≤
        w i * (christoffel (i.val + 1) a x μ) ^ γ := by
    have hi := christoffel_mixture_le (i.val + 1) a x ν η α β hab
    have hl : (1 - s) * christoffel (i.val + 1) a x ν ≤
        christoffel (i.val + 1) a x μ := by
      have hn := mul_nonneg hs.le (christoffel_nonneg (i.val + 1) a x η)
      dsimp [α, β] at hi
      exact (le_add_of_nonneg_right hn).trans hi
    have hp := Real.rpow_le_rpow
      (mul_nonneg (by linarith : 0 ≤ 1 - s) (christoffel_nonneg (i.val + 1) a x ν)) hl hγ₀.le
    rw [Real.mul_rpow (by linarith : 0 ≤ 1 - s) (christoffel_nonneg _ _ _ _)] at hp
    have ha : 1 - s ≤ (1 - s) ^ γ :=
      Real.self_le_rpow_of_le_one (by linarith) (by linarith) hγ₁.le
    have hb := mul_le_mul_of_nonneg_right ha
      (Real.rpow_nonneg (christoffel_nonneg (i.val + 1) a x ν) γ)
    have hwbound := mul_le_mul_of_nonneg_left (hb.trans hp) (hw i)
    nlinarith
  have hspecial : c * s ^ γ ≤ w j * (christoffel (j.val + 1) a x μ) ^ γ := by
    have hi := christoffel_mixture_le (j.val + 1) a x ν η α β hab
    rw [hz, mul_zero, zero_add] at hi
    have hp := Real.rpow_le_rpow (mul_nonneg hs.le hpos.le) hi hγ₀.le
    rw [Real.mul_rpow hs.le hpos.le] at hp
    have hb := mul_le_mul_of_nonneg_left hp hwj.le
    dsimp [c]
    nlinarith
  have hsum : (1 - s) * A + c * s ^ γ ≤ mixedObjective M w γ a x μ := by
    have hpoint (i : Fin M) :
        (1 - s) * (w i * (christoffel (i.val + 1) a x ν) ^ γ) +
          (if i = j then c * s ^ γ else 0) ≤
        w i * (christoffel (i.val + 1) a x μ) ^ γ := by
      by_cases hij : i = j
      · subst i
        simpa [hz, Real.zero_rpow hγ₀.ne'] using hspecial
      · simpa [hij] using hregular i
    have hb := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
    simpa [A, mixedObjective, Finset.sum_add_distrib, ← Finset.mul_sum] using hb
  exact ⟨μ, hgain.trans_le hsum⟩

omit [CompactSpace X] [BorelSpace X] in
/-- A measure concentrated on finitely many non-exterior coordinates has zero high-degree information.
Article: main_krylov, thm:B, finite-support singularity.
Proof: normalize the actual product of the support factors and integrate its almost-everywhere zeros. -/
theorem christoffel_zero_of_ae_mem_finset (m : ℕ) (a : ℝ) (x : C(X, ℝ))
    (ν : ProbabilityMeasure X) (s : Finset ℝ) (hcard : s.card ≤ m) (ha : a ∉ s)
    (hs : ∀ᵐ t ∂(ν : Measure X), x t ∈ s) : christoffel m a x ν = 0 := by
  let P : ℝ[X] := ∏ r ∈ s, (Polynomial.X - C r)
  have hdeg : P.natDegree ≤ s.card := by simp [P]
  have hPa : P.eval a ≠ 0 := by
    simp only [P, eval_prod, eval_sub, eval_X, eval_C]
    exact Finset.prod_ne_zero_iff.mpr (fun r hr => sub_ne_zero.mpr (by
      intro he
      exact ha (he.symm ▸ hr)))
  let p : Competitor m a := ⟨(P.eval a)⁻¹ • P,
    (natDegree_smul_le _ _).trans (hdeg.trans hcard), by simp [hPa]⟩
  have he : polynomialEnergy x ν p.val = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hs] with t ht
    have hz : P.eval (x t) = 0 := by
      simp only [P, eval_prod, eval_sub, eval_X, eval_C]
      exact Finset.prod_eq_zero ht (sub_self _)
    simp [p, hz]
  exact le_antisymm ((christoffel_le m a x ν p).trans_eq he) (christoffel_nonneg _ _ _ _)

/-- Every optimal physical design has strictly positive information in its highest active degree.
Article: main_krylov, thm:B, all-maximizers support lower bound.
Proof: mix a hypothetical zero-information optimizer with the explicit positive Lobatto design. -/
theorem optimal_interval_christoffel_pos (I : chebyshev1.SpectralInterval) (M : ℕ)
    (w : Fin M → ℝ) (hw : ∀ i, 0 ≤ w i) {γ : ℝ} (hγ₀ : 0 < γ) (hγ₁ : γ < 1)
    (ν : ProbabilityMeasure (Spectrum I))
    (hopt : ∀ η, intervalObjective I M w γ η ≤ intervalObjective I M w γ ν)
    (j : Fin M) (hwj : 0 < w j) :
    0 < christoffel (j.val + 1) 0 (spectralCoordinate I) ν := by
  by_contra hn
  have hz := le_antisymm (le_of_not_gt hn) (christoffel_nonneg (j.val + 1) 0 (spectralCoordinate I) ν)
  have hpos : 0 < christoffel (j.val + 1) 0 (spectralCoordinate I)
      (lobattoProbability I (j.val + 1)) := by
    rw [christoffel_lobatto]
    exact sq_pos_of_pos (chebyshev_scale_pos I _)
  obtain ⟨η, hη⟩ := mixedObjective_strict_improvement_of_zero M w hw hγ₀ hγ₁ 0
    (spectralCoordinate I) ν _ j hwj hz hpos
  exact (not_lt_of_ge (hopt η)) hη

/-- A finite set covering the support of an optimizer must contain more points than every active degree.
Article: main_krylov, thm:B, support-size lower bound.
Proof: the support carries the whole measure; an insufficient finite cover gives
an actual normalized annihilator, contradicting the proved positive information. -/
theorem optimal_interval_support_cover_card (I : chebyshev1.SpectralInterval) (M : ℕ)
    (w : Fin M → ℝ) (hw : ∀ i, 0 ≤ w i) {γ : ℝ} (hγ₀ : 0 < γ) (hγ₁ : γ < 1)
    (ν : ProbabilityMeasure (Spectrum I))
    (hopt : ∀ η, intervalObjective I M w γ η ≤ intervalObjective I M w γ ν)
    (j : Fin M) (hwj : 0 < w j) (s : Finset (Spectrum I))
    (hs : (ν : Measure (Spectrum I)).support ⊆ (s : Set (Spectrum I))) :
    j.val + 2 ≤ s.card := by
  by_contra hn
  have hcard : (s.image Subtype.val).card ≤ j.val + 1 :=
    (Finset.card_image_le).trans (by omega)
  have ha : (0 : ℝ) ∉ s.image Subtype.val := by
    intro h
    obtain ⟨t, _, ht⟩ := Finset.mem_image.mp h
    have hpos := lt_of_lt_of_le I.mu_pos t.property.1
    exact (ne_of_gt hpos) ht
  have hae : ∀ᵐ t ∂(ν : Measure (Spectrum I)),
      spectralCoordinate I t ∈ s.image Subtype.val := by
    filter_upwards [(ν : Measure (Spectrum I)).support_mem_ae] with t ht
    exact Finset.mem_image.mpr ⟨t, hs ht, rfl⟩
  have hz := christoffel_zero_of_ae_mem_finset (j.val + 1) 0 (spectralCoordinate I)
    ν (s.image Subtype.val) hcard ha hae
  have hp := optimal_interval_christoffel_pos I M w hw hγ₀ hγ₁ ν hopt j hwj
  exact (ne_of_gt hp) hz

/-- Every maximizer has at least M+1 support points, admitting also infinite support.
Article: main_krylov, thm:B, the complete support lower bound when the last weight is positive.
Proof: apply the finite-cover theorem to the actual topological support, or retain its infinitude. -/
theorem optimal_interval_support_card (I : chebyshev1.SpectralInterval) (M : ℕ)
    (w : Fin (M + 1) → ℝ) (hw : ∀ i, 0 ≤ w i) {γ : ℝ} (hγ₀ : 0 < γ) (hγ₁ : γ < 1)
    (ν : ProbabilityMeasure (Spectrum I))
    (hopt : ∀ η, intervalObjective I (M + 1) w γ η ≤ intervalObjective I (M + 1) w γ ν)
    (hlast : 0 < w (Fin.last M)) :
    (ν : Measure (Spectrum I)).support.Infinite ∨
      M + 2 ≤ (ν : Measure (Spectrum I)).support.ncard := by
  by_cases hinf : (ν : Measure (Spectrum I)).support.Infinite
  · exact Or.inl hinf
  · right
    have hf := Set.not_infinite.mp hinf
    have hc := optimal_interval_support_cover_card I (M + 1) w hw hγ₀ hγ₁ ν hopt
      (Fin.last M) hlast hf.toFinset (by simp)
    rw [Set.ncard_eq_toFinset_card _ hf]
    exact hc

end
end krylov.Design
