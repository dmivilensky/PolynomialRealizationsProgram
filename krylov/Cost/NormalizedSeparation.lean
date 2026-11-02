import krylov.OneGradient.SpectralSharpSupremum
import krylov.Reference.EnergyPositive
import krylov.Correction.GatedUniformBounds

/-!
Article: main_krylov, thm:hier, normalization by the initial error.
Use: retain a positive one-gradient obstruction on an actual spectral class
with a common positive preterminal energy floor. The reference pair and its
constants are chosen before the competing method and the output budget.
Source: the genuine last-pivot endpoint adversary and positivity of every
active CG energy; no reference-normalization hypothesis is assumed.
-/

/-!
Article: krylov, Proposition C.11 [thm:hier].

Actual normalized energy-floor families force a first-order output loss for every observed-span
method, while gated RFC has a uniform quadratic bound and a known base yields a mixed rω+ω²
estimate.
The one-gradient lower bound is on constant prefixes; nondegeneracy/positive energy floors
belong to the stated restricted reference family.
-/

namespace krylov.Cost
noncomputable section
open Matrix Set krylov.Reference krylov.Secant krylov.Methods krylov.OneGradient
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

/-- The source nondegenerate spectral subclass constrains all energies
before the final reference step, normalized by the actual initial error. -/
def EnergyFloor {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ)
    (g : EuclideanSpace ℝ (Fin m)) (N : ℕ) (γ : ℝ) : Prop :=
  ∀ k < N, γ * ‖cgCanonicalError A g 0‖ ^ 2 ≤ cgEnergy A g k

/-- Every actual full-active reference has a strictly positive common
floor on its finitely many preterminal energies. -/
theorem exists_energy_floor {n : ℕ} (A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ)
    (hA : A.PosDef) (g : EuclideanSpace ℝ (Fin (n + 2)))
    (hcount : referenceAtomCount A hA g = n + 2) :
    ∃ γ : ℝ, 0 < γ ∧ EnergyFloor A g (n + 1) γ := by
  let f : Fin (n + 1) → ℝ := fun k ↦ cgEnergy A g k / (1 + ‖cgCanonicalError A g 0‖ ^ 2)
  let S := Finset.univ.image f
  have hS : S.Nonempty := Finset.image_nonempty.mpr Finset.univ_nonempty
  refine ⟨S.min' hS, ?_, ?_⟩
  · apply (Finset.lt_min'_iff S hS).2
    intro x hx
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hx
    exact div_pos (cgEnergy_pos A hA g k (by omega)) (by positivity)
  · intro k hk
    have hle : S.min' hS ≤ f ⟨k, hk⟩ :=
      Finset.min'_le S _ (Finset.mem_image.mpr ⟨⟨k, hk⟩, Finset.mem_univ _, rfl⟩)
    have hf := (le_div_iff₀ (by positivity : 0 < 1 + ‖cgCanonicalError A g 0‖ ^ 2)).mp hle
    have hmin : 0 ≤ S.min' hS := by
      apply Finset.le_min' S hS
      intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact div_nonneg (cgEnergy_pos A hA g i (by omega)).le (by positivity)
    dsimp only [f] at hf
    nlinarith

/-- The actual one-gradient output error normalized by the initial
canonical reference error, as in the information-separation proposition. -/
def initialScenarioError {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ)
    (g : EuclideanSpace ℝ (Fin m))
    (method : OneGradientMethod (EuclideanSpace ℝ (Fin m)))
    (B : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  ‖cgOperator (metricRoot A)⁻¹
    (method.outputGradient (cgOperator B)
      (oneGradientRun method (fun _ ↦ cgOperator A) g m))‖ /
    ‖cgCanonicalError A g 0‖

/-- A genuine spectral information fibre with a positive harmonic loss
exists in every physical dimension at least two. -/
theorem exists_positive_spectral_fibre (μ L : ℝ) (hμ : 0 < μ) (hμL : μ < L) (n : ℕ) :
    ∃ P : SpectralPriorReference n μ L, 0 < spectralPriorCoefficient P := by
  by_contra h
  push Not at h
  have hu := (spectral_prior_coefficient_isLUB μ L hμ hμL n).2
    (show (0 : ℝ) ∈ upperBounds (range (fun P : SpectralPriorReference n μ L ↦ spectralPriorCoefficient P)) from by
      rintro x ⟨P, rfl⟩
      exact h P)
  have hp : 0 < (L - μ) / (L + μ) := div_pos (sub_pos.mpr hμL) (by linarith)
  linarith

/-- The information lower bound remains uniformly positive after division
by the actual initial error. All references, their spectral bounds, active
atom counts and preterminal energy floors are genuine physical quantities.
Constants precede every method, subclass parameter and output budget. -/
theorem normalized_information_lower (μ L : ℝ) (hμ : 0 < μ) (hμL : μ < L) (n : ℕ) :
    ∃ γ₀ c : ℝ, 0 < γ₀ ∧ 0 < c ∧ ∀ γ : ℝ, 0 < γ → γ ≤ γ₀ →
      ∀ method : OneGradientMethod (EuclideanSpace ℝ (Fin (n + 2))),
      OneGradientSpanRestricted method → ∀ ω : ℝ, 0 ≤ ω → ω ≤ 1 →
      ∃ (A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) (hA : A.PosDef)
        (g : EuclideanSpace ℝ (Fin (n + 2))) (B : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ),
        referenceAtomCount A hA g = n + 2 ∧ (A - μ • 1).PosSemidef ∧
        (L • 1 - A).PosSemidef ∧ EnergyFloor A g (n + 1) γ ∧ B.IsSymm ∧
        relativeBudget A (B - A) ≤ ω ∧ c * ω ≤ initialScenarioError A g method B := by
  obtain ⟨P, hP⟩ := exists_positive_spectral_fibre μ L hμ hμL n
  let lo := spectralLowerPivot P.matrix P.positive P.gradient P.gradient_ne_zero P.full_support μ
  let hi := spectralUpperPivot P.matrix P.positive P.gradient P.gradient_ne_zero P.full_support L
  let C := fun b ↦ lanczosCompletion P.matrix P.positive P.gradient P.gradient_ne_zero P.full_support b
  have hends := spectral_fibre_endpoint_band P.matrix P.positive P.gradient P.gradient_ne_zero
    P.full_support μ L (spectral_prior_nonempty_fibre P)
  have hb (b : ℝ) (h : b ∈ ({lo, hi} : Set ℝ)) :
      (C b - μ • 1).PosSemidef ∧ (L • 1 - C b).PosSemidef := by
    rcases h with h | h
    · rw [h]
      exact hends.2.1
    · rw [mem_singleton_iff.mp h]
      exact hends.2.2
  have hp (b : ℝ) (h : b ∈ ({lo, hi} : Set ℝ)) : (C b).PosDef :=
    spectral_fibre_completion_positive P.matrix P.positive P.gradient P.gradient_ne_zero
      P.full_support μ b hμ (hb b h).1
  have hcl := hp lo (mem_insert _ _)
  have hch := hp hi (mem_insert_of_mem _ (mem_singleton _))
  have hcountl := completion_full_atoms P.matrix P.positive P.gradient P.gradient_ne_zero P.full_support lo hcl
  have hcounth := completion_full_atoms P.matrix P.positive P.gradient P.gradient_ne_zero P.full_support hi hch
  obtain ⟨γl, hγl, hfl⟩ := exists_energy_floor (C lo) hcl P.gradient hcountl
  obtain ⟨γh, hγh, hfh⟩ := exists_energy_floor (C hi) hch P.gradient hcounth
  let d := fun b ↦ ‖cgCanonicalError (C b) P.gradient (n + 1)‖ /
    ‖cgCanonicalError (C b) P.gradient 0‖
  have hil : 0 < ‖cgCanonicalError (C lo) P.gradient 0‖ :=
    norm_pos_iff.mpr (cgCanonicalError_initial_ne_zero (C lo) hcl P.gradient P.gradient_ne_zero)
  have hih : 0 < ‖cgCanonicalError (C hi) P.gradient 0‖ :=
    norm_pos_iff.mpr (cgCanonicalError_initial_ne_zero (C hi) hch P.gradient P.gradient_ne_zero)
  have hdl : 0 < d lo := div_pos (last_reference_denominator (C lo) hcl P.gradient (n + 1) hcountl).1 hil
  have hdh : 0 < d hi := div_pos (last_reference_denominator (C hi) hch P.gradient (n + 1) hcounth).1 hih
  refine ⟨min γl γh, spectralPriorCoefficient P * min (d lo) (d hi),
    lt_min hγl hγh, mul_pos hP (lt_min hdl hdh), ?_⟩
  intro γ _ hγ method hm ω hω hω1
  have hgap := (spectral_fibre_endpoint_gaps P.matrix P.positive P.gradient P.gradient_ne_zero
    P.full_support μ L hμ (spectral_prior_nonempty_fibre P)).1
  obtain ⟨b, hbe, B, hB, hbudget, hlower⟩ := fibre_method_endpoint_lower P.matrix P.positive P.gradient
    P.gradient_ne_zero P.full_support method hm lo hi (by linarith) hends.1 hω hω1
  have hC := hp b hbe
  have hcount := completion_full_atoms P.matrix P.positive P.gradient P.gradient_ne_zero P.full_support b hC
  have hi0 : 0 < ‖cgCanonicalError (C b) P.gradient 0‖ :=
    norm_pos_iff.mpr (cgCanonicalError_initial_ne_zero (C b) hC P.gradient P.gradient_ne_zero)
  have hlast := (last_reference_denominator (C b) hC P.gradient (n + 1) hcount).1
  have hf : EnergyFloor (C b) P.gradient (n + 1) γ := by
    intro k hk
    rcases hbe with he | he
    · rw [he]
      exact (mul_le_mul_of_nonneg_right (hγ.trans (min_le_left _ _)) (sq_nonneg _)).trans (hfl k hk)
    · rw [mem_singleton_iff.mp he]
      exact (mul_le_mul_of_nonneg_right (hγ.trans (min_le_right _ _)) (sq_nonneg _)).trans (hfh k hk)
  refine ⟨C b, hC, P.gradient, B, hcount, (hb b hbe).1, (hb b hbe).2, hf, hB, hbudget, ?_⟩
  have hd : min (d lo) (d hi) ≤ d b := by
    rcases hbe with he | he
    · rw [he]
      exact min_le_left _ _
    · rw [mem_singleton_iff.mp he]
      exact min_le_right _ _
  have hdm := (le_div_iff₀ hi0).mp hd
  have hraw := (le_div_iff₀ hlast).mp hlower
  have hw : 0 ≤ ω * spectralPriorCoefficient P := mul_nonneg hω hP.le
  have hmul := mul_le_mul_of_nonneg_left hdm hw
  apply (le_div_iff₀ hi0).mpr
  change _ ≤ ‖cgOperator (metricRoot (C b))⁻¹
    (method.outputGradient (cgOperator B) (oneGradientRun method (fun _ ↦ cgOperator (C b)) P.gradient (n + 2)))‖
  change ω * spectralPriorCoefficient P * ‖cgCanonicalError (C b) P.gradient (n + 1)‖ ≤ _ at hraw
  calc
    _ = (ω * spectralPriorCoefficient P) *
        (min (d lo) (d hi) * ‖cgCanonicalError (C b) P.gradient 0‖) := by ring
    _ ≤ (ω * spectralPriorCoefficient P) *
        ‖cgCanonicalError (C b) P.gradient (n + 1)‖ := hmul
    _ ≤ _ := hraw

end
end krylov.Cost
