import krylov.Strings.DiscreteMeasure
import krylov.Strings.Mass
import Mathlib.Analysis.Complex.Norm
import Mathlib.Probability.CDF

/-!
Article: main_krylov, spectral-function definition before apC:prop:tauber.
Use: certify that the bare Fourier-isometry condition does not identify the
principal spectral measure when a mass-free tail is allowed. The same actual
two-atom physical mass has distinct Robin spectral measures, and both give
the exact complex Parseval identity for the same free-left eigenfunctions.
Source: the proved actual finite Stieltjes spectral dictionary. Tourigny,
arXiv:1101.2989, §1.1 instead defines the principal measure by the specified
Weyl characteristic function, which retains the right-end tying convention.
-/
namespace krylov.Strings.SpectralFunctionCounterexample
noncomputable section
open Set Real MeasureTheory Matrix Polynomial chebyshev1
open scoped BigOperators Matrix.Norms.L2Operator

/-- The actual two equal masses separated by a unit gap. Only the terminal
Robin parameter changes; the physical mass and free-left solutions do not. -/
def twoAtomString (ρ : ℝ) (hρ : 0 ≤ ρ) : DiscreteString 1 where
  mass _ := 1
  gap _ := 1
  mass_zero := rfl
  mass_pos _ _ := zero_lt_one
  gap_pos _ _ := zero_lt_one
  robin := ρ
  robin_nonneg := hρ

/-- The actual physical mass can be continued constantly along an infinite
mass-free tail without changing any L² mass function or its transform. -/
def physicalMass : Measure ℝ := Measure.dirac 0 + Measure.dirac 1

/-- A genuine global source Stieltjes string with this physical mass.
Its source length is infinite, and its mass is constant past position one. -/
def physicalString : Mass where
  cumulative := ProbabilityTheory.cdf (Measure.dirac 0) + ProbabilityTheory.cdf (Measure.dirac 1)
  origin := by simp [ProbabilityTheory.cdf_eq_real, Measure.real]
  negative x hx := by
    have hx₁ : ¬ (1 : ℝ) ≤ x := by linarith
    simp [ProbabilityTheory.cdf_eq_real, Measure.real, not_le.mpr hx, hx₁]

theorem physicalString_measure : physicalString.measure = physicalMass := by
  rw [Mass.measure, physicalString, StieltjesFunction.measure_add,
    ProbabilityTheory.measure_cdf, ProbabilityTheory.measure_cdf]
  rfl

theorem physicalString_plateau {x : ℝ} (hx : 1 ≤ x) : physicalString.cumulative x = 2 := by
  have hx₀ : (0 : ℝ) ≤ x := zero_le_one.trans hx
  norm_num [physicalString, ProbabilityTheory.cdf_eq_real, Measure.real, hx, hx₀]

/-- The genuine free-left generalized solution on the full physical
half-line, including its mass-free continuation beyond the second atom. -/
def freeSolution (x ξ : ℝ) : ℝ := 1 - ξ * x - ξ * (1 - ξ) * max (x - 1) 0

@[simp] theorem freeSolution_zero (ξ : ℝ) : freeSolution 0 ξ = 1 := by
  norm_num [freeSolution]

@[simp] theorem freeSolution_one (ξ : ℝ) : freeSolution 1 ξ = 1 - ξ := by
  simp [freeSolution]

/-- The displayed function is the actual free-left string solution at
every real spectral parameter, not only a chosen pair of nodal values. -/
theorem freeSolution_volterra (ξ : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    freeSolution x ξ = 1 - ξ * ∫ t in Icc 0 x, (x - t) * freeSolution t ξ ∂physicalMass := by
  have he : (∫ t in Icc 0 x, (x - t) * freeSolution t ξ ∂physicalMass) =
      x + if (1 : ℝ) ≤ x then (x - 1) * (1 - ξ) else 0 := by
    rw [← integral_indicator measurableSet_Icc, physicalMass,
      integral_add_measure (integrable_dirac (by finiteness)) (integrable_dirac (by finiteness)),
      integral_dirac, integral_dirac]
    rw [indicator_of_mem (show (0 : ℝ) ∈ Icc 0 x from ⟨le_rfl, hx⟩)]
    simp only [freeSolution_zero, sub_zero, mul_one]
    by_cases hx₁ : (1 : ℝ) ≤ x
    · rw [indicator_of_mem (show (1 : ℝ) ∈ Icc 0 x from ⟨zero_le_one, hx₁⟩), freeSolution_one,
        ite_eq_left hx₁]
    · rw [indicator_of_notMem (show (1 : ℝ) ∉ Icc 0 x from fun h ↦ hx₁ h.2), ite_eq_right hx₁]
  rw [he]
  by_cases hx₁ : (1 : ℝ) ≤ x
  · rw [ite_eq_left hx₁, freeSolution, max_eq_left (sub_nonneg.mpr hx₁)]
    ring
  · rw [ite_eq_right hx₁, freeSolution, max_eq_right (by linarith : x - 1 ≤ 0)]
    ring

/-- The actual Fourier integral against the original two-atom mass. -/
def transform (g : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  ∫ x, g x * (freeSolution x ξ : ℂ) ∂physicalMass

theorem transform_eq (g : ℝ → ℂ) (ξ : ℝ) :
    transform g ξ = g 0 + g 1 * ((1 - ξ : ℝ) : ℂ) := by
  rw [transform, physicalMass, integral_add_measure (integrable_dirac (by finiteness))
    (integrable_dirac (by finiteness))]
  simp

theorem physical_norm (g : ℝ → ℂ) :
    (∫ x, ‖g x‖ ^ 2 ∂physicalMass) = ‖g 0‖ ^ 2 + ‖g 1‖ ^ 2 := by
  rw [physicalMass, integral_add_measure (integrable_dirac (by finiteness))
    (integrable_dirac (by finiteness))]
  simp

theorem position_polynomials (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (twoAtomString ρ hρ).φPolynomial 0 = 1 ∧
      (twoAtomString ρ hρ).φPolynomial 1 = 1 - X := by
  simp [DiscreteString.φPolynomial_succ, twoAtomString, sub_eq_add_neg]

/-- Both actual Robin spectral measures obey the real Parseval identity
for the same physical eigenfunction values, independently of ρ. -/
theorem real_parseval (ρ : ℝ) (hρ : 0 ≤ ρ) (a b : ℝ) :
    (∫ ξ, (a + b * (1 - ξ)) ^ 2 ∂((twoAtomString ρ hρ).spectralMeasure : Measure ℝ)) = a ^ 2 + b ^ 2 := by
  let S := twoAtomString ρ hρ
  have h01 := S.spectralMeasure_orthogonality (0 : Fin 2) (1 : Fin 2)
  have h11 := S.spectralMeasure_orthogonality (1 : Fin 2) (1 : Fin 2)
  have hφ₀ : S.φPolynomial 0 = 1 := (position_polynomials ρ hρ).1
  have hφ₁ : S.φPolynomial 1 = 1 - X := (position_polynomials ρ hρ).2
  simp only [Fin.val_zero, Fin.val_one, hφ₀, hφ₁, eval_one, eval_sub, eval_X, one_mul,
    ite_eq_right (by decide : (0 : Fin 2) ≠ 1)] at h01
  simp only [Fin.val_one, hφ₁, eval_sub, eval_one, eval_X, ite_true] at h11
  have hmass : S.mass 1 = 1 := rfl
  rw [hmass, inv_one] at h11
  rw [S.spectralMeasure_integral] at h01 h11 ⊢
  have hprob := S.spectralData.probability
  calc
    _ = a ^ 2 * (∑ i, S.spectralData.weight i) +
        2 * a * b * (∑ i, S.spectralData.weight i * (1 - S.spectralData.node i)) +
        b ^ 2 * (∑ i, S.spectralData.weight i * ((1 - S.spectralData.node i) * (1 - S.spectralData.node i))) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [hprob, h01, h11]; ring

/-- Exact complex Parseval for the genuine original physical transform.
It holds for every function, hence in particular for all compactly
supported L² functions appearing in the article's bare isometry definition. -/
theorem complex_parseval (ρ : ℝ) (hρ : 0 ≤ ρ) (g : ℝ → ℂ) :
    (∫ ξ, ‖transform g ξ‖ ^ 2 ∂((twoAtomString ρ hρ).spectralMeasure : Measure ℝ)) =
      ∫ x, ‖g x‖ ^ 2 ∂physicalMass := by
  let S := twoAtomString ρ hρ
  have hr := real_parseval ρ hρ (g 0).re (g 1).re
  have hi := real_parseval ρ hρ (g 0).im (g 1).im
  rw [S.spectralMeasure_integral] at hr hi ⊢
  rw [physical_norm]
  simp only [transform_eq, Complex.sq_norm, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, zero_add] at hr hi ⊢
  simp only [← pow_two, mul_add, Finset.sum_add_distrib]
  rw [hr, hi]
  ring

private theorem power_reconstruct {n : ℕ} {H : Matrix (Fin n) (Fin n) ℝ}
    (B : SpectralBasis H) (k : ℕ) :
    H ^ k = B.Q * diagonal (fun i ↦ B.eigenvalues i ^ k) * B.Qᵀ := by
  induction k with
  | zero => simpa only [pow_zero, diagonal_one, Matrix.mul_one] using B.mul_transpose.symm
  | succ k ih =>
    rw [pow_succ, ih]
    calc
      _ = (B.Q * diagonal (fun i ↦ B.eigenvalues i ^ k) * B.Qᵀ) *
          (B.Q * diagonal B.eigenvalues * B.Qᵀ) :=
        congrArg (fun A ↦ (B.Q * diagonal (fun i ↦ B.eigenvalues i ^ k) * B.Qᵀ) * A) B.reconstruct.symm
      _ = B.Q * diagonal (fun i ↦ B.eigenvalues i ^ k) * (B.Qᵀ * B.Q) * diagonal B.eigenvalues * B.Qᵀ := by
        simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [B.transpose_mul, Matrix.mul_one,
          Matrix.mul_assoc B.Q (diagonal (fun i ↦ B.eigenvalues i ^ k)) (diagonal B.eigenvalues),
          diagonal_mul_diagonal]
        simp only [pow_succ]

/-- Actual spectral moments are matrix moments for the actual physical
eigenbasis, not merely for an arbitrarily chosen diagonalization. -/
theorem spectral_moment {N : ℕ} (S : DiscreteString N) (k : ℕ) :
    (∫ ξ, ξ ^ k ∂(S.spectralMeasure : Measure ℝ)) = (S.operator ^ k) 0 0 := by
  rw [S.spectralMeasure_integral, power_reconstruct S.spectralBasis k, Matrix.mul_apply]
  simp only [mul_diagonal, transpose_apply, DiscreteString.spectralData, SpectralBasis.weight]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem twoAtom_operator (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (twoAtomString ρ hρ).operator = !![1, -1; -1, 1 + ρ] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [DiscreteString.operator, vecMulVec_apply, DiscreteString.edgeVector, DiscreteString.lastVector, twoAtomString]

/-- The first moment detecting the different right boundary conditions.
The two measures have exactly the same free-left physical transform. -/
theorem third_moment (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (∫ ξ, ξ ^ 3 ∂((twoAtomString ρ hρ).spectralMeasure : Measure ℝ)) = 4 + ρ := by
  rw [spectral_moment, twoAtom_operator]
  norm_num [pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- A fully actual counterexample to uniqueness from the bare isometry
condition: two distinct nonnegative probability spectral measures give
Parseval for the same mass and the same generalized free-left solutions. -/
theorem distinct_isometric_measures :
    ∃ ν₀ ν₁ : ProbabilityMeasure ℝ, ν₀ ≠ ν₁ ∧
      (∀ g : ℝ → ℂ, (∫ ξ, ‖transform g ξ‖ ^ 2 ∂(ν₀ : Measure ℝ)) = ∫ x, ‖g x‖ ^ 2 ∂physicalMass) ∧
      (∀ g : ℝ → ℂ, (∫ ξ, ‖transform g ξ‖ ^ 2 ∂(ν₁ : Measure ℝ)) = ∫ x, ‖g x‖ ^ 2 ∂physicalMass) := by
  refine ⟨(twoAtomString 0 le_rfl).spectralMeasure, (twoAtomString 1 zero_le_one).spectralMeasure,
    ?_, complex_parseval 0 le_rfl, complex_parseval 1 zero_le_one⟩
  intro he
  have hμ : ((twoAtomString 0 le_rfl).spectralMeasure : Measure ℝ) =
      ((twoAtomString 1 zero_le_one).spectralMeasure : Measure ℝ) := congrArg (fun ν : ProbabilityMeasure ℝ ↦ (ν : Measure ℝ)) he
  have h0 := third_moment 0 le_rfl
  have h1 := third_moment 1 zero_le_one
  rw [hμ] at h0
  linarith

/-- Literal failure of the source's former uniqueness assertion with only
the bare Fourier-isometry condition. The actual source string is
`physicalString`, defined on the entire half-line and with a mass-free tail.
The principal energy realization must therefore be specified separately. -/
theorem bare_isometry_not_unique :
    ¬ ∃! ν : ProbabilityMeasure ℝ, ∀ g : ℝ → ℂ,
      (∫ ξ, ‖transform g ξ‖ ^ 2 ∂(ν : Measure ℝ)) = ∫ x, ‖g x‖ ^ 2 ∂physicalMass := by
  intro h
  obtain ⟨ν, _hν, hunique⟩ := h
  obtain ⟨ν₀, ν₁, hne, h₀, h₁⟩ := distinct_isometric_measures
  exact hne ((hunique ν₀ h₀).trans (hunique ν₁ h₁).symm)

end
end krylov.Strings.SpectralFunctionCounterexample
