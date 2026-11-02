import krylov.Design.CertificateSupport
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
Article: main_krylov, thm:B, the genuine finite moment matrix.
Use: connect actual compact-measure polynomial energies to coefficient-space
quadratic forms and derive positive definiteness from actual support points.
Source: the standard moment-matrix representation of polynomial c-information;
mathlib supplies finite polynomial coefficients and Lagrange uniqueness.
-/

namespace krylov.Design
noncomputable section
open Polynomial MeasureTheory Matrix
open scoped BigOperators

/-- The actual moment Gram matrix of monomials, integrated against the original probability measure.
Article: main_krylov, thm:B, M_m. -/
def momentGram (I : chebyshev1.SpectralInterval) (m : ℕ)
    (ν : ProbabilityMeasure (Spectrum I)) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  fun i j => ∫ t : Spectrum I, t.val ^ i.val * t.val ^ j.val ∂ν

/-- Evaluation of mathlib's finite coefficient polynomial is the actual monomial expansion.
Article: main_krylov, thm:B. -/
theorem eval_ofFn_sum {N : ℕ} (a : Fin N → ℝ) (t : ℝ) :
    (Polynomial.ofFn N a).eval t = ∑ i : Fin N, a i * t ^ i.val := by
  rw [Polynomial.ofFn_eq_sum_monomial]
  simp only [eval_finsetSum, eval_monomial]

/-- The genuine moment Gram matrix is symmetric.
Article: main_krylov, thm:B. Proof: commute the two real monomial factors under the integral. -/
theorem momentGram_isSymm (I : chebyshev1.SpectralInterval) (m : ℕ)
    (ν : ProbabilityMeasure (Spectrum I)) : (momentGram I m ν).IsSymm := by
  ext i j
  change (∫ t : Spectrum I, t.val ^ j.val * t.val ^ i.val ∂ν) = _
  simp only [momentGram, mul_comm]

/-- Actual polynomial-square integration equals the coefficient-space moment quadratic form.
Article: main_krylov, thm:B, the displayed variational moment formula.
Proof: expand the square of the finite monomial sum and integrate every term. -/
theorem polynomialEnergy_eq_momentGram (I : chebyshev1.SpectralInterval) (m : ℕ)
    (ν : ProbabilityMeasure (Spectrum I)) (a : Fin (m + 1) → ℝ) :
    polynomialEnergy (spectralCoordinate I) ν (Polynomial.ofFn (m + 1) a) =
      a ⬝ᵥ (momentGram I m ν *ᵥ a) := by
  have hi (i j : Fin (m + 1)) : Integrable
      (fun t : Spectrum I => a i * (t.val ^ i.val * t.val ^ j.val) * a j) ν :=
    (by fun_prop : Continuous (fun t : Spectrum I =>
      a i * (t.val ^ i.val * t.val ^ j.val) * a j)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  calc
    _ = ∫ t : Spectrum I, ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
        a i * (t.val ^ i.val * t.val ^ j.val) * a j ∂ν := by
      unfold polynomialEnergy
      congr 1
      funext t
      rw [show spectralCoordinate I t = t.val from rfl, eval_ofFn_sum, pow_two,
        Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
        ∫ t : Spectrum I, a i * (t.val ^ i.val * t.val ^ j.val) * a j ∂ν := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
      apply Finset.sum_congr rfl
      intro i _
      exact integral_finsetSum _ (fun j _ => hi i j)
    _ = a ⬝ᵥ (momentGram I m ν *ᵥ a) := by
      simp only [dotProduct, mulVec, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_mul_const, integral_const_mul]
      change (a i * momentGram I m ν i j) * a j = _
      ring

/-- A polynomial of zero square energy vanishes on the actual topological support.
Article: main_krylov, thm:B, positive definiteness of the moment matrix.
Proof: its continuous nonnegative square vanishes almost everywhere and hence on the support. -/
theorem eval_zero_on_support_of_energy_zero (I : chebyshev1.SpectralInterval)
    (ν : ProbabilityMeasure (Spectrum I)) (p : ℝ[X])
    (he : polynomialEnergy (spectralCoordinate I) ν p = 0) :
    ∀ t ∈ (ν : Measure (Spectrum I)).support, p.eval t.val = 0 := by
  have hc : Continuous (fun t : Spectrum I => (p.eval t.val) ^ 2) :=
    (p.continuous.comp continuous_subtype_val).pow 2
  have hi := hc.integrable_of_hasCompactSupport (μ := (ν : Measure (Spectrum I)))
    (HasCompactSupport.of_compactSpace _)
  change (∫ t : Spectrum I, (p.eval t.val) ^ 2 ∂ν) = 0 at he
  have hae : (fun t : Spectrum I => (p.eval t.val) ^ 2) =ᵐ[(ν : Measure (Spectrum I))] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun t : Spectrum I => sq_nonneg (p.eval t.val)) hi).mp he
  have hs : (ν : Measure (Spectrum I)).support ⊆ {t : Spectrum I | (p.eval t.val) ^ 2 = 0} :=
    Measure.support_subset_of_isClosed (isClosed_eq hc continuous_const) hae
  intro t ht
  exact sq_eq_zero_iff.mp (hs ht)

/-- Enough actual support points make every nonzero degree-bounded polynomial energy strictly positive.
Article: main_krylov, thm:B, nonsingular moment domain.
Proof: a zero-energy polynomial vanishes at m+1 distinct support points;
Lagrange uniqueness then makes all its coefficients zero. -/
theorem polynomialEnergy_pos_of_support_points (I : chebyshev1.SpectralInterval) (m : ℕ)
    (ν : ProbabilityMeasure (Spectrum I)) (z : Fin (m + 1) → Spectrum I)
    (hz : Function.Injective z) (hs : ∀ i, z i ∈ (ν : Measure (Spectrum I)).support)
    (p : ℝ[X]) (hp : p.natDegree ≤ m) (hne : p ≠ 0) :
    0 < polynomialEnergy (spectralCoordinate I) ν p := by
  by_contra hn
  have he := le_antisymm (le_of_not_gt hn) (polynomialEnergy_nonneg (spectralCoordinate I) ν p)
  have hvan := eval_zero_on_support_of_energy_zero I ν p he
  have hinj : Function.Injective (fun i => (z i).val) := fun i j hij => hz (Subtype.ext hij)
  have hd : p.degree < (Finset.univ : Finset (Fin (m + 1))).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast Nat.lt_succ_of_le hp)
  have hpzero := Lagrange.eq_interpolate_of_eval_eq (r := fun _ => (0 : ℝ)) hinj.injOn hd
    (fun i _ => hvan (z i) (hs i))
  apply hne
  simpa using hpzero

/-- The genuine moment matrix is positive definite whenever the measure has m+1 distinct support points.
Article: main_krylov, thm:B, the printed positive moment-matrix domain.
Proof: coefficient injectivity and the proved positive actual polynomial-square integral. -/
theorem momentGram_posDef (I : chebyshev1.SpectralInterval) (m : ℕ)
    (ν : ProbabilityMeasure (Spectrum I)) (z : Fin (m + 1) → Spectrum I)
    (hz : Function.Injective z) (hs : ∀ i, z i ∈ (ν : Measure (Spectrum I)).support) :
    (momentGram I m ν).PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  refine ⟨?_, ?_⟩
  · exact Matrix.isHermitian_iff_isSymm.mpr (momentGram_isSymm I m ν)
  intro a ha
  rw [star_trivial, ← polynomialEnergy_eq_momentGram]
  apply polynomialEnergy_pos_of_support_points I m ν z hz hs
  · exact Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by omega) a)
  · intro h
    exact ha (Polynomial.injective_ofFn (m + 1) (by simpa using h))

end
end krylov.Design
