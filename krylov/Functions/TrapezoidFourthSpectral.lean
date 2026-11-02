import krylov.Functions.TrapezoidFourthVariation
import krylov.Tensor.QuarticMaximum

/-!
Article: main_krylov, thm:Fexact, the original diagonal-only M4 hypothesis.
Use: derive the full sharp anchored remainder from the genuine symmetric
fourth derivative and its printed diagonal bound. No mixed fourth-variation
bound is assumed: the proved quartic Banach theorem supplies it.
Source: Appendix G and Banach38, both proved in the imported formalization.
-/

namespace krylov.Functions
noncomputable section
open Set krylov.Tensor
open scoped NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The genuine diagonal fourth-variation bound gives the full Lipschitz third variation.
Article: main_krylov, thm:Fexact, the original M4 alternative.
Proof: apply the proved quartic Banach identity, then the genuine convex-domain
mean value theorem to each evaluated third-derivative component. -/
theorem thirdVariationLipschitzOn_of_fourthDiagonal
    (T : E → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (Q : E → SymmetricQuartic E)
    (S : Set E) (hS : Convex ℝ S)
    (hQ : ∀ z ∈ S, ∀ u v w,
      HasFDerivAt (fun p => T p u v w) ((Q z).form u v w) z)
    (M : ℝ≥0) (hM : ∀ z ∈ S, ∀ h : E,
      |(Q z).form h h h h| ≤ (M : ℝ) * ‖h‖ ^ 4) :
    ThirdVariationLipschitzOn T M S := by
  apply thirdVariationLipschitzOn_of_fourthVariation T (fun z u v w => (Q z).form u v w) S hS hQ M
  intro z hz u v w h
  have hd a (ha : ‖a‖ = 1) : |(Q z).form a a a a| ≤ (M : ℝ) := by
    simpa only [ha, one_pow, mul_one] using hM z hz a
  have hb := quartic_diagonal_bound (Q z) (M : ℝ) hd u v w h
  convert! hb using 1
  ring

/-- The complete sharp anchored remainder holds under the article's diagonal-only fourth-derivative bound.
Article: main_krylov, thm:Fexact, M4 in place of L3 with exactly the printed constants.
Proof: derive mixed control from genuine quartic symmetry using Banach's
theorem, derive actual Lipschitz control, then reuse the proved Peano kernels. -/
theorem anchored_trapezoid_remainder_fourthDiagonal
    (f : E → ℝ) (D : E → E →L[ℝ] ℝ)
    (H : E → E →L[ℝ] E →L[ℝ] ℝ)
    (T : E → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (Q : E → SymmetricQuartic E)
    (S : Set E) (hS : Convex ℝ S)
    (hD : ∀ z ∈ S, HasFDerivAt f (D z) z)
    (hH : ∀ z ∈ S, HasFDerivAt D (H z) z)
    (hT : ∀ z ∈ S, HasFDerivAt H (T z) z)
    (hQ : ∀ z ∈ S, ∀ u v w,
      HasFDerivAt (fun p => T p u v w) ((Q z).form u v w) z)
    (M : ℝ≥0) (hM : ∀ z ∈ S, ∀ h : E,
      |(Q z).form h h h h| ≤ (M : ℝ) * ‖h‖ ^ 4)
    (a s x : E) (ha : a ∈ S) (hb : a + s ∈ S) (hx : x ∈ S) (l : ℝ) :
    let δ := f (a + s) - f a - (D a s + D (a + s) s) / 2
    let w := x - (a + (1 / 2 : ℝ) • s) - l • s
    ∃ R : ℝ,
      (D (a + s) - D a) s - 12 * l * δ - H x s s =
        -T (a + s) w s s + R ∧
      |R| ≤ (M : ℝ) * ((1 / 12 + 1 / 2 * |l - 1 / 2|) * ‖s‖ ^ 4 +
        1 / 2 * ‖x - (a + s)‖ ^ 2 * ‖s‖ ^ 2) :=
  anchored_trapezoid_remainder f D H T S hS hD hH hT M
    (thirdVariationLipschitzOn_of_fourthDiagonal T Q S hS hQ M hM) a s x ha hb hx l

end
end krylov.Functions
