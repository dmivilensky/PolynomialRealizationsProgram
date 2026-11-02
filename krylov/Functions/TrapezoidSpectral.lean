import krylov.Functions.AnchoredTrapezoid
import krylov.Tensor.CubicBanach

/-!
Article: main_krylov, thm:Fexact, spectral-norm third-variation regularity.
Use: connect the article's diagonal tensor Lipschitz bound to the proved full
anchored remainder without strengthening its regularity assumption.
Source: Banach38, the proved finite-dimensional real Hilbert cubic theorem.
-/

namespace krylov.Functions
noncomputable section
open Set
open scoped NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The article's diagonal spectral bound implies the full mixed third-variation bound.
Article: main_krylov, thm:Fexact, the original norm-sigma Lipschitz assumption.
Proof: apply the proved Banach theorem to the actual difference tensor at each pair of points. -/
theorem thirdVariationLipschitzOn_of_diagonal (T : E → SymmetricCubic E)
    (L : ℝ≥0) (S : Set E)
    (hdiag : ∀ p ∈ S, ∀ q ∈ S, ∀ h : E, ‖h‖ = 1 →
      |(T p).form h h h - (T q).form h h h| ≤ (L : ℝ) * ‖p - q‖) :
    ThirdVariationLipschitzOn (fun p => (T p).form) L S := by
  let : AddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.addCommGroup (R := ℝ) (R₂ := ℝ) (M := E) (M₂ := E →L[ℝ] E →L[ℝ] ℝ)
  intro p hp q hq u v w
  let R : SymmetricCubic E :=
    { form := (T p).form - (T q).form
      swap₁ := fun a b c => by
        change (T p).form a b c - (T q).form a b c = (T p).form b a c - (T q).form b a c
        rw [(T p).swap₁ a b c, (T q).swap₁ a b c]
      swap₂ := fun a b c => by
        change (T p).form a b c - (T q).form a b c = (T p).form a c b - (T q).form a c b
        rw [(T p).swap₂ a b c, (T q).swap₂ a b c] }
  have hd h (hh : ‖h‖ = 1) : |R.form h h h| ≤ (L : ℝ) * ‖p - q‖ := by
    exact hdiag p hp q hq h hh
  exact krylov.Tensor.cubic_diagonal_bound R ((L : ℝ) * ‖p - q‖) hd u v w

/-- The complete anchored remainder holds under the article's diagonal spectral Lipschitz bound.
Article: main_krylov, thm:Fexact, equation (trapezoid-remainder).
Proof: derive the genuine mixed estimate by Banach's theorem and reuse the
sharp Peano-kernel and anchor-displacement estimates. -/
theorem anchored_trapezoid_remainder_spectral (f : E → ℝ) (D : E → E →L[ℝ] ℝ)
    (H : E → E →L[ℝ] E →L[ℝ] ℝ) (T : E → SymmetricCubic E)
    (S : Set E) (hS : Convex ℝ S)
    (hD : ∀ z ∈ S, HasFDerivAt f (D z) z)
    (hH : ∀ z ∈ S, HasFDerivAt D (H z) z)
    (hT : ∀ z ∈ S, HasFDerivAt H (T z).form z)
    (L : ℝ≥0)
    (hdiag : ∀ p ∈ S, ∀ q ∈ S, ∀ h : E, ‖h‖ = 1 →
      |(T p).form h h h - (T q).form h h h| ≤ (L : ℝ) * ‖p - q‖)
    (a s x : E) (ha : a ∈ S) (hb : a + s ∈ S) (hx : x ∈ S) (l : ℝ) :
    let δ := f (a + s) - f a - (D a s + D (a + s) s) / 2
    let w := x - (a + (1 / 2 : ℝ) • s) - l • s
    ∃ R : ℝ,
      (D (a + s) - D a) s - 12 * l * δ - H x s s =
        -(T (a + s)).form w s s + R ∧
      |R| ≤ (L : ℝ) * ((1 / 12 + 1 / 2 * |l - 1 / 2|) * ‖s‖ ^ 4 +
        1 / 2 * ‖x - (a + s)‖ ^ 2 * ‖s‖ ^ 2) :=
  anchored_trapezoid_remainder f D H (fun p => (T p).form) S hS hD hH hT L
    (thirdVariationLipschitzOn_of_diagonal T L S hdiag) a s x ha hb hx l

end
end krylov.Functions
