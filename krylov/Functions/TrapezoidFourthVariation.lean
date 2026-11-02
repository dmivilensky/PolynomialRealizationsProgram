import krylov.Functions.AnchoredTrapezoid
import Mathlib.Analysis.Calculus.MeanValue

/-!
Article: main_krylov, thm:Fexact, fourth-variation route to the same remainder.
Use: a bound on the genuine mixed fourth variation implies the required
Lipschitz third variation on every convex domain. The diagonal-only fourth
variation formulation additionally requires Banach's symmetric tensor theorem.
Source: Appendix G and mathlib's convex-domain mean value theorem.
-/

namespace krylov.Functions
noncomputable section
open Set
open scoped NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A genuine bounded mixed fourth derivative makes the third variation Lipschitz.
Article: main_krylov, thm:Fexact, the mixed-norm M4 variant.
Proof: fix the three tensor arguments, bound the actual derivative's operator
norm, and use the imported mean value theorem on the original convex set. -/
theorem thirdVariationLipschitzOn_of_fourthVariation
    (T : E → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (U : E → E → E → E → E →L[ℝ] ℝ) (S : Set E) (hS : Convex ℝ S)
    (hU : ∀ z ∈ S, ∀ u v w,
      HasFDerivAt (fun p => T p u v w) (U z u v w) z)
    (M : ℝ≥0)
    (hM : ∀ z ∈ S, ∀ u v w h,
      |U z u v w h| ≤ (M : ℝ) * ‖h‖ * ‖u‖ * ‖v‖ * ‖w‖) :
    ThirdVariationLipschitzOn T M S := by
  intro p hp q hq u v w
  let C : ℝ := (M : ℝ) * ‖u‖ * ‖v‖ * ‖w‖
  have hC : 0 ≤ C := by positivity
  have hbound z (hz : z ∈ S) : ‖U z u v w‖ ≤ C := by
    apply ContinuousLinearMap.opNorm_le_bound _ hC
    intro h
    calc
      ‖U z u v w h‖ = |U z u v w h| := Real.norm_eq_abs _
      _ ≤ (M : ℝ) * ‖h‖ * ‖u‖ * ‖v‖ * ‖w‖ := hM z hz u v w h
      _ = C * ‖h‖ := by dsimp only [C]; ring
  have hb := hS.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z hz => (hU z hz u v w).hasFDerivWithinAt) hbound hq hp
  rw [Real.norm_eq_abs] at hb
  convert! hb using 1
  dsimp only [C]
  ring

/-- The full anchored remainder follows from a bound on the actual mixed fourth variation.
Article: main_krylov, thm:Fexact, M4 in place of L3.
Proof: derive genuine Lipschitz control of the third derivative, then reuse
the already proved arbitrary-anchor theorem with all of its sharp constants. -/
theorem anchored_trapezoid_remainder_fourthVariation
    (f : E → ℝ) (D : E → E →L[ℝ] ℝ)
    (H : E → E →L[ℝ] E →L[ℝ] ℝ)
    (T : E → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (U : E → E → E → E → E →L[ℝ] ℝ) (S : Set E) (hS : Convex ℝ S)
    (hD : ∀ z ∈ S, HasFDerivAt f (D z) z)
    (hH : ∀ z ∈ S, HasFDerivAt D (H z) z)
    (hT : ∀ z ∈ S, HasFDerivAt H (T z) z)
    (hU : ∀ z ∈ S, ∀ u v w,
      HasFDerivAt (fun p => T p u v w) (U z u v w) z)
    (M : ℝ≥0)
    (hM : ∀ z ∈ S, ∀ u v w h,
      |U z u v w h| ≤ (M : ℝ) * ‖h‖ * ‖u‖ * ‖v‖ * ‖w‖)
    (a s x : E) (ha : a ∈ S) (hb : a + s ∈ S) (hx : x ∈ S) (l : ℝ) :
    let δ := f (a + s) - f a - (D a s + D (a + s) s) / 2
    let w := x - (a + (1 / 2 : ℝ) • s) - l • s
    ∃ R : ℝ,
      (D (a + s) - D a) s - 12 * l * δ - H x s s =
        -T (a + s) w s s + R ∧
      |R| ≤ (M : ℝ) * ((1 / 12 + 1 / 2 * |l - 1 / 2|) * ‖s‖ ^ 4 +
        1 / 2 * ‖x - (a + s)‖ ^ 2 * ‖s‖ ^ 2) :=
  anchored_trapezoid_remainder f D H T S hS hD hH hT M
    (thirdVariationLipschitzOn_of_fourthVariation T U S hS hU M hM) a s x ha hb hx l

end
end krylov.Functions
