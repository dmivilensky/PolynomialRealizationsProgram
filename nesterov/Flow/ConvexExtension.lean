import nesterov.Flow.Model
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
Article: Lemma `creduce`, the nonsmooth convex interpolation equivalence.
Use: uniformly bounded jets with pairwise supports are interpolated by the
finite-valued supremum of their affine supports.  This intermediate result
does not assert differentiability; Lemma `extend` supplies smooth witnesses.
-/

noncomputable section

namespace nesterov.Flow

open scoped InnerProductSpace

variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def SupportFeasible (x G : I → E) (F : I → ℝ) : Prop :=
  ∀ i j, F j + ⟪G j, x i - x j⟫_ℝ ≤ F i

def supportSet (x G : I → E) (F : I → ℝ) (u : E) : Set ℝ :=
  Set.range fun i => F i + ⟪G i, u - x i⟫_ℝ

def supportEnvelope (x G : I → E) (F : I → ℝ) (u : E) : ℝ :=
  sSup (supportSet x G F u)

omit [CompleteSpace E] in
theorem supportSet_bddAbove {x G : I → E} {F : I → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hbounded : ∀ i, |F i| ≤ B ∧ ‖G i‖ ≤ B ∧ ‖x i‖ ≤ B) (u : E) :
    BddAbove (supportSet x G F u) := by
  refine ⟨B + B * (‖u‖ + B), ?_⟩
  rintro _ ⟨i, rfl⟩
  have hi := hbounded i
  have hnorm : ‖u - x i‖ ≤ ‖u‖ + B := (norm_sub_le _ _).trans (by linarith [hi.2.2])
  have hinner := real_inner_le_norm (G i) (u - x i)
  have hm := mul_le_mul hi.2.1 hnorm (norm_nonneg (u - x i)) hB
  have hf := (abs_le.mp hi.1).2
  linarith

omit [CompleteSpace E] in
theorem exists_convex_support_interpolant {x G : I → E} {F : I → ℝ} {B : ℝ}
    (h : SupportFeasible x G F) (hB : 0 ≤ B)
    (hbounded : ∀ i, |F i| ≤ B ∧ ‖G i‖ ≤ B ∧ ‖x i‖ ≤ B)
    (star : I) (hx : x star = 0) (hG : G star = 0) (hF : F star = 0) :
    ∃ f : E → ℝ, ConvexOn ℝ Set.univ f ∧ f 0 = 0 ∧
      (∀ u, 0 ≤ f u) ∧ ∀ i, f (x i) = F i ∧
        ∀ u, f (x i) + ⟪G i, u - x i⟫_ℝ ≤ f u := by
  let f := supportEnvelope x G F
  have hbd (u : E) := supportSet_bddAbove hB hbounded u
  have hs (u : E) : (supportSet x G F u).Nonempty := ⟨_, ⟨star, rfl⟩⟩
  have hle (u : E) (i : I) : F i + ⟪G i, u - x i⟫_ℝ ≤ f u :=
    le_csSup (hbd u) ⟨i, rfl⟩
  have hdata (i : I) : f (x i) = F i := by
    apply le_antisymm
    · apply csSup_le (hs (x i))
      rintro _ ⟨j, rfl⟩
      exact h i j
    · simpa only [sub_self, inner_zero_right, add_zero] using hle (x i) i
  refine ⟨f, ⟨convex_univ, ?_⟩, ?_, ?_, ?_⟩
  · intro u _ v _ a b ha hb hab
    change f (a • u + b • v) ≤ a * f u + b * f v
    apply csSup_le (hs _)
    rintro _ ⟨i, rfl⟩
    have h1 := mul_le_mul_of_nonneg_left (hle u i) ha
    have h2 := mul_le_mul_of_nonneg_left (hle v i) hb
    have hi : ⟪G i, a • u + b • v - x i⟫_ℝ =
        a * ⟪G i, u - x i⟫_ℝ + b * ⟪G i, v - x i⟫_ℝ := by
      simp only [inner_sub_right, inner_add_right, inner_smul_right]
      nlinarith [congrArg (fun r : ℝ => r * ⟪G i, x i⟫_ℝ) hab]
    change F i + ⟪G i, a • u + b • v - x i⟫_ℝ ≤ a * f u + b * f v
    rw [hi]
    have hf : a * F i + b * F i = F i := by
      nlinarith [congrArg (fun r : ℝ => r * F i) hab]
    nlinarith
  · simpa [hx, hF] using hdata star
  · intro u
    simpa [hx, hG, hF] using hle u star
  · intro i
    exact ⟨hdata i, fun u => by rw [hdata i]; exact hle u i⟩

end nesterov.Flow
