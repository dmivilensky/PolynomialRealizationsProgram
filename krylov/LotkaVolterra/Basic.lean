import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic

/-!
Article: `main_krylov`, `s3:eq:LV`, `apC:prop:LV`, and `apC:prop:g1`.

The concrete planar Lotka--Volterra field used to characterize the continuum
constant. This file proves its equilibrium algebra directly; no orbit or
stable-manifold hypothesis is hidden in the definitions.

Source: substitution and elimination in the polynomial field displayed in the
article. General local ODE existence is imported separately in `LocalFlow`.
-/
namespace krylov.LotkaVolterra
noncomputable section

/-- Squared-control component of the continuum feedback field. -/
def sRate (γ s U : ℝ) : ℝ := 2 * s * (s - 1 - γ * U)

/-- State-ratio component of the continuum feedback field. -/
def uRate (s U : ℝ) : ℝ := U * (s + 1 - U)

/-- The autonomous field `(LV_γ)`, with coordinates `(s,U)`. -/
def vectorField (γ : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (sRate γ z.1 z.2, uRate z.1 z.2)

/-- The positive physical quadrant of the feedback system. -/
def positiveQuadrant : Set (ℝ × ℝ) := {z | 0 < z.1 ∧ 0 < z.2}

/-- The first coordinate of the interior equilibrium, when `γ < 1`. -/
def saddleS (γ : ℝ) : ℝ := (1 + γ) / (1 - γ)

/-- The second coordinate of the interior equilibrium, when `γ < 1`. -/
def saddleU (γ : ℝ) : ℝ := 2 / (1 - γ)

/-- The interior equilibrium. Existence in the positive quadrant is proved
below under the actual parameter restrictions. -/
def saddlePoint (γ : ℝ) : ℝ × ℝ := (saddleS γ, saddleU γ)

/-- Equilibrium means that both components of the concrete field vanish. -/
def IsEquilibrium (γ : ℝ) (z : ℝ × ℝ) : Prop := vectorField γ z = 0

theorem isEquilibrium_iff (γ : ℝ) (z : ℝ × ℝ) :
    IsEquilibrium γ z ↔
      (z.1 = 0 ∨ z.1 - 1 - γ * z.2 = 0) ∧
      (z.2 = 0 ∨ z.1 + 1 - z.2 = 0) := by
  simp [IsEquilibrium, vectorField, sRate, uRate, Prod.ext_iff,
    mul_eq_zero]

theorem saddleS_pos {γ : ℝ} (hγ : 0 < γ) (hγ₁ : γ < 1) : 0 < saddleS γ := by
  exact div_pos (by linarith) (by linarith)

theorem saddleU_pos {γ : ℝ} (hγ₁ : γ < 1) : 0 < saddleU γ := by
  exact div_pos (by norm_num) (by linarith)

theorem saddleU_eq_saddleS_add_one {γ : ℝ} (hγ : γ ≠ 1) :
    saddleU γ = saddleS γ + 1 := by
  unfold saddleU saddleS
  field_simp
  grind

theorem saddleS_eq_one_add_mul_saddleU {γ : ℝ} (hγ : γ ≠ 1) :
    saddleS γ = 1 + γ * saddleU γ := by
  unfold saddleS saddleU
  field_simp
  grind

theorem saddlePoint_isEquilibrium {γ : ℝ} (hγ : γ ≠ 1) :
    IsEquilibrium γ (saddlePoint γ) := by
  rw [isEquilibrium_iff]
  constructor
  · right
    change saddleS γ - 1 - γ * saddleU γ = 0
    rw [saddleS_eq_one_add_mul_saddleU hγ]
    ring
  · right
    change saddleS γ + 1 - saddleU γ = 0
    rw [saddleU_eq_saddleS_add_one hγ]
    ring

/-- Solving the two nullcline equations gives the unique interior equilibrium.
The statement also excludes any other equilibrium outside the axes. -/
theorem equilibrium_eq_saddlePoint {γ : ℝ} (hγ : γ ≠ 1)
    {z : ℝ × ℝ} (hs : z.1 ≠ 0) (hU : z.2 ≠ 0)
    (hz : IsEquilibrium γ z) : z = saddlePoint γ := by
  obtain ⟨hs', hU'⟩ := (isEquilibrium_iff γ z).mp hz
  have ha := hs'.resolve_left hs
  have hb := hU'.resolve_left hU
  have hmul : γ * z.2 = γ * (z.1 + 1) :=
    congrArg (γ * ·) (by linarith : z.2 = z.1 + 1)
  have hden : 1 - γ ≠ 0 := by exact sub_ne_zero.mpr (Ne.symm hγ)
  apply Prod.ext
  · change z.1 = (1 + γ) / (1 - γ)
    apply (eq_div_iff hden).mpr
    nlinarith
  · change z.2 = 2 / (1 - γ)
    apply (eq_div_iff hden).mpr
    nlinarith

/-- Full equilibrium classification, not only the positive-quadrant case. -/
theorem equilibrium_classification {γ : ℝ} (hγ : γ ≠ 1) (z : ℝ × ℝ) :
    IsEquilibrium γ z ↔
      z = (0, 0) ∨ z = (1, 0) ∨ z = (0, 1) ∨ z = saddlePoint γ := by
  constructor
  · intro hz
    obtain ⟨hs, hU⟩ := (isEquilibrium_iff γ z).mp hz
    rcases eq_or_ne z.1 0 with hs0 | hs0
    · rcases hU with hU0 | hU0
      · exact Or.inl (Prod.ext hs0 hU0)
      · exact Or.inr (Or.inr (Or.inl (Prod.ext hs0 (by linarith))))
    · rcases eq_or_ne z.2 0 with hU0 | hU0
      · exact Or.inr (Or.inl (Prod.ext (by
          have := hs.resolve_left hs0
          simp only [hU0, mul_zero, sub_zero] at this
          linarith) hU0))
      · exact Or.inr (Or.inr (Or.inr (equilibrium_eq_saddlePoint hγ hs0 hU0 hz)))
  · rintro (rfl | rfl | rfl | rfl)
    · simp [IsEquilibrium, vectorField, sRate, uRate]
    · simp [IsEquilibrium, vectorField, sRate, uRate]
    · simp [IsEquilibrium, vectorField, sRate, uRate]
    · exact saddlePoint_isEquilibrium hγ

/-- Proposition `apC:prop:LV`, equilibrium existence and uniqueness in `Q`. -/
theorem positive_equilibrium_iff {γ : ℝ} (hγ₁ : γ < 1)
    {z : ℝ × ℝ} (hz : z ∈ positiveQuadrant) :
    IsEquilibrium γ z ↔ z = saddlePoint γ := by
  refine ⟨equilibrium_eq_saddlePoint (ne_of_lt hγ₁)
    (ne_of_gt hz.1) (ne_of_gt hz.2), ?_⟩
  rintro rfl
  exact saddlePoint_isEquilibrium (ne_of_lt hγ₁)

/-- At `γ = 1` the only equilibria lie on the axes. -/
theorem endpoint_equilibrium_classification (z : ℝ × ℝ) :
    IsEquilibrium 1 z ↔ z = (0, 0) ∨ z = (1, 0) ∨ z = (0, 1) := by
  constructor
  · intro hz
    obtain ⟨hs, hU⟩ := (isEquilibrium_iff 1 z).mp hz
    rcases hs with hs | hs
    · rcases hU with hU | hU
      · exact Or.inl (Prod.ext hs hU)
      · exact Or.inr (Or.inr (Prod.ext hs (by linarith)))
    · rcases hU with hU | hU
      · have hs₁ : z.1 = 1 := by
          simp only [hU, mul_zero, sub_zero] at hs
          linarith
        exact Or.inr (Or.inl (Prod.ext hs₁ hU))
      · linarith
  · rintro (rfl | rfl | rfl) <;>
      simp [IsEquilibrium, vectorField, sRate, uRate]

/-- Proposition `apC:prop:g1`: no equilibrium is available in the positive
quadrant at the endpoint parameter. -/
theorem no_positive_equilibrium_endpoint {z : ℝ × ℝ}
    (hz : z ∈ positiveQuadrant) : ¬ IsEquilibrium 1 z := by
  intro h
  rcases (endpoint_equilibrium_classification z).mp h with rfl | rfl | rfl <;>
    simp [positiveQuadrant] at hz

end
end krylov.LotkaVolterra
