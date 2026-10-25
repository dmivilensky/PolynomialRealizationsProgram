import polyak.Levels.Chart.TongueGraph
import Mathlib.Analysis.Convex.Function

/-! The literal `(a,D)` coordinates of the edge in Section 8.  No inverse
chart or geometric membership is built into these coordinates. -/
noncomputable section
namespace polyak.FareyPlateau
open General Levels Set

def edgeCoefficients (c₀ h₀ a D : ℝ) : Chart.Coefficients where
  c0 := h₀-(1+D)*c₀-a*c₀^2
  c1 := 1+D+2*a*c₀
  c2 := -a

theorem edgeCoefficients_eval (c₀ h₀ a D c : ℝ) :
    (edgeCoefficients c₀ h₀ a D).eval c = h₀+(1+D)*(c-c₀)-a*(c-c₀)^2 := by
  dsimp [edgeCoefficients, Chart.Coefficients.eval]
  ring

@[simp] theorem edgeCoefficients_center (c₀ h₀ a D : ℝ) :
    (edgeCoefficients c₀ h₀ a D).eval c₀=h₀ := by
  simp [edgeCoefficients_eval]

def edgeFace (c₀ h₀ c D : ℝ) : ℝ :=
  (h₀+(1+D)*(c-c₀))/(c-c₀)^2

def gapFace (c₀ h₀ c D : ℝ) : ℝ :=
  (h₀-1-c₀+D*(c-c₀))/(c-c₀)^2

def edgeBound (c₀ h₀ l r D : ℝ) : ℝ :=
  max (max (edgeFace c₀ h₀ 1 D) (edgeFace c₀ h₀ (-1) D))
    (max (gapFace c₀ h₀ l D) (gapFace c₀ h₀ r D))

theorem edgeFace_iff {c₀ h₀ c a D : ℝ} (hc : c≠c₀) :
    edgeFace c₀ h₀ c D<a ↔ (edgeCoefficients c₀ h₀ a D).eval c<0 := by
  rw [edgeFace, div_lt_iff₀ (sq_pos_of_ne_zero (sub_ne_zero.mpr hc)), edgeCoefficients_eval]
  constructor <;> intro h <;> nlinarith

theorem gapFace_iff {c₀ h₀ c a D : ℝ} (hc : c≠c₀) :
    gapFace c₀ h₀ c D<a ↔ (edgeCoefficients c₀ h₀ a D).eval c<1+c := by
  rw [gapFace, div_lt_iff₀ (sq_pos_of_ne_zero (sub_ne_zero.mpr hc)), edgeCoefficients_eval]
  constructor <;> intro h <;> nlinarith

theorem edgeBound_iff {c₀ h₀ l r a D : ℝ} (hc : c₀∈Ioo (-1:ℝ) 1)
    (hl : l<c₀) (hr : c₀<r) :
    edgeBound c₀ h₀ l r D<a ↔
      (edgeCoefficients c₀ h₀ a D).eval 1<0 ∧
      (edgeCoefficients c₀ h₀ a D).eval (-1)<0 ∧
      (edgeCoefficients c₀ h₀ a D).eval l<1+l ∧
      (edgeCoefficients c₀ h₀ a D).eval r<1+r := by
  simp only [edgeBound,max_lt_iff]
  rw [edgeFace_iff (ne_of_gt hc.2), edgeFace_iff (ne_of_lt hc.1),
    gapFace_iff (ne_of_lt hl), gapFace_iff (ne_of_gt hr)]
  tauto

@[fun_prop] theorem continuous_edgeBound (c₀ h₀ l r : ℝ) :
    Continuous (edgeBound c₀ h₀ l r) := by
  unfold edgeBound edgeFace gapFace
  fun_prop

@[fun_prop] theorem continuous_edgeCoefficients (c₀ h₀ : ℝ) :
    Continuous (fun p : ℝ×ℝ => edgeCoefficients c₀ h₀ p.1 p.2) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun p : ℝ×ℝ =>
    (h₀-(1+p.2)*c₀-p.1*c₀^2, 1+p.2+2*p.1*c₀, -p.1))
  fun_prop

theorem convexOn_edgeBound (c₀ h₀ l r : ℝ) :
    ConvexOn ℝ univ (edgeBound c₀ h₀ l r) := by
  have ef (c : ℝ) : ConvexOn ℝ univ (edgeFace c₀ h₀ c) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ α β _ _ hab
    dsimp [edgeFace]
    apply le_of_eq
    linear_combination -((h₀+c-c₀)/(c-c₀)^2)*hab
  have gf (c : ℝ) : ConvexOn ℝ univ (gapFace c₀ h₀ c) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ α β _ _ hab
    dsimp [gapFace]
    apply le_of_eq
    linear_combination -((h₀-1-c₀)/(c-c₀)^2)*hab
  exact ((ef 1).sup (ef (-1))).sup ((gf l).sup (gf r))

theorem edgeBound_pos {c₀ h₀ l r D : ℝ} (hh : 1+c₀<h₀)
    (hl : l<c₀) (hr : c₀<r) : 0<edgeBound c₀ h₀ l r D := by
  have le_l : gapFace c₀ h₀ l D≤edgeBound c₀ h₀ l r D :=
    (le_max_left _ _).trans (le_max_right _ _)
  have le_r : gapFace c₀ h₀ r D≤edgeBound c₀ h₀ l r D :=
    (le_max_right _ _).trans (le_max_right _ _)
  rcases le_total D 0 with hD|hD
  · apply lt_of_lt_of_le _ le_l
    unfold gapFace
    apply div_pos _ (sq_pos_of_ne_zero (sub_ne_zero.mpr (ne_of_lt hl)))
    have hm := mul_nonneg_of_nonpos_of_nonpos hD (by linarith : l-c₀≤0)
    linarith
  · apply lt_of_lt_of_le _ le_r
    unfold gapFace
    apply div_pos _ (sq_pos_of_ne_zero (sub_ne_zero.mpr (ne_of_gt hr)))
    have hm := mul_nonneg hD (by linarith : 0≤r-c₀)
    linarith

end polyak.FareyPlateau
