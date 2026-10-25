import polyak.FareyPlateau.Domain.Coordinates

/-! The negative endpoint face is redundant, including the gap K=2 where
the lower window endpoint is exactly -1. -/
noncomputable section
namespace polyak.FareyPlateau
open Set

theorem gapBound_pos {c₀ h₀ l r D : ℝ} (hh : 1+c₀<h₀)
    (hl : l<c₀) (hr : c₀<r) :
    0<max (gapFace c₀ h₀ l D) (gapFace c₀ h₀ r D) := by
  rcases le_total D 0 with hd|hd
  · apply lt_of_lt_of_le _ (le_max_left _ _)
    unfold gapFace
    apply div_pos _ (sq_pos_of_ne_zero (sub_ne_zero.mpr hl.ne))
    have := mul_nonneg_of_nonpos_of_nonpos hd (sub_nonpos.mpr hl.le)
    linarith
  · apply lt_of_lt_of_le _ (le_max_right _ _)
    unfold gapFace
    apply div_pos _ (sq_pos_of_ne_zero (sub_ne_zero.mpr hr.ne'))
    have := mul_nonneg hd (sub_nonneg.mpr hr.le)
    linarith

theorem negative_face_redundant {c₀ h₀ l r D : ℝ} (hc : -1<c₀)
    (hh : 1+c₀<h₀) (hlb : -1≤l) (hl : l<c₀) (hr : c₀<r) :
    edgeFace c₀ h₀ (-1) D≤max (gapFace c₀ h₀ l D) (gapFace c₀ h₀ r D) := by
  let M := max (gapFace c₀ h₀ l D) (gapFace c₀ h₀ r D)
  have hm : 0<M := gapBound_pos hh hl hr
  have hml := le_max_left (gapFace c₀ h₀ l D) (gapFace c₀ h₀ r D)
  change gapFace c₀ h₀ l D≤M at hml
  rw [gapFace,div_le_iff₀ (sq_pos_of_ne_zero (sub_ne_zero.mpr hl.ne))] at hml
  change (h₀+(1+D)*((-1)-c₀))/((-1)-c₀)^2≤M
  rw [div_le_iff₀ (sq_pos_of_ne_zero (sub_ne_zero.mpr hc.ne))]
  have hmul := mul_le_mul_of_nonneg_left hml (show 0≤c₀+1 by linarith)
  have haux : 0≤(l+1)*(M*(c₀-l)*(c₀+1)+(h₀-1-c₀)) :=
    mul_nonneg (by linarith) (add_nonneg
      (mul_nonneg (mul_nonneg hm.le (sub_pos.mpr hl).le) (by linarith))
      (by linarith))
  have hid : (M*((-1)-c₀)^2-(h₀+(1+D)*((-1)-c₀)))*(c₀-l) =
      (l+1)*(M*(c₀-l)*(c₀+1)+(h₀-1-c₀)) +
      (c₀+1)*(M*(l-c₀)^2-(h₀-1-c₀+D*(l-c₀))) := by ring
  have hp : 0≤(M*((-1)-c₀)^2-(h₀+(1+D)*((-1)-c₀)))*(c₀-l) := by
    rw [hid]
    nlinarith
  have := nonneg_of_mul_nonneg_left hp (sub_pos.mpr hl)
  linarith

theorem edgeBound_three_faces {c₀ h₀ l r D : ℝ} (hc : -1<c₀)
    (hh : 1+c₀<h₀) (hlb : -1≤l) (hl : l<c₀) (hr : c₀<r) :
    edgeBound c₀ h₀ l r D=max (edgeFace c₀ h₀ 1 D)
      (max (gapFace c₀ h₀ l D) (gapFace c₀ h₀ r D)) := by
  unfold edgeBound
  rw [max_assoc]
  rw [max_eq_right (negative_face_redundant hc hh hlb hl hr)]

end polyak.FareyPlateau
