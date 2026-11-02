import krylov.Information.NormalizedLower

/-!
Article: main_krylov, s4:cor-Q, actual inner-subclass sharp witnesses.
Use: place the genuine signed physical lower scenarios in the original
pre-quadratic inner source class with only a uniform cubic loss.
Source: actual terminal-fibre CG probe geometry, original scaled physical
admissibility and proved sharp-coefficient homogeneity.
-/

namespace krylov.Information
noncomputable section
open krylov.Correction

/-- Scaling every primitive budget by the exact original inner slack changes the true sharp coefficient by only the stated cubic loss, including all zero profiles.
Use: Transfer the genuine signed-source lower bound into the original inner subclass with the same leading sharp constant.
Article: main_krylov, s4:cor-Q, inner-class sharp attainment.
Proof: The proved exact degree-two homogeneity gives the scaled sharp coefficient. Its lost fraction is at most 8nW, while K is at most (W+w)^2; the scaled cubic remainder is no larger than the original one. -/
theorem inner_sharp_cubic_loss (n W w C R : ℝ) (hn : 0≤n) (hW : 0≤W) (hw : 0≤w)
    (hC : 0≤C) (hslack : 4*n*W≤1)
    (hR : sharpConstant ((1-4*n*W)*W) ((1-4*n*W)*w)-C*((1-4*n*W)*(W+w))^3≤R) :
    sharpConstant W w-(C+8*n)*(W+w)^3≤R := by
  -- Retain the exact common inner slack until applying degree-two homogeneity.
  let θ := 1-4*n*W
  have hθ : 0≤θ := by dsimp only [θ]; linarith
  have hθ₁ : θ≤1 := by dsimp only [θ]; nlinarith
  have hK : 0≤sharpConstant W w := sharpConstant_nonneg hW hw
  have hKs : sharpConstant W w≤(W+w)^2 := (sharpConstant_upper hW hw).trans (by nlinarith)
  have hhom : sharpConstant (θ*W) (θ*w)=θ^2*sharpConstant W w := sharpConstant_homogeneous hW hw hθ
  have hloss : (1-θ^2)*sharpConstant W w≤8*n*(W+w)^3 := by
    have hsq : 1-θ^2≤8*n*W := by dsimp only [θ]; nlinarith [sq_nonneg (4*n*W)]
    calc
      _ ≤ (8*n*W)*sharpConstant W w := mul_le_mul_of_nonneg_right hsq hK
      _ ≤ (8*n*W)*(W+w)^2 := mul_le_mul_of_nonneg_left hKs (by positivity)
      _ ≤ (8*n*(W+w))*(W+w)^2 := mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg _)
      _ = _ := by ring
  have hcube : C*(θ*(W+w))^3≤C*(W+w)^3 := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) (by nlinarith : θ*(W+w)≤W+w) 3) hC
  change sharpConstant (θ*W) (θ*w)-C*(θ*(W+w))^3≤R at hR
  rw [hhom] at hR
  nlinarith

end
end krylov.Information
