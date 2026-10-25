import polyak.Certificates.PartII.Plateaus.Data
import polyak.CertifiedExamples.Plateaus.Root
import polyak.CertifiedExamples.Trigonometry

/-! These rejecting finite checks validate the proposed strict interval signs;
the source semantics and regularity assembly use the handwritten modules. -/
namespace polyak.Certificates.PartII.Plateaus
open LeanCert.Core
open polyak.CertifiedExamples.Plateaus chebyshev2.Numerics

theorem row18_right_positive :
    ∀ i, 0<(row18Right i).lo := by kernel_decide

theorem row18_left_positive :
    ∀ i, 0<(row18Left i).lo := by kernel_decide

theorem row18_dual_positive :
    ∀ p ∈ row18Dual, 0<p.2.lo := by kernel_decide

theorem row18_cosines_mem :
    ∀ i, (![Real.cos (2*Real.pi*3/18),Real.cos (2*Real.pi*4/18)] : Fin 2 → ℝ) i ∈ row18Cosines i := by
  intro i
  fin_cases i
  · have h := CertifiedExamples.Trigonometry.cos_bounds (2*3/18) 32 (24999999999999/50000000000000) (50000000000001/100000000000000)
      (by kernel_decide)
    have he : (((2*3/18):ℚ):ℝ)*Real.pi = 2*Real.pi*3/18 := by push_cast; ring
    rw [he] at h
    exact h
  · have h := CertifiedExamples.Trigonometry.cos_bounds (2*4/18) 32 (4341204441673/25000000000000) (3472963553339/20000000000000)
      (by kernel_decide)
    have he : (((2*4/18):ℚ):ℝ)*Real.pi = 2*Real.pi*4/18 := by push_cast; ring
    rw [he] at h
    exact h
theorem row18_endpoint0_sign : 0<determinant18 (10055082108856557/100000000000000) := by
  have h := IntervalExpr.strictNegative_sound (IntervalExpr.neg (determinant18Expr (10055082108856557/100000000000000))) row18Cosines
    (by kernel_decide) row18_cosines_mem
  change -(determinant18Expr (10055082108856557/100000000000000)).value ![Real.cos (2*Real.pi*3/18),Real.cos (2*Real.pi*4/18)] < 0 at h
  rw [determinant18Expr_value] at h
  push_cast at h
  exact neg_lt_zero.mp h

theorem row18_endpoint1_sign : determinant18 (10055082128856557/100000000000000)<0 := by
  have h := IntervalExpr.strictNegative_sound (determinant18Expr (10055082128856557/100000000000000)) row18Cosines
    (by kernel_decide) row18_cosines_mem
  rw [determinant18Expr_value] at h
  push_cast at h
  exact h

theorem row18_boundary_root :
    ∃ κ ∈ Set.Icc ((10055082108856557/100000000000000):ℝ) (10055082128856557/100000000000000), determinant18 κ=0 :=
  polynomial_root_from_opposite_signs continuous_determinant18 (by norm_num)
    (Or.inr ⟨row18_endpoint1_sign,row18_endpoint0_sign⟩)

theorem row21_right_positive :
    ∀ i, 0<(row21Right i).lo := by kernel_decide

theorem row21_left_positive :
    ∀ i, 0<(row21Left i).lo := by kernel_decide

theorem row21_dual_positive :
    ∀ p ∈ row21Dual, 0<p.2.lo := by kernel_decide

theorem row21_cosines_mem :
    ∀ i, (![Real.cos (2*Real.pi*3/21),Real.cos (2*Real.pi*4/21),Real.cos (2*Real.pi*5/21)] : Fin 3 → ℝ) i ∈ row21Cosines i := by
  intro i
  fin_cases i
  · have h := CertifiedExamples.Trigonometry.cos_bounds (2*3/21) 32 (3896811261617/6250000000000) (498791841487/800000000000)
      (by kernel_decide)
    have he : (((2*3/21):ℚ):ℝ)*Real.pi = 2*Real.pi*3/21 := by push_cast; ring
    rw [he] at h
    exact h
  · have h := CertifiedExamples.Trigonometry.cos_bounds (2*4/21) 32 (18267051218319/50000000000000) (36534102436641/100000000000000)
      (by kernel_decide)
    have he : (((2*4/21):ℚ):ℝ)*Real.pi = 2*Real.pi*4/21 := by push_cast; ring
    rw [he] at h
    exact h
  · have h := CertifiedExamples.Trigonometry.cos_bounds (2*5/21) 32 (7473009358641/100000000000000) (1868252339661/25000000000000)
      (by kernel_decide)
    have he : (((2*5/21):ℚ):ℝ)*Real.pi = 2*Real.pi*5/21 := by push_cast; ring
    rw [he] at h
    exact h
theorem row21_endpoint0_sign : 0<determinant21 (5340275592191389/50000000000000) := by
  have h := IntervalExpr.strictNegative_sound (IntervalExpr.neg (determinant21Expr (5340275592191389/50000000000000))) row21Cosines
    (by kernel_decide) row21_cosines_mem
  change -(determinant21Expr (5340275592191389/50000000000000)).value ![Real.cos (2*Real.pi*3/21),Real.cos (2*Real.pi*4/21),Real.cos (2*Real.pi*5/21)] < 0 at h
  rw [determinant21Expr_value] at h
  push_cast at h
  exact neg_lt_zero.mp h

theorem row21_endpoint1_sign : determinant21 (5340275602191389/50000000000000)<0 := by
  have h := IntervalExpr.strictNegative_sound (determinant21Expr (5340275602191389/50000000000000)) row21Cosines
    (by kernel_decide) row21_cosines_mem
  rw [determinant21Expr_value] at h
  push_cast at h
  exact h

theorem row21_boundary_root :
    ∃ κ ∈ Set.Icc ((5340275592191389/50000000000000):ℝ) (5340275602191389/50000000000000), determinant21 κ=0 :=
  polynomial_root_from_opposite_signs continuous_determinant21 (by norm_num)
    (Or.inr ⟨row21_endpoint1_sign,row21_endpoint0_sign⟩)

end polyak.Certificates.PartII.Plateaus
