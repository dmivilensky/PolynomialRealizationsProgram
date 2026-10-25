import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-! Analytic bounds for the sine ratio at junctions. All denominators and
constants are exact. The estimate holds on a real interval, not a finite grid. -/
noncomputable section
namespace polyak.GapEdges.Junction
open Set Real

 theorem sine_ratio_lower {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y)
    (hy : 0 < y) (hyπ : y < Real.pi) :
    x/y ≤ Real.sin x / Real.sin y := by
  have hs : 0 < Real.sin y := Real.sin_pos_of_pos_of_lt_pi hy hyπ
  have ht : x/y ≤ 1 := (div_le_one hy).mpr hxy
  have h := strictConcaveOn_sin_Icc.concaveOn.2
    (show (0:ℝ)∈Icc 0 Real.pi by simp [Real.pi_pos.le])
    (show y∈Icc 0 Real.pi from ⟨hy.le,hyπ.le⟩)
    (sub_nonneg.mpr ht) (div_nonneg hx hy.le) (by ring : 1-x/y+x/y=1)
  simp only [smul_eq_mul, Real.sin_zero, mul_zero, zero_add] at h
  have he : x/y*y=x := div_mul_cancel₀ x hy.ne'
  rw [he] at h
  exact (le_div_iff₀ hs).mpr h

 theorem sine_difference_lower {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y)
    (hyπ : y ≤ Real.pi) :
    Real.cos y*(y-x) ≤ Real.sin y-Real.sin x := by
  exact (convex_Icc x y).mul_sub_le_image_sub_of_le_deriv
    Real.continuous_sin.continuousOn Real.differentiable_sin.differentiableOn
    (fun z hz => by
      rw [Real.deriv_sin]
      have hz' : z ∈ Icc x y := interior_subset hz
      exact Real.cos_le_cos_of_nonneg_of_le_pi (hx.trans hz'.1) hyπ hz'.2)
    x ⟨le_rfl,hxy⟩ y ⟨hxy,le_rfl⟩ hxy

/-- A two-sided estimate using concavity of sine and its derivative at the
right endpoint. It is sharp enough for every integer m≥6 below. -/
theorem sine_ratio_square_bounds {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y)
    (hy : 0 < y) (hyhalf : y < Real.pi/2) :
    (1-(x/y)^2)*Real.cos y ≤ 1-(Real.sin x/Real.sin y)^2 ∧
      1-(Real.sin x/Real.sin y)^2 ≤ 1-(x/y)^2 := by
  have hyπ : y < Real.pi := by linarith [Real.pi_pos]
  have hs : 0 < Real.sin y := Real.sin_pos_of_pos_of_lt_pi hy hyπ
  have hc : 0 < Real.cos y := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],hyhalf⟩
  have hr := sine_ratio_lower hx hxy hy hyπ
  have hsn : 0 ≤ Real.sin x := Real.sin_nonneg_of_nonneg_of_le_pi hx (hxy.trans hyπ.le)
  have hratio : 0 ≤ Real.sin x/Real.sin y := div_nonneg hsn hs.le
  have hinc : Real.sin x ≤ Real.sin y := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.pi_pos]) hyhalf.le hxy
  have hr1 : Real.sin x/Real.sin y ≤ 1 := (div_le_one hs).mpr hinc
  have hxy1 : x/y ≤ 1 := (div_le_one hy).mpr hxy
  have hxyr : 0 ≤ x/y := div_nonneg hx hy.le
  have hd := sine_difference_lower hx hxy hyπ.le
  have hd' : (1-x/y)*Real.cos y ≤ 1-Real.sin x/Real.sin y := by
    have hsy := Real.sin_le hy.le
    have hprod := mul_le_mul_of_nonneg_left hsy
      (mul_nonneg (sub_nonneg.mpr hxy1) hc.le)
    have he : ((1-x/y)*Real.cos y)*y = Real.cos y*(y-x) := by
      field_simp
    rw [he] at hprod
    have hh : (1-x/y)*Real.cos y*Real.sin y ≤ Real.sin y-Real.sin x := hprod.trans hd
    rw [show 1-Real.sin x/Real.sin y = (Real.sin y-Real.sin x)/Real.sin y by field_simp]
    exact (le_div_iff₀ hs).mpr hh
  constructor
  · have hh := mul_le_mul hd' (show 1+x/y ≤ 1+Real.sin x/Real.sin y from by linarith)
      (by positivity : 0 ≤ 1+x/y) (sub_nonneg.mpr hr1)
    nlinarith
  · nlinarith

end polyak.GapEdges.Junction
