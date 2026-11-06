import chebyshev1.SineJacobi.LogSinc
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Smooth removal of the cotangent pole at the hard endpoint. -/
namespace chebyshev1
noncomputable section
open Real Set MeasureTheory Filter
open scoped ContDiff Topology

namespace Analysis

def sinc₃ (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..1, t ^ 3 * sin (x * t)

theorem sinc₂_deriv (x : ℝ) : HasDerivAt sinc₂ (sinc₃ x) x := by
  apply hasDerivAt_integral_rectangle
    (fun u t => -t ^ 2 * cos (u * t)) (fun u t => t ^ 3 * sin (u * t))
    (lo := x - 1) (hi := x + 1) (by constructor <;> linarith) (by norm_num)
  · intro u _; fun_prop
  · fun_prop
  · intro u _ t _
    convert (((hasDerivAt_id u).mul_const t).cos.const_mul (-t ^ 2)) using 1 <;> simp
    ring

theorem sinc₃_continuous : Continuous sinc₃ := by
  have hc : Continuous (fun p : ℝ × ℝ => p.2 ^ 3 * sin (p.1 * p.2)) := by fun_prop
  have hi := continuous_parametric_integral_of_continuous (μ := volume)
    (f := fun x t : ℝ => t ^ 3 * sin (x * t)) hc
    (isCompact_Icc (a := (0 : ℝ)) (b := 1))
  convert hi using 1
  funext x
  rw [sinc₃, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Icc_eq_integral_Ioc]

theorem sinc_contDiff_three : ContDiff ℝ 3 sinc := by
  have hd1 : deriv sinc = sinc₁ := funext fun x => (sinc_deriv x).deriv
  have hd2 : deriv sinc₁ = sinc₂ := funext fun x => (sinc₁_deriv x).deriv
  have hd3 : deriv sinc₂ = sinc₃ := funext fun x => (sinc₂_deriv x).deriv
  have h2 : ContDiff ℝ 1 sinc₂ := by
    rw [contDiff_one_iff_deriv, hd3]
    exact ⟨fun x => (sinc₂_deriv x).differentiableAt, sinc₃_continuous⟩
  have h1 : ContDiff ℝ 2 sinc₁ := by
    rw [show (2 : ℕ∞ω) = 1 + 1 by rfl, contDiff_succ_iff_deriv, hd2]
    exact ⟨fun x => (sinc₁_deriv x).differentiableAt, by simp, h2⟩
  rw [show (3 : ℕ∞ω) = 2 + 1 by rfl, contDiff_succ_iff_deriv, hd1]
  exact ⟨fun x => (sinc_deriv x).differentiableAt, by simp, h1⟩

end Analysis

namespace SineJacobi

def cotangentPotential (x : ℝ) : ℝ := log (sinc (π * x / 2))

/-- The pole-subtracted cotangent, defined smoothly also at zero. -/
def regularCotangent (x : ℝ) : ℝ := (2 / π) * deriv cotangentPotential x

theorem cotangentPotential_contDiff :
    ContDiffOn ℝ 3 cotangentPotential (Ioo (-2 : ℝ) 2) := by
  apply ((Analysis.sinc_contDiff_three.comp
    (show ContDiff ℝ 3 (fun x : ℝ => π * x / 2) by fun_prop)).contDiffOn).log
  intro x hx
  change sinc (π * x / 2) ≠ 0
  have hp : π * x / 2 = π * (x / 2) := by ring
  rw [hp]
  exact (sinc_pi_pos (show x / 2 ∈ Ioo (-1 : ℝ) 1 by
    constructor <;> linarith [hx.1, hx.2])).ne'

theorem regularCotangent_contDiff :
    ContDiffOn ℝ 2 regularCotangent (Ioo (-2 : ℝ) 2) := by
  have hd : ContDiffOn ℝ 2 (deriv cotangentPotential) (Ioo (-2 : ℝ) 2) :=
    cotangentPotential_contDiff.deriv_of_isOpen isOpen_Ioo (by norm_num)
  exact contDiffOn_const.mul hd

theorem regularCotangent_second_bound :
    ∃ M, 0 ≤ M ∧ ∀ x ∈ Icc (0 : ℝ) 1,
      |deriv (deriv regularCotangent) x| ≤ M := by
  have h1 : ContDiffOn ℝ 1 (deriv regularCotangent) (Ioo (-2 : ℝ) 2) :=
    regularCotangent_contDiff.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have h2 := (h1.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)).mono
    (show Icc (0 : ℝ) 1 ⊆ Ioo (-2 : ℝ) 2 from fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).bddAbove_image h2.norm
  refine ⟨max M 0, le_max_right _ _, fun x hx => ?_⟩
  have hh := hM (mem_image_of_mem (fun x : ℝ => ‖deriv (deriv regularCotangent) x‖) hx)
  simpa only [Real.norm_eq_abs] using hh.trans (le_max_left _ _)

theorem regularCotangent_eq (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 2) :
    regularCotangent x = cot (π * x / 2) - 2 / (π * x) := by
  have hy : 0 < π * x / 2 := div_pos (mul_pos pi_pos hx.1) (by norm_num)
  have hyπ : π * x / 2 < π := by nlinarith [pi_pos, hx.2]
  have hs : sin (π * x / 2) ≠ 0 := (sin_pos_of_pos_of_lt_pi hy hyπ).ne'
  have harg : HasDerivAt (fun t : ℝ => π * t / 2) (π / 2) x := by
    convert ((hasDerivAt_id x).const_mul π).div_const 2 using 1 <;> simp
  have hder := (harg.sin.log hs).sub (harg.log hy.ne')
  have heq : cotangentPotential =ᶠ[𝓝 x]
      (fun t : ℝ => log (sin (π * t / 2)) - log (π * t / 2)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
    have ht0 : 0 < π * t / 2 := div_pos (mul_pos pi_pos ht.1) (by norm_num)
    have htπ : π * t / 2 < π := by nlinarith [pi_pos, ht.2]
    rw [cotangentPotential, sinc_of_ne_zero ht0.ne',
      log_div (sin_pos_of_pos_of_lt_pi ht0 htπ).ne' ht0.ne']
  have hd := (hder.congr_of_eventuallyEq heq).deriv
  rw [regularCotangent, hd, cot_eq_cos_div_sin]
  field_simp [pi_ne_zero, hx.1.ne', hs]

theorem regularCotangent_integral :
    (∫ x in (0 : ℝ)..1, regularCotangent x) = (2 / π) * log (2 / π) := by
  have hd (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      HasDerivAt cotangentPotential (deriv cotangentPotential x) x := by
    have hx' : x ∈ Ioo (-2 : ℝ) 2 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    exact ((cotangentPotential_contDiff.contDiffAt (isOpen_Ioo.mem_nhds hx')).differentiableAt
      (by norm_num)).hasDerivAt
  have hc : ContinuousOn (deriv cotangentPotential) (Icc (0 : ℝ) 1) :=
    (cotangentPotential_contDiff.deriv_of_isOpen isOpen_Ioo
      (show (0 : ℕ∞ω) + 1 ≤ 3 by norm_num)).continuousOn.mono
        (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hd x (by simpa using hx)) (hc.intervalIntegrable_of_Icc (by norm_num))
  change (∫ x in (0 : ℝ)..1, (2 / π) * deriv cotangentPotential x) = _
  rw [intervalIntegral.integral_const_mul, hi]
  have hs : sinc (π / 2) = 2 / π := by
    rw [sinc_of_ne_zero (div_ne_zero pi_ne_zero (by norm_num : (2 : ℝ) ≠ 0)),
      sin_pi_div_two]
    ring
  simp [cotangentPotential, hs]

end SineJacobi
end
end chebyshev1
