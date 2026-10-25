import polyak.Global.Symbols.EscapedMass
import polyak.Global.Symbols.OscillatoryMoments

/-! The residual-mass identity S=cos Θ−Σλ cos(nω−Θ), and its actual
Lebesgue integrals against arbitrary L¹ test functions. -/
noncomputable section
namespace polyak.Global.Symbols
open Levels MeasureTheory Filter Set Topology
open scoped BigOperators

def Weights.oscSeries {𝒩 : Set ℤ} (a : Weights 𝒩) (Θ : Curve) (x : ℝ) : ℝ :=
  ∑'n,a.weight n*Real.cos ((n:ℝ)*x-realCurve Θ x)
def Weights.realSymbol {𝒩 : Set ℤ} (a : Weights 𝒩) (Θ : Curve) (x : ℝ) : ℝ :=
  Real.cos (realCurve Θ x)-a.oscSeries Θ x

theorem Weights.osc_term_bound {𝒩 : Set ℤ} (a : Weights 𝒩) (Θ : Curve) (n : ℤ) (x : ℝ) :
    ‖a.weight n*Real.cos ((n:ℝ)*x-realCurve Θ x)‖≤a.weight n := by
  rw [norm_mul,Real.norm_of_nonneg (a.nonneg n)]
  exact mul_le_of_le_one_right (a.nonneg n) (by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one _)

theorem Weights.continuous_oscSeries {𝒩 : Set ℤ} (a : Weights 𝒩) (Θ : Curve) :
    Continuous (a.oscSeries Θ) :=
  continuous_tsum (fun n=>show Continuous (fun x : ℝ=>a.weight n*Real.cos ((n:ℝ)*x-realCurve Θ x)) from
    continuous_const.mul (Real.continuous_cos.comp
    ((continuous_const.mul continuous_id).sub (continuous_realCurve Θ))))
    a.summable (a.osc_term_bound Θ)

theorem Weights.oscSeries_norm_bound {𝒩 : Set ℤ} (a : Weights 𝒩) (Θ : Curve) (x : ℝ) :
    ‖a.oscSeries Θ x‖≤1 := by
  have hn := a.summable.of_nonneg_of_le (fun n=>norm_nonneg _) (fun n=>a.osc_term_bound Θ n x)
  exact ((norm_tsum_le_tsum_norm hn).trans (hn.tsum_le_tsum
    (fun n=>a.osc_term_bound Θ n x) a.summable)).trans a.mass_le_one

theorem Weights.continuous_realSymbol {𝒩 : Set ℤ} (a : Weights 𝒩) (Θ : Curve) :
    Continuous (a.realSymbol Θ) :=
  (Real.continuous_cos.comp (continuous_realCurve Θ)).sub (a.continuous_oscSeries Θ)

theorem Weights.realSymbol_norm_bound {𝒩 : Set ℤ} (a : Weights 𝒩) (Θ : Curve) (x : ℝ) :
    ‖a.realSymbol Θ x‖≤2 := by
  have hh := norm_sub_le (Real.cos (realCurve Θ x)) (a.oscSeries Θ x)
  have hc : ‖Real.cos (realCurve Θ x)‖≤1 := by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one _
  exact hh.trans (by linarith [a.oscSeries_norm_bound Θ x])

theorem Weights.realSymbol_eq_eval {𝒩 : Set ℤ} (a : Weights 𝒩) (Θ : Curve) (ω : Frequency) :
    a.realSymbol Θ (ω:ℝ)=a.eval Θ ω := by
  have hs : Summable (fun n=>a.weight n*Real.cos ((n:ℝ)*(ω:ℝ)-Θ ω)) :=
    a.weighted_summable (fun n=>by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one _)
  have he (n : ℤ) : a.weight n*Θ.lag n ω=
      a.weight n*Θ.minimizer ω-a.weight n*Real.cos ((n:ℝ)*(ω:ℝ)-Θ ω) := by
    unfold Curve.lag Curve.minimizer
    ring
  unfold realSymbol oscSeries eval series gamma
  simp only [realCurve_of_mem Θ ω.property]
  rw [tsum_congr he,(a.summable.mul_right (Θ.minimizer ω)).tsum_sub hs,tsum_mul_right]
  unfold Curve.minimizer
  ring

theorem Weights.integrable_realSymbol_mul {𝒩 : Set ℤ} (a : Weights 𝒩) (Θ : Curve)
    {φ : ℝ→ℝ} (hφ : Integrable φ) : Integrable (fun x=>a.realSymbol Θ x*φ x) :=
  hφ.bdd_mul (a.continuous_realSymbol Θ).aestronglyMeasurable
    (Eventually.of_forall (a.realSymbol_norm_bound Θ))

theorem Weights.integral_realSymbol {𝒩 : Set ℤ} (a : Weights 𝒩) (Θ : Curve)
    {φ : ℝ→ℝ} (hφ : Integrable φ) :
    (∫x,a.realSymbol Θ x*φ x)=oscillatoryMoment Θ φ 0-
      ∑'n,a.weight n*oscillatoryMoment Θ φ n := by
  have hcos (n : ℤ) : Integrable (fun x=>Real.cos ((n:ℝ)*x-realCurve Θ x)*φ x) :=
    hφ.bdd_mul (Real.continuous_cos.comp ((continuous_const.mul continuous_id).sub
      (continuous_realCurve Θ))).aestronglyMeasurable
      (Eventually.of_forall (fun x=>by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one _))
  have hint (n : ℤ) : Integrable (fun x=>a.weight n*(Real.cos ((n:ℝ)*x-realCurve Θ x)*φ x)) :=
    (hcos n).const_mul _
  have hb (n : ℤ) : (∫x,‖a.weight n*(Real.cos ((n:ℝ)*x-realCurve Θ x)*φ x)‖)≤
      a.weight n*(∫x,‖φ x‖) := by
    have hpoint (x : ℝ) : ‖a.weight n*(Real.cos ((n:ℝ)*x-realCurve Θ x)*φ x)‖≤a.weight n*‖φ x‖ := by
      rw [norm_mul,norm_mul,Real.norm_of_nonneg (a.nonneg n)]
      have hh : ‖Real.cos ((n:ℝ)*x-realCurve Θ x)‖≤1 := by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one _
      exact mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_left (norm_nonneg (φ x)) hh) (a.nonneg n)
    simpa only [integral_const_mul] using integral_mono (hint n).norm (hφ.norm.const_mul _) hpoint
  have hsum : Summable (fun n=>∫x,‖a.weight n*(Real.cos ((n:ℝ)*x-realCurve Θ x)*φ x)‖) :=
    (a.summable.mul_right (∫x,‖φ x‖)).of_nonneg_of_le
      (fun _=>integral_nonneg (fun _=>norm_nonneg _)) hb
  have hosc : Integrable (fun x=>a.oscSeries Θ x*φ x) :=
    hφ.bdd_mul (a.continuous_oscSeries Θ).aestronglyMeasurable
      (Eventually.of_forall (a.oscSeries_norm_bound Θ))
  have hmin : Integrable (fun x=>Real.cos (realCurve Θ x)*φ x) := by
    simpa only [Int.cast_zero,zero_mul,zero_sub,Real.cos_neg] using hcos 0
  have he (x : ℝ) : a.oscSeries Θ x*φ x=
      ∑'n,a.weight n*(Real.cos ((n:ℝ)*x-realCurve Θ x)*φ x) := by
    unfold oscSeries
    rw [←tsum_mul_right]
    apply tsum_congr
    intro n
    ring
  unfold realSymbol
  simp_rw [sub_mul]
  rw [integral_sub hmin hosc]
  simp_rw [he]
  rw [←integral_tsum_of_summable_integral_norm hint hsum]
  simp only [integral_const_mul,oscillatoryMoment,Int.cast_zero,zero_mul,zero_sub,Real.cos_neg]

end polyak.Global.Symbols
