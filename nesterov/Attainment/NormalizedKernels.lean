import polyak.Spectral.ComplexLag
import polyak.Spectral.HullAnalytic

/-! Uniform compactification of the normalized cosine and sine lag kernels.
The exponent ranges over an entire compact interval away from zero, while
frequency ranges over a fixed complex neighbourhood of all physical angles. -/
noncomputable section
open Set Filter
open scoped Topology OnePoint
namespace nesterov.Attainment

abbrev LagParameter (lo hi : ℝ) := Set.Icc lo hi
abbrev LagWindow := polyak.Spectral.lagWindow
abbrev LagDomain (lo hi : ℝ) := LagParameter lo hi × LagWindow lo

def radial (s : ℝ) (n : ℕ) : ℝ := polyak.Spectral.lagRadial s n

def cosineKernel (s : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  (1+(radial s n : ℂ)^2-2*(radial s n : ℂ)*Complex.cos ((n+1 : ℕ)*z)) /
    (1-(radial s n : ℂ)^2)

def sineKernel (s : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  (2*(radial s n : ℂ)*Complex.sin ((n+1 : ℕ)*z)) / (1-(radial s n : ℂ)^2)

theorem radial_bound {lo s : ℝ} (hlo : 0 < lo) (hs : lo ≤ s) (n : ℕ) :
    0 < radial s n ∧ radial s n ≤ Real.exp (-lo) ∧ Real.exp (-lo) < 1 := by
  have hs' : 0 < s := hlo.trans_le hs
  refine ⟨Real.exp_pos _, ?_, Real.exp_lt_one_iff.mpr (by linarith)⟩
  exact (polyak.Spectral.lagRadial_bounds hs' n).2.1.trans (Real.exp_le_exp.mpr (by linarith))

/-- One geometric majorant works for every exponent in the parameter interval. -/
theorem normalized_kernel_bounds {lo s : ℝ} (hlo : 0 < lo) (hs : lo ≤ s)
    (n : ℕ) {z : ℂ} (hz : |z.im| ≤ lo/2) :
    ‖cosineKernel s n z-1‖ ≤
      (4/(1-Real.exp (-lo)^2))*Real.exp (-lo/2)^(n+1) ∧
    ‖sineKernel s n z‖ ≤
      (2/(1-Real.exp (-lo)^2))*Real.exp (-lo/2)^(n+1) := by
  let r := radial s n
  let b := Real.exp (-lo)
  let N : ℝ := (n+1 : ℕ)
  let E := Real.exp (N*(lo/2))
  obtain ⟨hr, hrb, hb⟩ := radial_bound hlo hs n
  have hr' : 0 < r := hr
  have hD : 0 < 1-b^2 := by dsimp [b]; nlinarith [Real.exp_pos (-lo)]
  have hdr : 0 < 1-r^2 := by dsimp [r]; nlinarith
  have hden : 1-b^2 ≤ 1-r^2 := by dsimp [b,r] at *; nlinarith
  have hN : 0 ≤ N := by positivity
  have hE : 1 ≤ E := Real.one_le_exp_iff.mpr (mul_nonneg hN (half_pos hlo).le)
  have hr1 : r ≤ 1 := hrb.trans hb.le
  have hrE : r^2 ≤ r*E := by dsimp [r] at *; nlinarith
  have hc : ‖Complex.cos ((n+1 : ℕ)*z)‖ ≤ E := by
    apply (polyak.Spectral.norm_complex_cos_le_exp _).trans
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul,
      add_zero, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ ((n+1 : ℕ) : ℝ) by positivity)]
    exact mul_le_mul_of_nonneg_left hz hN
  have hsin : ‖Complex.sin ((n+1 : ℕ)*z)‖ ≤ E := by
    apply (polyak.Spectral.norm_complex_sin_le_exp _).trans
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul,
      add_zero, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ ((n+1 : ℕ) : ℝ) by positivity)]
    exact mul_le_mul_of_nonneg_left hz hN
  have hnormden : ‖(1 : ℂ)-(r : ℂ)^2‖ = 1-r^2 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hdr]
  have hpow : r*E ≤ Real.exp (-lo/2)^(n+1) := by
    rw [← Real.exp_nat_mul]
    dsimp [r,E,N,radial,polyak.Spectral.lagRadial]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hs hN]
  have hnumA : ‖(2 : ℂ)*(r : ℂ)^2-2*(r : ℂ)*Complex.cos ((n+1 : ℕ)*z)‖ ≤ 4*(r*E) := by
    calc
      _ ≤ ‖(2 : ℂ)*(r : ℂ)^2‖ + ‖2*(r : ℂ)*Complex.cos ((n+1 : ℕ)*z)‖ := norm_sub_le _ _
      _ = 2*r^2+2*r*‖Complex.cos ((n+1 : ℕ)*z)‖ := by
        simp only [norm_mul,norm_pow,Complex.norm_ofNat,Complex.norm_real,
          Real.norm_eq_abs,abs_of_pos hr']
      _ ≤ 2*r^2+2*r*E := by gcongr
      _ ≤ _ := by nlinarith
  have hnumB : ‖(2 : ℂ)*(r : ℂ)*Complex.sin ((n+1 : ℕ)*z)‖ ≤ 2*(r*E) := by
    simp only [norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr']
    calc
      _ ≤ 2*r*E := by gcongr
      _ = _ := by ring
  have he : cosineKernel s n z-1 =
      ((2 : ℂ)*(r : ℂ)^2-2*(r : ℂ)*Complex.cos ((n+1 : ℕ)*z))/(1-(r : ℂ)^2) := by
    have hd : (1 : ℂ)-(r : ℂ)^2 ≠ 0 := by exact_mod_cast ne_of_gt hdr
    dsimp [cosineKernel,r]
    dsimp [r] at hd
    field_simp [hd]
    ring
  constructor
  · rw [he,norm_div,hnormden]
    calc
      _ ≤ 4*(r*E)/(1-r^2) := div_le_div_of_nonneg_right hnumA hdr.le
      _ ≤ 4*(r*E)/(1-b^2) := div_le_div_of_nonneg_left (by positivity) hD hden
      _ ≤ _ := by
        rw [div_mul_eq_mul_div]
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow (by norm_num : (0:ℝ)≤4)) hD.le
  · change ‖((2 : ℂ)*(r : ℂ)*Complex.sin ((n+1 : ℕ)*z))/(1-(r : ℂ)^2)‖ ≤ _
    rw [norm_div,hnormden]
    calc
      _ ≤ 2*(r*E)/(1-r^2) := div_le_div_of_nonneg_right hnumB hdr.le
      _ ≤ 2*(r*E)/(1-b^2) := div_le_div_of_nonneg_left (by positivity) hD hden
      _ ≤ _ := by
        rw [div_mul_eq_mul_div]
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow (by norm_num : (0:ℝ)≤2)) hD.le

def cosineKernelMap (lo hi : ℝ) (hlo : 0 < lo) (n : ℕ) : C(LagDomain lo hi,ℂ) where
  toFun q := cosineKernel q.1 n q.2
  continuous_toFun := by
    have hden (q : LagDomain lo hi) : (1 : ℂ)-(radial q.1 n : ℂ)^2 ≠ 0 := by
      exact_mod_cast ne_of_gt (polyak.Spectral.lagRadial_denominator_pos (hlo.trans_le q.1.property.1) n)
    unfold cosineKernel radial polyak.Spectral.lagRadial at *
    fun_prop

def sineKernelMap (lo hi : ℝ) (hlo : 0 < lo) (n : ℕ) : C(LagDomain lo hi,ℂ) where
  toFun q := sineKernel q.1 n q.2
  continuous_toFun := by
    have hden (q : LagDomain lo hi) : (1 : ℂ)-(radial q.1 n : ℂ)^2 ≠ 0 := by
      exact_mod_cast ne_of_gt (polyak.Spectral.lagRadial_denominator_pos (hlo.trans_le q.1.property.1) n)
    unfold sineKernel radial polyak.Spectral.lagRadial at *
    fun_prop

theorem tendsto_kernelMaps (lo hi : ℝ) (hlo : 0 < lo) :
    Tendsto (fun n => (cosineKernelMap lo hi hlo n, sineKernelMap lo hi hlo n))
      atTop (𝓝 ((1,0) : C(LagDomain lo hi,ℂ) × C(LagDomain lo hi,ℂ))) := by
  have hD : 0 < 1-Real.exp (-lo)^2 := by
    have he := Real.exp_lt_one_iff.mpr (neg_neg_iff_pos.mpr hlo)
    nlinarith [Real.exp_pos (-lo)]
  have hθ0 : 0 ≤ Real.exp (-lo/2) := (Real.exp_pos _).le
  have hθ1 : Real.exp (-lo/2) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hp : Tendsto (fun n : ℕ => Real.exp (-lo/2)^(n+1)) atTop (𝓝 0) := by
    simpa only [pow_succ,zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1).mul_const (Real.exp (-lo/2))
  have hA : Tendsto (cosineKernelMap lo hi hlo) atTop (𝓝 1) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) (by simpa only [mul_zero] using hp.const_mul (4/(1-Real.exp (-lo)^2)))
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro q
    exact (normalized_kernel_bounds hlo q.1.property.1 n q.2.property.2).1
  have hB : Tendsto (sineKernelMap lo hi hlo) atTop (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) (by simpa only [mul_zero] using hp.const_mul (2/(1-Real.exp (-lo)^2)))
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro q
    exact (normalized_kernel_bounds hlo q.1.property.1 n q.2.property.2).2
  exact hA.prodMk_nhds hB

def compactifiedKernels (lo hi : ℝ) (hlo : 0 < lo) :
    C(OnePoint ℕ, C(LagDomain lo hi,ℂ) × C(LagDomain lo hi,ℂ)) :=
  OnePoint.continuousMapMkNat (fun n => (cosineKernelMap lo hi hlo n,sineKernelMap lo hi hlo n))
    (1,0) (tendsto_kernelMaps lo hi hlo)

/-- The rational exponential kernels are exactly the sinh-normalized lags. -/
theorem kernels_eq_hyperbolic {s : ℝ} (hs : 0 < s) (n : ℕ) (z : ℂ) :
    cosineKernel s n z =
      ((Real.cosh ((n+1 : ℕ)*s) : ℂ)-Complex.cos ((n+1 : ℕ)*z)) /
        (Real.sinh ((n+1 : ℕ)*s) : ℂ) ∧
    sineKernel s n z = Complex.sin ((n+1 : ℕ)*z) /
        (Real.sinh ((n+1 : ℕ)*s) : ℂ) := by
  have hp := polyak.Spectral.lagRadial_hyperbolic s n
  have hr : radial s n ≠ 0 := ne_of_gt (Real.exp_pos _)
  have hd : (1 : ℂ)-(radial s n : ℂ)^2 ≠ 0 := by
    exact_mod_cast ne_of_gt (polyak.Spectral.lagRadial_denominator_pos hs n)
  have hsh : (Real.sinh ((n+1 : ℕ)*s) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sinh_pos_iff.mpr
      (mul_pos (Nat.cast_pos.mpr (Nat.succ_pos _)) hs)))
  have hc' : 2*(radial s n : ℂ)*(Real.cosh ((n+1 : ℕ)*s) : ℂ) = 1+(radial s n : ℂ)^2 := by
    exact_mod_cast hp.1
  have hs' : 2*(radial s n : ℂ)*(Real.sinh ((n+1 : ℕ)*s) : ℂ) = 1-(radial s n : ℂ)^2 := by
    exact_mod_cast hp.2
  constructor
  · unfold cosineKernel
    apply (div_eq_div_iff hd hsh).mpr
    linear_combination -(Real.sinh ((n+1 : ℕ)*s) : ℂ)*hc' +
      ((Real.cosh ((n+1 : ℕ)*s) : ℂ)-Complex.cos ((n+1 : ℕ)*z))*hs'
  · unfold sineKernel
    apply (div_eq_div_iff hd hsh).mpr
    linear_combination Complex.sin ((n+1 : ℕ)*z)*hs'

end nesterov.Attainment
