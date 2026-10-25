import polyak.Waves.Polyak

/-!
Article: Appendix B, Lemma tailsharp.
Use: a single exact amplitude bound certifies every lag past a finite cutoff.
Proof: the planar Pythagorean identity, a real two-dimensional Cauchy inequality,
probability integration, and |sinh x|≤cosh x.
-/

noncomputable section
open MeasureTheory

namespace polyak.Boundary
open Spectral

/-- Article: the sharp oscillatory amplitude identity at every frequency. -/
theorem amplitude_identity (u : ℝ) (c : Frequency) :
    g u c ^ 2 + (2*u*Real.sin (Real.arccos c))^2 = (1-(c : ℝ)^2+u^2)^2 := by
  have hs := Real.sin_sq_add_cos_sq (Real.arccos (c : ℝ))
  rw [Real.cos_arccos c.property.1 c.property.2] at hs
  unfold g
  nlinarith [hs]

/-- Article: the sine-polynomial term is division-free even at c=±1. -/
theorem lagB_trig (u : ℝ) (n : ℕ) (hn : 1 ≤ n) (c : Frequency) :
    lagB u n c = 2*u*Real.sin (Real.arccos c)*Real.sin (n*Real.arccos c) := by
  have h := Waves.polyak_skew (Real.arsinh u) n hn c
  simpa only [Real.sinh_arsinh, Waves.polyakMultiplier_im, mul_assoc] using h.symm

/-- Article: sharp pointwise amplitude estimate for both lag signs. -/
theorem lag_oscillation_bound (u : ℝ) (n : ℕ) (hn : 1 ≤ n) (c : Frequency) (δ : ℝ)
    (hδ : δ = 1 ∨ δ = -1) :
    |g u c * chebT n c + δ * lagB u n c| ≤ 1-(c : ℝ)^2+u^2 := by
  have hc : 0 ≤ 1-(c : ℝ)^2 := by
    have h := (sq_le_one_iff_abs_le_one (c : ℝ)).mpr (abs_le.mpr c.property)
    linarith
  have hamp := amplitude_identity u c
  have htrig := Real.sin_sq_add_cos_sq (n*Real.arccos (c : ℝ))
  rw [Waves.chebT_arccos, lagB_trig u n hn c]
  have hb : δ^2 = 1 := by rcases hδ with rfl | rfl <;> norm_num
  let A := g u c
  let B := δ*(2*u*Real.sin (Real.arccos (c : ℝ)))
  let x := Real.cos (n*Real.arccos (c : ℝ))
  let y := Real.sin (n*Real.arccos (c : ℝ))
  have hB : A^2+B^2 = (1-(c : ℝ)^2+u^2)^2 := by
    dsimp [A,B]
    rw [mul_pow, hb, one_mul]
    exact hamp
  have hxy : x^2+y^2=1 := by dsimp [x,y]; linarith
  have hid : (A*x+B*y)^2+(A*y-B*x)^2=(A^2+B^2)*(x^2+y^2) := by ring
  have hsq : (A*x+B*y)^2 ≤ (1-(c : ℝ)^2+u^2)^2 := by
    rw [hB,hxy,mul_one] at hid
    nlinarith [sq_nonneg (A*y-B*x)]
  have h := (sq_le_sq₀ (abs_nonneg (A*x+B*y)) (by positivity : 0 ≤ 1-(c : ℝ)^2+u^2)).mp
    (by simpa only [sq_abs] using hsq)
  simpa only [A,B,x,y,mul_assoc] using h

/-- Article: pointwise raw-lag lower bound, with both interpolation signs. -/
theorem pointwise_lag_tail (u t : ℝ) (n : ℕ) (hn : 1 ≤ n) (c : Frequency) (δ : ℝ)
    (hδ : δ=1 ∨ δ= -1) :
    g u c * Real.cosh (n*t) - (g u c + 2*u^2) ≤ lagA u t n c - δ*lagB u n c := by
  have h := (le_abs_self (g u c*chebT n c+δ*lagB u n c)).trans
    (lag_oscillation_bound u n hn c δ hδ)
  unfold lagA lagD g at *
  nlinarith

/-- Article: averaged amplitude tail before the value-constant correction. -/
theorem mean_lag_tail (ν : Spectrum) (u t : ℝ) (n : ℕ) (hn : 1 ≤ n) (δ : ℝ)
    (hδ : δ=1 ∨ δ= -1) :
    meanG ν u*Real.cosh (n*t) - (meanG ν u+2*u^2) ≤
      meanA ν u t n - δ*meanB ν u n := by
  have hg := integrable_continuous ν (show Continuous (fun c : Frequency => g u c) by unfold g; fun_prop)
  have ha := integrable_continuous ν (show Continuous (fun c : Frequency => lagA u t n c) by
    unfold lagA lagD g chebT; fun_prop)
  have hb := integrable_continuous ν (show Continuous (fun c : Frequency => lagB u n c) by
    unfold lagB chebU; fun_prop)
  have hga : Integrable (fun c : Frequency => g u c*Real.cosh (n*t)) (ν : Measure Frequency) :=
    hg.mul_const _
  have hgc : Integrable (fun c : Frequency => g u c+2*u^2) (ν : Measure Frequency) :=
    integrable_continuous ν (by unfold g; fun_prop)
  have hl : Integrable (fun c : Frequency => g u c*Real.cosh (n*t)-(g u c+2*u^2))
      (ν : Measure Frequency) := by
    exact integrable_continuous ν (by unfold g; fun_prop)
  have hr : Integrable (fun c : Frequency => lagA u t n c-δ*lagB u n c)
      (ν : Measure Frequency) := by
    exact integrable_continuous ν (by unfold lagA lagD lagB g chebT chebU; fun_prop)
  have h := integral_mono hl hr (fun c => pointwise_lag_tail u t n hn c δ hδ)
  rw [integral_sub hga hgc, integral_mul_const, integral_add hg (integrable_const _),
    integral_sub ha (hb.const_mul _), integral_const_mul] at h
  simp only [meanG_eq_integral, meanA_eq_integral, meanB_eq_integral, avg]
  simp_rw [integral_const_mul] at h
  simpa using h

/-- Article: the hyperbolic skew factor is bounded by the symmetric radial factor. -/
theorem abs_sinh_le_cosh (x : ℝ) : |Real.sinh x| ≤ Real.cosh x := by
  apply abs_le.mpr
  constructor
  · have h := Real.sinh_lt_cosh (-x)
    rw [Real.sinh_neg, Real.cosh_neg] at h
    linarith
  · exact (Real.sinh_lt_cosh x).le

/-- Article: tailsharp, both raw lag signs including the common value correction. -/
theorem raw_lag_tail (ν : Spectrum) (u C t : ℝ) (n : ℕ) (hn : 1 ≤ n) (δ : ℝ)
    (hδ : δ=1 ∨ δ= -1) :
    (meanG ν u-|C|)*Real.cosh (n*t) - (meanG ν u+2*u^2) ≤
      meanA ν u t n - δ*meanB ν u n + δ*C*Real.sinh (n*t) := by
  have h := mean_lag_tail ν u t n hn δ hδ
  have hab : |C*Real.sinh (n*t)| ≤ |C| *Real.cosh (n*t) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_sinh_le_cosh _) (abs_nonneg _)
  have hval : -(|C| *Real.cosh (n*t)) ≤ δ*C*Real.sinh (n*t) := by
    have hh := abs_le.mp hab
    rcases hδ with rfl | rfl <;> nlinarith [hh.1,hh.2]
  nlinarith

/-- Article: the sharp simultaneous lower and upper raw-lag tail estimate. -/
theorem raw_lag_tail_both (ν : Spectrum) (u C t : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    (meanG ν u-|C|)*Real.cosh (n*t) - (meanG ν u+2*u^2) ≤
      meanA ν u t n - meanB ν u n + C*Real.sinh (n*t) ∧
    (meanG ν u-|C|)*Real.cosh (n*t) - (meanG ν u+2*u^2) ≤
      meanA ν u t n + meanB ν u n - C*Real.sinh (n*t) := by
  constructor
  · simpa only [one_mul] using raw_lag_tail ν u C t n hn 1 (Or.inl rfl)
  · simpa only [neg_one_mul, sub_neg_eq_add, neg_mul, one_mul, sub_eq_add_neg, neg_neg] using
      raw_lag_tail ν u C t n hn (-1) (Or.inr rfl)

/-- Article: finite-prefix certification plus one analytic tail proves all infinite constraints.
Use: a finite certificate never silently drops any unverified lag. -/
theorem feasibleU_of_prefix_tail (ν : Spectrum) (u C t : ℝ) (N : ℕ)
    (hstar : |C| ≤ meanG ν u)
    (hprefix : ∀ n : ℕ, 1 ≤ n → n ≤ N →
      0 ≤ meanA ν u t n - meanB ν u n + C*Real.sinh (n*t) ∧
      0 ≤ meanA ν u t n + meanB ν u n - C*Real.sinh (n*t))
    (htail : ∀ n : ℕ, N < n →
      meanG ν u+2*u^2 ≤ (meanG ν u-|C|)*Real.cosh (n*t)) :
    FeasibleU u t ν C := by
  refine ⟨hstar,fun n hn => ?_⟩
  by_cases hN : n ≤ N
  · exact hprefix n hn hN
  · have h := raw_lag_tail_both ν u C t n hn
    have ht := htail n (by omega)
    exact ⟨by linarith [h.1],by linarith [h.2]⟩

/-- Article: cosh(nt) grows without bound whenever t≠0.
Use: one explicit tail estimate handles both positive and negative exponents. -/
theorem tendsto_cosh_nat_mul {t : ℝ} (ht : t ≠ 0) :
    Filter.Tendsto (fun n : ℕ => Real.cosh (n*t)) Filter.atTop Filter.atTop := by
  have harg := Filter.Tendsto.atTop_mul_const (abs_pos.mpr ht)
    (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop)
  have hexp := Real.tendsto_exp_atTop.comp harg
  have hhalf := Filter.Tendsto.atTop_mul_const (by norm_num : (0 : ℝ) < 1/2) hexp
  apply Filter.tendsto_atTop_mono (fun n => ?_) hhalf
  have hc : Real.cosh ((n : ℝ)*|t|)=Real.cosh (n*t) := by
    rcases le_total 0 t with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h,mul_neg,Real.cosh_neg]
  rw [Function.comp_apply] at *
  rw [← hc,Real.cosh_eq]
  have hp := (Real.exp_pos (-((n : ℝ)*|t|))).le
  nlinarith

/-- Article: strict minimizer slack makes every sufficiently large lag strictly inactive.
Use: the finite-prefix classifier retains only finitely many possible active constraints. -/
theorem eventually_raw_lags_positive (ν : Spectrum) (u C t : ℝ)
    (hstar : |C| < meanG ν u) (ht : t ≠ 0) :
    ∀ᶠ n : ℕ in Filter.atTop,
      0 < meanA ν u t n-meanB ν u n+C*Real.sinh (n*t) ∧
      0 < meanA ν u t n+meanB ν u n-C*Real.sinh (n*t) := by
  have hgap : 0 < meanG ν u-|C| := sub_pos.mpr hstar
  have hlarge := (tendsto_cosh_nat_mul ht).eventually
    (Filter.eventually_gt_atTop ((meanG ν u+2*u^2)/(meanG ν u-|C|)))
  filter_upwards [hlarge,Filter.eventually_ge_atTop 1] with n hn hn1
  have htail : 0 < (meanG ν u-|C|)*Real.cosh (n*t)-(meanG ν u+2*u^2) := by
    have h := (div_lt_iff₀ hgap).mp hn
    nlinarith
  have h := raw_lag_tail_both ν u C t n hn1
  exact ⟨htail.trans_le h.1,htail.trans_le h.2⟩

end polyak.Boundary
