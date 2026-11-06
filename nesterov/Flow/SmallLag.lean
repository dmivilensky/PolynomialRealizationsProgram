import nesterov.Flow.Kernel

/-!
Article: Lemma `lem:spread`, the short-lag regime.
Use: explicit Taylor bounds make the estimates uniform over an entire band
of frequencies before the quadrature size is chosen.
-/
namespace nesterov.Flow
noncomputable section

 theorem cosh_taylor_bound {x : ℝ} (hx : |x|≤1) :
    |Real.cosh x-(1+x^2/2)|≤|x|^4*(5/96) := by
  have h := Complex.cos_bound (x:=(x:ℂ)*Complex.I) (by simpa using hx)
  rw [Complex.cos_mul_I] at h
  have he : Complex.cosh (x:ℂ)-(1-((x:ℂ)*Complex.I)^2/2)=
      ((Real.cosh x-(1+x^2/2):ℝ):ℂ) := by
    rw [Complex.ofReal_sub,Complex.ofReal_add,Complex.ofReal_cosh]
    push_cast
    rw [mul_pow,Complex.I_sq]
    ring
  rw [he,Complex.norm_real,Real.norm_eq_abs] at h
  simpa only [norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs] using h

 theorem sinh_taylor_bound {x : ℝ} (hx : |x|≤1) :
    |Real.sinh x-(x+x^3/6)|≤|x|^5/100 := by
  have h := Complex.sin_bound (x:=(x:ℂ)*Complex.I) (by simpa using hx)
  rw [Complex.sin_mul_I] at h
  have he : Complex.sinh (x:ℂ)*Complex.I-
      ((x:ℂ)*Complex.I-((x:ℂ)*Complex.I)^3/6)=
      ((Real.sinh x-(x+x^3/6):ℝ):ℂ)*Complex.I := by
    rw [Complex.ofReal_sub,Complex.ofReal_add,Complex.ofReal_sinh]
    push_cast
    rw [mul_pow,show Complex.I^3= -Complex.I by simp [pow_succ]]
    ring
  rw [he,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs] at h
  simpa only [norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs] using h

theorem cosh_sub_one_le_sq {x : ℝ} (hx0 : 0≤x) (hx1 : x≤1) : Real.cosh x-1≤x^2 := by
  have h := (abs_le.mp (cosh_taylor_bound (x:=x) (by simpa [abs_of_nonneg hx0] using hx1))).2
  rw [abs_of_nonneg hx0] at h
  have hx2 : x^2≤1 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hx2 (sq_nonneg x)]

theorem sinh_sub_self_le_cube {x : ℝ} (hx0 : 0≤x) (hx1 : x≤1) : Real.sinh x-x≤x^3/5 := by
  have h := (abs_le.mp (sinh_taylor_bound (x:=x) (by simpa [abs_of_nonneg hx0] using hx1))).2
  rw [abs_of_nonneg hx0] at h
  have hx2 : x^2≤1 := by nlinarith
  have hx3 : 0≤x^3 := pow_nonneg hx0 _
  nlinarith [mul_le_mul_of_nonneg_left hx2 hx3]

theorem one_sub_cos_ge_sq {x : ℝ} (hx0 : 0≤x) (hx1 : x≤1) :
    (43/96:ℝ)*x^2≤1-Real.cos x := by
  have h := (abs_le.mp (Real.cos_bound (x:=x) (by simpa [abs_of_nonneg hx0] using hx1))).2
  rw [abs_of_nonneg hx0] at h
  have hx2 : x^2≤1 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hx2 (sq_nonneg x)]

theorem one_sub_cos_le_sq {x : ℝ} (hx0 : 0≤x) (hx1 : x≤1) :
    1-Real.cos x≤x^2 := by
  have h := (abs_le.mp (Real.cos_bound (x:=x) (by simpa [abs_of_nonneg hx0] using hx1))).1
  rw [abs_of_nonneg hx0] at h
  have hx2 : x^2≤1 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hx2 (sq_nonneg x)]


theorem cosh_sub_one_ge_sq {x : ℝ} (hx0 : 0≤x) (hx1 : x≤1) :
    (43/96:ℝ)*x^2≤Real.cosh x-1 := by
  have h := (abs_le.mp (cosh_taylor_bound (x:=x) (by simpa [abs_of_nonneg hx0] using hx1))).1
  rw [abs_of_nonneg hx0] at h
  have hx2 : x^2≤1 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hx2 (sq_nonneg x)]

theorem kernelA_small_bounds {c γ q : ℝ} (hc : 0≤c) (hγ : 0≤γ) (hq : 0≤q)
    (hcq : c*q≤1) (hγq : γ*q≤1) :
    (43/96:ℝ)*(c^2+γ^2)*q^2≤kernelA c γ q ∧
      kernelA c γ q≤(c^2+γ^2)*q^2 := by
  have ha := cosh_sub_one_ge_sq (mul_nonneg hc hq) hcq
  have hb := one_sub_cos_ge_sq (mul_nonneg hγ hq) hγq
  have hc' := cosh_sub_one_le_sq (mul_nonneg hc hq) hcq
  have hd := one_sub_cos_le_sq (mul_nonneg hγ hq) hγq
  dsimp [kernelA]
  constructor <;> nlinarith only [ha,hb,hc',hd]

theorem kernelB_small_upper {c γ q : ℝ} (hc : 0<c) (hγ : 0≤γ) (hq : 0≤q)
    (hcq : c*q≤1) :
    kernelB c γ q≤γ*(c^2+γ^2)*q^3/5 := by
  have hs := sinh_sub_self_le_cube (mul_nonneg hc.le hq) hcq
  have ht := Real.sin_ge_sub_cube (mul_nonneg hγ hq)
  have hm := mul_le_mul_of_nonneg_left hs (div_nonneg hγ hc.le)
  have he : kernelB c γ q=(γ/c)*(Real.sinh (c*q)-c*q)+(γ*q-Real.sin (γ*q)) := by
    dsimp [kernelB]
    field_simp
    ring
  rw [he]
  have he' : γ/c*((c*q)^3/5)=γ*c^2*q^3/5 := by field_simp
  rw [he'] at hm
  nlinarith [mul_nonneg (pow_nonneg hγ 3) (pow_nonneg hq 3)]

theorem forwardKernel_short {θ m c γ γ₀ q : ℝ} (hc : 0<c) (hb : 0≤θ-2*c)
    (hbc : θ-2*c≤c) (hg0 : 0<γ₀) (hcg : 2*c≤γ₀)
    (hγ : γ₀≤γ) (hγ' : γ≤2*γ₀) (hq : 0<q) (hsmall : q≤1/(2*γ₀))
    (hd : 16*delta θ m c≤γ₀^2) :
    (γ₀^2/6)*(kernelA c γ q+kernelB c γ q)≤forwardKernel θ m c γ q := by
  have hgp : 0≤γ := (hg0.trans_le hγ).le
  have hγq : γ*q≤1 := by
    have hh := (le_div_iff₀ (by positivity : 0<2*γ₀)).mp hsmall
    nlinarith [mul_le_mul_of_nonneg_right hγ' hq.le]
  have hcq : c*q≤1 := by nlinarith [mul_le_mul_of_nonneg_right (show c≤γ by linarith) hq.le]
  obtain ⟨hAl,hAu⟩ := kernelA_small_bounds hc.le hgp hq.le hcq hγq
  have hBu := kernelB_small_upper hc hgp hq.le hcq
  have hB0 := kernelB_nonneg hc hgp hq.le
  have hA0 := kernelA_nonneg c γ q
  have hbase : 0≤(c^2+γ^2)*q^2 := by positivity
  have hgg : γ₀^2≤γ^2 := pow_le_pow_left₀ hg0.le hγ 2
  have hcoef : (15/16:ℝ)*γ^2≤γ^2-delta θ m c := by linarith
  have hβq : (θ-2*c)*q/5≤1/20 := by
    have hh := (le_div_iff₀ (by positivity : 0<2*γ₀)).mp hsmall
    nlinarith [mul_le_mul_of_nonneg_right hbc hq.le]
  have hprod : (θ-2*c)*γ*kernelB c γ q≤γ^2*(c^2+γ^2)*q^2/20 := by
    have hh := mul_le_mul_of_nonneg_left hBu (mul_nonneg hb hgp)
    have hi := mul_le_mul_of_nonneg_left hβq (by positivity : 0≤γ^2*(c^2+γ^2)*q^2)
    nlinarith only [hh,hi]
  have hW : γ^2*(c^2+γ^2)*q^2/3≤forwardKernel θ m c γ q := by
    have hh := mul_le_mul_of_nonneg_right hcoef hA0
    have hi := mul_le_mul_of_nonneg_left hAl (by positivity : 0≤(15/16:ℝ)*γ^2)
    dsimp [forwardKernel]
    nlinarith only [hh,hi,hprod,mul_nonneg (sq_nonneg γ) hbase]
  have hAB : kernelA c γ q+kernelB c γ q≤2*((c^2+γ^2)*q^2) := by
    have hh := mul_le_mul_of_nonneg_left hγq (by positivity : 0≤(c^2+γ^2)*q^2)
    nlinarith only [hAu,hBu,hh]
  have hh := mul_le_mul_of_nonneg_left hAB (by positivity : 0≤γ₀^2/6)
  have hi := mul_le_mul_of_nonneg_right hgg hbase
  nlinarith only [hh,hi,hW]

end
end nesterov.Flow
