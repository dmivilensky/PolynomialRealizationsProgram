import krylov.Functions.AnchoredTrapezoid

/-!
Article: main_krylov, thm:ss1F, continuous-third-derivative branch.
Use: replace Lipschitz third-variation bounds by an actual uniform
oscillation modulus without ever dividing by the segment length.
Source: the proved exact trapezoid Peano kernel and the scalar FTC.
-/
namespace krylov.Functions
noncomputable section
open Set MeasureTheory

/-- A uniform derivative oscillation gives the first-order unit-segment
Taylor remainder, with no Lipschitz or fourth-derivative assumption.
Article: main_krylov, thm:ss1F, continuous D3 branch. -/
theorem scalar_unit_taylor_modulus (g g₁ : ℝ → ℝ)
    (hd : ∀ t ∈ Icc (0 : ℝ) 1,HasDerivAt g (g₁ t) t)
    (hc : ContinuousOn g₁ (Icc 0 1)) (C : ℝ)
    (hb : ∀ t ∈ Icc (0 : ℝ) 1,|g₁ t-g₁ 0|≤C) :
    |g 1-g 0-g₁ 0|≤C := by
  have hi : IntervalIntegrable (fun t : ℝ=>g₁ t-g₁ 0) volume 0 1 :=
    (hc.sub continuousOn_const).intervalIntegrable_of_Icc (by norm_num : (0:ℝ)≤1)
  have hd' t (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun t : ℝ=>g t-t*g₁ 0) (g₁ t-g₁ 0) t := by
    convert! (hd t ht).sub ((hasDerivAt_id t).mul_const (g₁ 0)) using 1
    simp only [one_mul]
  have he : (∫ t in (0 : ℝ)..1,g₁ t-g₁ 0)=g 1-g 0-g₁ 0 := by
    have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht=>hd' t (by simpa using ht)) hi
    simp only [one_mul,zero_mul,sub_zero] at hh
    linarith only [hh]
  have hh := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
    (by norm_num : (0:ℝ)≤1) (f := fun t : ℝ=>g₁ t-g₁ 0) (g := fun _ : ℝ=>C)
    (Filter.Eventually.of_forall fun t ht=>by
      simpa only [Real.norm_eq_abs] using hb t ⟨ht.1.le,ht.2⟩) intervalIntegrable_const
  simpa only [he,Real.norm_eq_abs,intervalIntegral.integral_const,sub_zero,one_smul] using hh

/-- The actual scalar endpoint remainders depend only on oscillation of
the continuous third derivative. The first constant is deliberately
coarse; the defect retains its exact integral mass 1/12.
Article: main_krylov, thm:ss1F, continuous D3 branch. -/
theorem trapezoid_endpoint_modulus (f f₁ f₂ f₃ : ℝ → ℝ)
    (h₁ : ∀ t ∈ Icc (0 : ℝ) 1,HasDerivAt f (f₁ t) t)
    (h₂ : ∀ t ∈ Icc (0 : ℝ) 1,HasDerivAt f₁ (f₂ t) t)
    (h₃ : ∀ t ∈ Icc (0 : ℝ) 1,HasDerivAt f₂ (f₃ t) t)
    (hc : ContinuousOn f₃ (Icc 0 1)) (C : ℝ) (hC : 0≤C)
    (hmod : ∀ t ∈ Icc (0 : ℝ) 1,|f₃ t-f₃ 1|≤C) :
    |f₁ 1-f₁ 0-6*trapezoidDefect f f₁-f₂ 1|≤C ∧
      |trapezoidDefect f f₁+f₃ 1/12|≤C/12 := by
  have hi₁ : IntervalIntegrable (fun t : ℝ=>t*f₃ t) volume 0 1 :=
    (continuous_id.continuousOn.mul hc).intervalIntegrable_of_Icc (by norm_num : (0:ℝ)≤1)
  have hi₂ : IntervalIntegrable (fun t : ℝ=>t*(1-t)*f₃ t) volume 0 1 :=
    ((by fun_prop : Continuous (fun t : ℝ=>t*(1-t))).continuousOn.mul hc).intervalIntegrable_of_Icc
      (by norm_num : (0:ℝ)≤1)
  have haux : (∫ t in (0 : ℝ)..1,t*f₃ t)=f₂ 1-f₁ 1+f₁ 0 := by
    have hd t (ht : t ∈ Icc (0 : ℝ) 1) :
        HasDerivAt (fun t : ℝ=>t*f₂ t-f₁ t) (t*f₃ t) t := by
      convert! ((hasDerivAt_id t).mul (h₃ t ht)).sub (h₂ t ht) using 1
      simp only [id_eq]
      ring
    have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht=>hd t (by simpa using ht)) hi₁
    simpa only [one_mul,zero_mul,zero_sub,sub_neg_eq_add] using hh
  have hvalue : f₁ 1-f₁ 0-6*trapezoidDefect f f₁-f₂ 1=
      ∫ t in (0 : ℝ)..1,(2*t-3*t^2)*f₃ t := by
    have he : (fun t : ℝ=>(2*t-3*t^2)*f₃ t)=
        (fun t : ℝ=>3*(t*(1-t)*f₃ t)-t*f₃ t) := by ext t; ring
    rw [he,intervalIntegral.integral_sub (hi₂.const_mul 3) hi₁,
      intervalIntegral.integral_const_mul,haux,trapezoid_integral f f₁ f₂ f₃ h₁ h₂ h₃ hc]
    ring
  have hweight : (∫ t in (0 : ℝ)..1,2*t-3*t^2)=0 := by
    have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t (_ : t ∈ uIcc (0 : ℝ) 1)=>endpoint_kernel_hasDerivAt t)
      ((by fun_prop : Continuous (fun t : ℝ=>2*t-3*t^2)).intervalIntegrable 0 1)
    norm_num at hh
    exact hh
  have hcenter : (∫ t in (0 : ℝ)..1,(2*t-3*t^2)*(f₃ t-f₃ 1))=
      f₁ 1-f₁ 0-6*trapezoidDefect f f₁-f₂ 1 := by
    rw [show (fun t : ℝ=>(2*t-3*t^2)*(f₃ t-f₃ 1))=
      (fun t : ℝ=>(2*t-3*t^2)*f₃ t-(2*t-3*t^2)*f₃ 1) from
      funext (fun _=>mul_sub _ _ _)]
    rw [intervalIntegral.integral_sub
      (f := fun t : ℝ=>(2*t-3*t^2)*f₃ t)
      (g := fun t : ℝ=>(2*t-3*t^2)*f₃ 1)
      (((by fun_prop : Continuous (fun t : ℝ=>2*t-3*t^2)).continuousOn.mul hc).intervalIntegrable_of_Icc
        (by norm_num : (0:ℝ)≤1))
      ((by fun_prop : Continuous (fun t : ℝ=>(2*t-3*t^2)*f₃ 1)).intervalIntegrable 0 1),
      intervalIntegral.integral_mul_const,hweight,zero_mul,sub_zero,←hvalue]
  have hfirst := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
    (by norm_num : (0:ℝ)≤1) (f := fun t : ℝ=>(2*t-3*t^2)*(f₃ t-f₃ 1)) (g := fun _ : ℝ=>C)
    (Filter.Eventually.of_forall fun t ht=>by
      have ht₀ : 0≤t := ht.1.le
      have ht₁ : t≤1 := ht.2
      have hw : |2*t-3*t^2|≤1 := abs_le.mpr
        ⟨by nlinarith [mul_nonneg (sub_nonneg.mpr ht₁) (by linarith : 0≤3*t+1)],
          by nlinarith [sq_nonneg t,sq_nonneg (t-1)]⟩
      rw [Real.norm_eq_abs,abs_mul]
      exact (mul_le_mul_of_nonneg_left (hmod t ⟨ht₀,ht₁⟩) (abs_nonneg _)).trans
        ((mul_le_mul_of_nonneg_right hw hC).trans_eq (one_mul C))) intervalIntegrable_const
  have hi : IntervalIntegrable (fun t : ℝ=>t*(1-t)*(f₃ t-f₃ 1)) volume 0 1 :=
    ((by fun_prop : Continuous (fun t : ℝ=>t*(1-t))).continuousOn.mul
      (hc.sub continuousOn_const)).intervalIntegrable_of_Icc (by norm_num : (0:ℝ)≤1)
  have he : trapezoidDefect f f₁+f₃ 1/12=
      -(1/2 : ℝ)*(∫ t in (0 : ℝ)..1,t*(1-t)*(f₃ t-f₃ 1)) := by
    rw [trapezoid_integral f f₁ f₂ f₃ h₁ h₂ h₃ hc]
    rw [show (fun t : ℝ=>t*(1-t)*(f₃ t-f₃ 1))=
      (fun t : ℝ=>t*(1-t)*f₃ t-t*(1-t)*f₃ 1) from
      funext (fun _=>mul_sub _ _ _)]
    rw [intervalIntegral.integral_sub
      (f := fun t : ℝ=>t*(1-t)*f₃ t) (g := fun t : ℝ=>t*(1-t)*f₃ 1) hi₂
      ((by fun_prop : Continuous (fun t : ℝ=>t*(1-t)*f₃ 1)).intervalIntegrable 0 1),
      intervalIntegral.integral_mul_const,integral_trapezoid_weight]
    ring
  have hsecond := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
    (by norm_num : (0:ℝ)≤1) (f := fun t : ℝ=>t*(1-t)*(f₃ t-f₃ 1))
    (g := fun t : ℝ=>C*(t*(1-t)))
    (Filter.Eventually.of_forall fun t ht=>by
      have hw : 0≤t*(1-t) := mul_nonneg ht.1.le (sub_nonneg.mpr ht.2)
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg hw]
      exact (mul_le_mul_of_nonneg_left (hmod t ⟨ht.1.le,ht.2⟩) hw).trans_eq (mul_comm _ _))
    ((by fun_prop : Continuous (fun t : ℝ=>C*(t*(1-t)))).intervalIntegrable 0 1)
  constructor
  · simpa only [hcenter,Real.norm_eq_abs,intervalIntegral.integral_const,sub_zero,one_smul] using hfirst
  · rw [intervalIntegral.integral_const_mul,integral_trapezoid_weight,Real.norm_eq_abs] at hsecond
    rw [he,abs_mul]
    norm_num
    nlinarith only [hsecond]

end
end krylov.Functions
