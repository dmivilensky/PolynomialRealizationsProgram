import nesterov.Flow.SpreadAnalysis
import Mathlib.Analysis.Calculus.Taylor

/-! The source midpoint quadrature constants in the spread-spectrum proof:
the O(J⁻²) bound with the literal factor 1/6. -/
noncomputable section
open Finset Set Filter intervalIntegral
namespace nesterov.Flow

private theorem linear_taylor_bound {f : ℝ→ℝ} (hf : ContDiff ℝ 2 f) {M : ℝ}
    (hM : ∀ y∈Icc (1:ℝ) 2,|iteratedDeriv 2 f y|≤M)
    {m x : ℝ} (hm : m∈Icc (1:ℝ) 2) (hx : x∈Icc (1:ℝ) 2) :
    |f x-f m-(x-m)*deriv f m|≤M/2*(x-m)^2 := by
  by_cases hmx : m=x
  · subst x
    simp
  obtain ⟨y,hy,he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (n:=1) hmx hf.contDiffOn
  have h₁ : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hd : iteratedDerivWithin 1 f (uIcc m x) m=deriv f m := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hmx) h₁.contDiffAt left_mem_uIcc,
      iteratedDeriv_one]
  have ht : taylorWithinEval f 1 (uIcc m x) m x=f m+(x-m)*deriv f m := by
    rw [show 1=0+1 by rfl,taylorWithinEval_succ,taylor_within_zero_eval,hd]
    norm_num
  rw [ht] at he
  have hxy : y∈Icc (1:ℝ) 2 := uIcc_subset_Icc hm hx (uIoo_subset_uIcc_self hy)
  have hb := hM y hxy
  have he' : f x-f m-(x-m)*deriv f m=iteratedDeriv 2 f y*(x-m)^2/2 := by
    norm_num at he
    linarith
  rw [he',abs_div,abs_mul,abs_pow,sq_abs]
  norm_num
  nlinarith [mul_le_mul_of_nonneg_right hb (sq_nonneg (x-m))]

private theorem midpoint_cell_error {f : ℝ→ℝ} (hf : ContDiff ℝ 2 f) {M a b : ℝ}
    (hM : ∀ y∈Icc (1:ℝ) 2,|iteratedDeriv 2 f y|≤M)
    (ha : 1≤a) (hb : b≤2) (hab : a≤b) :
    |(∫ x in a..b,f x)-(b-a)*f ((a+b)/2)|≤M*(b-a)^3/24 := by
  let m := (a+b)/2
  let R := fun x=>f x-f m-(x-m)*deriv f m
  have hm : m∈Icc (1:ℝ) 2 := by dsimp [m]; constructor <;> linarith
  have hbound (x : ℝ) (hx : x∈Ioc a b) : ‖R x‖≤M/2*(x-m)^2 := by
    rw [Real.norm_eq_abs]
    exact linear_taylor_bound hf hM hm ⟨ha.trans hx.1.le,hx.2.trans hb⟩
  have hnorm := norm_integral_le_of_norm_le (μ:=MeasureTheory.volume) hab (Eventually.of_forall hbound)
    ((by fun_prop : Continuous (fun x : ℝ=>M/2*(x-m)^2)).intervalIntegrable a b)
  have hlin : (∫ x in a..b,(x-m)*deriv f m)=0 := by
    rw [integral_mul_const,integral_sub
      ((by fun_prop : Continuous (fun x : ℝ=>x)).intervalIntegrable _ _)
      ((by fun_prop : Continuous (fun _x : ℝ=>m)).intervalIntegrable _ _),
      integral_id,integral_const,smul_eq_mul]
    dsimp [m]
    ring
  have hR : (∫ x in a..b,R x)=(∫ x in a..b,f x)-(b-a)*f m := by
    dsimp only [R]
    rw [integral_sub
      ((show Continuous (fun x : ℝ=>f x-f m) from hf.continuous.sub continuous_const).intervalIntegrable _ _)
      ((by fun_prop : Continuous (fun x : ℝ=>(x-m)*deriv f m)).intervalIntegrable _ _),
      integral_sub (hf.continuous.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _),
      integral_const,smul_eq_mul,hlin,sub_zero]
  have hsq : (∫ x in a..b,M/2*(x-m)^2)=M*(b-a)^3/24 := by
    rw [integral_const_mul,integral_comp_sub_right (fun x : ℝ=>x^2) m,integral_pow]
    dsimp [m]
    norm_num
    ring
  rw [hR,Real.norm_eq_abs,hsq] at hnorm
  exact hnorm

/-- Composite midpoint quadrature with the sharp classical second-derivative
constant on the article's unit frequency interval. -/
theorem midpoint_error_secondDerivative {J : ℕ} (hJ : 0<J) {f : ℝ→ℝ}
    (hf : ContDiff ℝ 2 f) {M : ℝ}
    (hM : ∀ y∈Icc (1:ℝ) 2,|iteratedDeriv 2 f y|≤M) :
    |(∫ x in (1:ℝ)..2,f x)-midpointAverage J f|≤M/(24*(J:ℝ)^2) := by
  have hJp : (0:ℝ)<J := Nat.cast_pos.mpr hJ
  have hJn : (J:ℝ)≠0 := hJp.ne'
  have hcell (j : ℕ) (hj : j<J) :
      |(∫ x in grid J j..grid J (j+1),f x)-(1/(J:ℝ))*f (midpoint J j)|≤M/(24*(J:ℝ)^3) := by
    have hj' : (j:ℝ)+1≤J := by exact_mod_cast hj
    have hstep : grid J (j+1)-grid J j=1/(J:ℝ) := by dsimp [grid]; push_cast; ring
    have hlo : 1≤grid J j := le_add_of_nonneg_right (by positivity)
    have hhi : grid J (j+1)≤2 := by
      dsimp [grid]
      have hh : ((j+1:ℕ):ℝ)/(J:ℝ)≤1 := (div_le_one hJp).mpr (by exact_mod_cast hj)
      linarith
    have hab : grid J j≤grid J (j+1) := by linarith [div_pos zero_lt_one hJp]
    have hmid : (grid J j+grid J (j+1))/2=midpoint J j := by
      dsimp [grid,midpoint]
      push_cast
      ring
    have he := midpoint_cell_error hf hM hlo hhi hab
    rw [hstep,hmid] at he
    convert he using 1
    field_simp
  have hsum := sum_integral_adjacent_intervals (μ:=MeasureTheory.volume) (a:=grid J) (n:=J)
    (fun j _=>hf.continuous.intervalIntegrable (grid J j) (grid J (j+1)))
  have hg0 : grid J 0=1 := by simp [grid]
  have hgJ : grid J J=2 := by simp [grid,hJn]; norm_num
  rw [hg0,hgJ] at hsum
  rw [←hsum,midpointAverage,mul_sum,←sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _j∈range J,M/(24*(J:ℝ)^3) := sum_le_sum (fun j hj=>hcell j (mem_range.mp hj))
    _ = _ := by simp; field_simp

theorem weighted_cos_secondDerivative (x lam : ℝ) :
    iteratedDeriv 2 (fun y : ℝ=>y^2*Real.cos (y*x)) lam=
      2*Real.cos (lam*x)-4*lam*x*Real.sin (lam*x)-lam^2*x^2*Real.cos (lam*x) := by
  have h₁ (y : ℝ) : HasDerivAt (fun y : ℝ=>y^2*Real.cos (y*x))
      (2*y*Real.cos (y*x)-y^2*Real.sin (y*x)*x) y := by
    convert ((hasDerivAt_pow 2 y).mul (((hasDerivAt_id y).mul_const x).cos)) using 1
    · rfl
    · dsimp
      ring
  have h₂ (y : ℝ) : HasDerivAt
      (fun y : ℝ=>2*y*Real.cos (y*x)-y^2*Real.sin (y*x)*x)
      (2*Real.cos (y*x)-4*y*x*Real.sin (y*x)-y^2*x^2*Real.cos (y*x)) y := by
    convert ((((hasDerivAt_id y).const_mul 2).mul (((hasDerivAt_id y).mul_const x).cos)).sub
      (((hasDerivAt_pow 2 y).mul (((hasDerivAt_id y).mul_const x).sin)).mul_const x)) using 1
    · rfl
    · dsimp
      ring
  rw [iteratedDeriv_succ (n:=1),iteratedDeriv_one,funext (fun y=>(h₁ y).deriv)]
  exact (h₂ lam).deriv

theorem weighted_one_sub_cos_secondDerivative (x lam : ℝ) :
    iteratedDeriv 2 (fun y : ℝ=>y^2*(1-Real.cos (y*x))) lam=
      2*(1-Real.cos (lam*x))+4*lam*x*Real.sin (lam*x)+lam^2*x^2*Real.cos (lam*x) := by
  have h₁ (y : ℝ) : HasDerivAt (fun y : ℝ=>y^2*(1-Real.cos (y*x)))
      (2*y*(1-Real.cos (y*x))+y^2*Real.sin (y*x)*x) y := by
    convert ((hasDerivAt_pow 2 y).mul
      ((hasDerivAt_const y 1).sub (((hasDerivAt_id y).mul_const x).cos))) using 1
    · rfl
    · dsimp
      ring
  have h₂ (y : ℝ) : HasDerivAt
      (fun y : ℝ=>2*y*(1-Real.cos (y*x))+y^2*Real.sin (y*x)*x)
      (2*(1-Real.cos (y*x))+4*y*x*Real.sin (y*x)+y^2*x^2*Real.cos (y*x)) y := by
    convert ((((hasDerivAt_id y).const_mul 2).mul
      ((hasDerivAt_const y 1).sub (((hasDerivAt_id y).mul_const x).cos))).add
      (((hasDerivAt_pow 2 y).mul (((hasDerivAt_id y).mul_const x).sin)).mul_const x)) using 1
    · rfl
    · dsimp
      ring
  rw [iteratedDeriv_succ (n:=1),iteratedDeriv_one,funext (fun y=>(h₁ y).deriv)]
  exact (h₂ lam).deriv

private theorem oscillatory_second_terms_bound {x lam : ℝ} (hx : 0≤x)
    (hlam : lam∈Icc (1:ℝ) 2) :
    |4*lam*x*Real.sin (lam*x)|≤8*x ∧ |lam^2*x^2*Real.cos (lam*x)|≤4*x^2 := by
  have hlam0 : 0≤lam := by linarith [hlam.1]
  constructor
  · rw [abs_mul,abs_of_nonneg (by positivity : 0≤4*lam*x)]
    have hh := mul_le_mul_of_nonneg_left (Real.abs_sin_le_one (lam*x))
      (show 0≤4*lam*x by positivity)
    have hl := mul_le_mul_of_nonneg_right hlam.2 hx
    nlinarith
  · rw [abs_mul,abs_of_nonneg (by positivity : 0≤lam^2*x^2)]
    have hh := mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (lam*x))
      (show 0≤lam^2*x^2 by positivity)
    have hl := mul_le_mul_of_nonneg_right (show lam^2≤4 by nlinarith [hlam.1,hlam.2]) (sq_nonneg x)
    nlinarith

/-- The literal uniform second-derivative bound asserted in the source. -/
theorem weighted_UV_secondDerivative_bound {x lam : ℝ} (hx : 0≤x)
    (hlam : lam∈Icc (1:ℝ) 2) :
    |iteratedDeriv 2 (fun y : ℝ=>y^2*(1-Real.cos (y*x))) lam|≤4*(1+x)^2 ∧
    |iteratedDeriv 2 (fun y : ℝ=>y^2*Real.cos (y*x)) lam|≤4*(1+x)^2 := by
  obtain ⟨hs,hc⟩ := oscillatory_second_terms_bound hx hlam
  have hfirstU : |2*(1-Real.cos (lam*x))|≤4 := by
    rw [abs_of_nonneg (by nlinarith [Real.cos_le_one (lam*x)])]
    nlinarith [Real.neg_one_le_cos (lam*x)]
  have hfirstV : |2*Real.cos (lam*x)|≤4 := by
    rw [abs_mul]
    norm_num
    linarith [Real.abs_cos_le_one (lam*x)]
  constructor
  · rw [weighted_one_sub_cos_secondDerivative]
    have hh := (abs_add_le
      (2*(1-Real.cos (lam*x))+4*lam*x*Real.sin (lam*x))
      (lam^2*x^2*Real.cos (lam*x))).trans
        (add_le_add ((abs_add_le _ _).trans (add_le_add hfirstU hs)) hc)
    nlinarith
  · rw [weighted_cos_secondDerivative]
    have hh := (abs_sub
      (2*Real.cos (lam*x)-4*lam*x*Real.sin (lam*x))
      (lam^2*x^2*Real.cos (lam*x))).trans
        (add_le_add ((abs_sub _ _).trans (add_le_add hfirstV hs)) hc)
    nlinarith

/-- The exact O(J⁻²) pair of midpoint bounds, for every nonnegative lag. -/
theorem midpoint_UV_error_sharp {J : ℕ} (hJ : 0<J) {x : ℝ} (hx : 0≤x) :
    |spreadU x-midpointAverage J (fun lam=>lam^2*(1-Real.cos (lam*x)))|≤
      (1+x)^2/(6*(J:ℝ)^2) ∧
    |spreadV x-midpointAverage J (fun lam=>lam^2*Real.cos (lam*x))|≤
      (1+x)^2/(6*(J:ℝ)^2) := by
  constructor
  · have hh := midpoint_error_secondDerivative hJ
      (show ContDiff ℝ 2 (fun y : ℝ=>y^2*(1-Real.cos (y*x))) by fun_prop)
      (fun y hy=>(weighted_UV_secondDerivative_bound hx hy).1)
    exact hh.trans_eq (by ring)
  · have hh := midpoint_error_secondDerivative hJ
      (show ContDiff ℝ 2 (fun y : ℝ=>y^2*Real.cos (y*x)) by fun_prop)
      (fun y hy=>(weighted_UV_secondDerivative_bound hx hy).2)
    exact hh.trans_eq (by ring)

theorem midpoint_UV_error_uniform_sharp {J : ℕ} (hJ : 0<J) {x X : ℝ}
    (hx : 0≤x) (hX : x≤X) :
    |spreadU x-midpointAverage J (fun lam=>lam^2*(1-Real.cos (lam*x)))|≤
      (1+X)^2/(6*(J:ℝ)^2) ∧
    |spreadV x-midpointAverage J (fun lam=>lam^2*Real.cos (lam*x))|≤
      (1+X)^2/(6*(J:ℝ)^2) := by
  have hh := midpoint_UV_error_sharp hJ hx
  have hbound : (1+x)^2/(6*(J:ℝ)^2)≤(1+X)^2/(6*(J:ℝ)^2) :=
    div_le_div_of_nonneg_right (by nlinarith) (by positivity)
  exact ⟨hh.1.trans hbound,hh.2.trans hbound⟩
end nesterov.Flow
