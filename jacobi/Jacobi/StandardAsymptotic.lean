import jacobi.Jacobi.StandardNorm
import jacobi.Reference.PositiveGammaRatio

/-!
The actual standard Jacobi endpoint values have their exact power law.
The norm is the genuine weighted integral, already evaluated in Gamma
functions at every positive degree. Euler's Gamma-ratio limit supplies
its asymptotic throughout the full two-parameter range.
Use: StandardJacobi estimates the genuine inverse conductance tails and
passes the actual matrix entries and energy to their one-sided limits.
Article: jacobi, Theorem 5.4, Equation (5.10).
Article role: the endpoint and recurrence-coefficient power limits.
-/
namespace jacobi.Jacobi
noncomputable section
open Real Filter jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The genuine standard Jacobi norm has its exact leading constant.
The shift to degree n+1 keeps every Gamma argument positive without
restricting the parameter sum; dropping that finite shift recovers n.
Article: jacobi, Theorem 5.4, Equation (5.10).
-/
theorem standard_norm_power_limit {a b : ℝ} (ha : -1<a) (hb : -1<b) :
    Tendsto (fun n : ℕ => jacobiNorm a b n*(n:ℝ)^(2*a+1)) atTop
      (𝓝 (Gamma (a+1)^2/2)) := by
  have hg1 := positive_gamma_ratio_limit (p := 1) (q := a+2) (by norm_num) (by linarith)
  have hg2 := positive_gamma_ratio_limit (p := b+2) (q := a+b+2) (by linarith) (by linarith)
  have hf : Tendsto (fun n : ℕ => ((n:ℝ)+1)/(2*(n:ℝ)+a+b+3)) atTop (𝓝 (1/2:ℝ)) := by
    have h := (shifted_nat_ratio 1 ((a+b+3)/2)).div_const 2
    convert h using 1
    funext n
    rw [div_div]
    congr 1
    ring
  have hp := (shifted_nat_ratio 1 0).rpow_const (p := 2*a+1) (Or.inl one_ne_zero)
  simp only [add_zero,one_rpow] at hp
  have h := (((hf.mul hg1).mul hg2).mul hp).const_mul (Gamma (a+1)^2)
  simp only [mul_one,mul_one_div] at h
  have h' : Tendsto (fun n : ℕ => jacobiNorm a b (n+1)*((n+1:ℕ):ℝ)^(2*a+1))
      atTop (𝓝 (Gamma (a+1)^2/2)) := by
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
    have hnR : (0:ℝ)<n := Nat.cast_pos.mpr hn
    have hA : 0<(n:ℝ)+a+2 := by linarith
    have hB : 0<(n:ℝ)+b+2 := by linarith
    have hS : 0<(n:ℝ)+a+b+2 := by linarith
    have hD : 0<2*(n:ℝ)+a+b+3 := by linarith
    rw [jacobiNorm_formula_succ ha hb,← Gamma_nat_eq_factorial]
    simp only [Nat.cast_add,Nat.cast_one]
    rw [show (n:ℝ)+1+b+1=(n:ℝ)+(b+2) by ring,
      show (n:ℝ)+1+a+1=(n:ℝ)+(a+2) by ring,
      show (n:ℝ)+1+a+b+1=(n:ℝ)+(a+b+2) by ring,
      show 2*((n:ℝ)+1)+a+b+1=2*(n:ℝ)+a+b+3 by ring]
    rw [Gamma_add_one (show (n:ℝ)+1≠0 by positivity),
      div_rpow (by positivity : 0≤(n:ℝ)+1) hnR.le]
    have he1 : a+2-1=a+1 := by ring
    have he2 : a+b+2-(b+2)=a := by ring
    rw [he1,he2]
    have hpow : (n:ℝ)^(2*a+1)=(n:ℝ)^(a+1)*(n:ℝ)^a := by
      rw [← rpow_add hnR]
      congr 1
      ring
    rw [hpow]
    field_simp [hnR.ne',hA.ne',hB.ne',hS.ne',hD.ne',
      (Gamma_pos_of_pos hA).ne',(Gamma_pos_of_pos hB).ne',(Gamma_pos_of_pos hS).ne',
      (rpow_pos_of_pos hnR (a+1)).ne',(rpow_pos_of_pos hnR a).ne']
  exact (tendsto_add_atTop_iff_nat 1).mp h'

/-- The exact positive endpoint-square power constant for the probability
Jacobi weight. Its dependence on b is a common normalization that cancels
between the two endpoint factors and the inverse conductance.
Article: jacobi, Theorem 5.4, Equation (5.10).
-/
def standardEndpointConstant (a b : ℝ) : ℝ :=
  2*jacobiNorm a b 0/Gamma (a+1)^2

/-- The actual endpoint-square leading constant is strictly positive.
Article: jacobi, Theorem 5.4, Equation (5.10).
-/
theorem standardEndpointConstant_pos {a b : ℝ} (ha : -1<a) (hb : -1<b) :
    0<standardEndpointConstant a b := by
  exact div_pos (mul_pos (by norm_num) (jacobiNorm_pos ha hb 0))
    (sq_pos_of_pos (Gamma_pos_of_pos (by linarith)))

/-- The genuine squared endpoint values have exponent 2*a+1 and the
proved positive constant, with no asymptotic coefficient premise.
Article: jacobi, Theorem 5.4, Equation (5.10).
-/
theorem standardEndpointSquare_power_limit {a b : ℝ} (ha : -1<a) (hb : -1<b) :
    Tendsto (fun n : ℕ => standardEndpointSquare a b n/(n:ℝ)^(2*a+1)) atTop
      (𝓝 (standardEndpointConstant a b)) := by
  have h := (tendsto_const_nhds (x := jacobiNorm a b 0)).div
    (standard_norm_power_limit ha hb)
    (div_ne_zero (pow_ne_zero _ (Gamma_pos_of_pos (show 0<a+1 by linarith)).ne') (by norm_num))
  convert h using 1
  · funext n
    dsimp [standardEndpointSquare]
    ring
  · dsimp [standardEndpointConstant]
    ring

end
end jacobi.Jacobi
