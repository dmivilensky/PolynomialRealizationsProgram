import polyak.Boundary.P2.Atoms
import polyak.Boundary.P2.MomentSource

/-!
Article: quadratic reduction of actual P₂ probability integrals.
Use: the numerical source moment functional is proved to be the actual spectral average.
-/

namespace polyak.Boundary.P2
noncomputable section
open Spectral Polynomial MeasureTheory

/-- Article: integration against the actual two-atom probability measure. -/
theorem avg_spectrum {z : ℝ} (hz : z∈parameterInterval) (h1 : zeta1 ≤ z) (f : Frequency → ℝ) :
    avg (spectrum z hz h1) f=(1-p z)*f (lowerFrequency z hz)+p z*f (upperFrequency z hz) := by
  unfold avg spectrum
  rw [Waves.finiteSpectrum_integral,Fintype.sum_bool]
  change p z*f (upperFrequency z hz)+(1-p z)*f (lowerFrequency z hz)=_
  ring

/-- Article: every root of the atom quadratic obeys the source power recurrence. -/
theorem quadratic_power_recurrence {a b c : ℝ} (hc : c^2+a*c+b=0) (n : ℕ) :
    c^(n+2)= -a*c^(n+1)-b*c^n := by
  rw [pow_add,pow_succ]
  linear_combination c^n*hc

/-- Article: all reduced moments equal the actual weighted powers, at every order. -/
theorem moment_eq {z : ℝ} (hz : z∈parameterInterval) (n : ℕ) :
    moment z n=(1-p z)*x z^n+p z*y z^n := by
  have hxy : y z-x z≠0 := ne_of_gt (sub_pos.mpr (roots_order hz).2.2)
  have hm : p z*(y z-x z)=meanCosine z-x z := by unfold p; field_simp
  induction n using Nat.twoStepInduction with
  | zero => simp only [moment,pow_zero,mul_one]; ring
  | one => simp only [moment,pow_one]; nlinarith [hm]
  | more n ih0 ih1 =>
    have hx : x z^2+atomA z*x z+atomB z=0 := atomPolynomial_x hz
    have hy : y z^2+atomA z*y z+atomB z=0 := atomPolynomial_y hz
    rw [moment,ih0,ih1,quadratic_power_recurrence hx,quadratic_power_recurrence hy]
    ring

/-- Article: every actual power average equals the independently specified reduced source moment. -/
theorem avg_power {z : ℝ} (hz : z∈parameterInterval) (h1 : zeta1 ≤ z) (n : ℕ) :
    avg (spectrum z hz h1) (fun c => (c : ℝ)^n)=moment z n := by
  rw [avg_spectrum,moment_eq hz n]
  rfl

/-- Article: exact polynomial integration after reduction modulo the actual atom quadratic. -/
theorem avg_polynomial {z : ℝ} (hz : z∈parameterInterval) (h1 : zeta1 ≤ z) (q : ℝ[X]) :
    avg (spectrum z hz h1) (fun c => q.eval (c : ℝ))=momentLinear z q := by
  rw [avg_spectrum]
  change (1-p z)*q.eval (x z)+p z*q.eval (y z)=momentLinear z q
  induction q using Polynomial.induction_on' with
  | add f g ihf ihg =>
    rw [eval_add,eval_add,map_add]
    linarith [ihf,ihg]
  | monomial n a =>
    rw [eval_monomial,eval_monomial,momentLinear_monomial,moment_eq hz n]
    ring

/-- Article: the actual mean minimizer gap is the rational source ḡ. -/
theorem meanG_spectrum {z : ℝ} (hz : z∈parameterInterval) (h1 : zeta1 ≤ z) :
    meanG (spectrum z hz h1) (u z)=meanGap z := by
  unfold meanG
  rw [avg_power]
  simp only [moment,meanGap]
  ring

/-- Article: all actual raw slacks agree with the rational source after quadratic reduction. -/
theorem actual_reducedSlack {z t : ℝ} (hz : z∈parameterInterval) (h1 : zeta1 ≤ z)
    (ht : Real.cosh t=G z) (hs : Real.sinh t≠0) (n : ℕ) (hn : 1 ≤ n) (δ : ℝ) :
    meanA (spectrum z hz h1) (u z) t n+δ*meanB (spectrum z hz h1) (u z) n-
      δ*(d z/Real.sinh t)*Real.sinh (n*t)=reducedSlack z n δ := by
  let q : ℝ[X] := (1-X^2-C (u z^2))*(C (chebT n (G z))-Chebyshev.T ℝ (n : ℤ))+
    C (δ*2*u z)*(1-X^2)*Chebyshev.U ℝ ((n-1 : ℕ) : ℤ)
  have hq (c : Frequency) : q.eval (c : ℝ)=lagA (u z) t n c+δ*lagB (u z) n c := by
    dsimp [q,lagA,lagD,g,lagB,chebT,chebU]
    rw [←Spectral.chebT_cosh n t,ht]
    norm_num [chebT]
    ring
  have hiA := integrable_continuous (spectrum z hz h1)
    (show Continuous (fun c : Frequency => lagA (u z) t n c) by unfold lagA lagD g chebT; fun_prop)
  have hiB := integrable_continuous (spectrum z hz h1)
    (show Continuous (fun c : Frequency => lagB (u z) n c) by unfold lagB chebU; fun_prop)
  have havg := avg_polynomial hz h1 q
  simp_rw [hq] at havg
  unfold avg at havg
  rw [integral_add hiA (hiB.const_mul δ),integral_const_mul] at havg
  change avg (spectrum z hz h1) (fun c => lagA (u z) t n c)+
    δ*avg (spectrum z hz h1) (fun c => lagB (u z) n c)=momentLinear z q at havg
  rw [←meanA_eq_integral,←meanB_eq_integral] at havg
  have hsinh := Boundary.lagDenominator_mul_sinh t n hn
  change chebU (n-1) (Real.cosh t)*Real.sinh t=Real.sinh (n*t) at hsinh
  rw [ht] at hsinh
  have hc : (d z/Real.sinh t)*Real.sinh (n*t)=d z*chebU (n-1) (G z) := by
    rw [←hsinh]
    field_simp
  change _=momentLinear z q-δ*d z*chebU (n-1) (G z)
  rw [show δ*(d z/Real.sinh t)*Real.sinh (n*t)=δ*((d z/Real.sinh t)*Real.sinh (n*t)) by ring,hc]
  linarith [havg]

end
end polyak.Boundary.P2
