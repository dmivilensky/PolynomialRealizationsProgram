import jacobi.Reference.NegativeKernel
import jacobi.Reference.CosineDomination
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
Article: jacobi, Appendix C.1 (negative-energy bounds).
The actual reference solution is strictly positive at z=c_0-y^2.
Its upper bound has the original endpoint/frequency minimum, and its
uniform lower bound away from t=0 has the matching exp(t*y)*y^(-gamma)
scale. The lower bound integrates only the original prefix 0<s<1/y;
its coefficient is the genuine positive compact minimum, with no
numerical or asymptotic premise.
Use: transfers proved literal-integral positivity and both frequency bounds to the same f(t,c_0-y^2) used in the midpoint argument.
-/
namespace jacobi.Reference
noncomputable section
open Real Set MeasureTheory Filter _root_.Complex
set_option backward.isDefEq.respectTransparency false

/-- The actual reference solution on the shifted negative-energy axis is its genuine imaginary-frequency wave, for every real y.
Use: transfers proved literal-integral positivity and both frequency bounds to the same f(t,c_0-y^2) used in the midpoint argument.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Proof: the actual imaginary frequency square is -y^2; apply the already proved independence of the chosen frequency square root. -/
theorem solution_negative_eq_wave (a y t : ℝ) :
    solution a ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ) t=
      wave a (Complex.I*(y:ℂ)) t := by
  apply solution_eq_wave
  push_cast
  rw [mul_pow,Complex.I_sq]
  ring

/-- The actual negative-energy reference solution has the full original positivity and upper minimum estimate.
Use: supplies the upper half of Negative-energy bounds for the subsequent midpoint quotient and concentration arguments.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Proof: strict positivity comes from the actual cosh integral; the
proved genuine complex-frequency minimum estimate specializes to
omega=i*y, whose norm and imaginary part are exactly y for y>=1. -/
theorem solution_negative_upper {a : ℝ} (ha : -1<a) :
    ∃ C : ℝ,0<C ∧ ∀ y : ℝ,1≤y → ∀ t∈Ioc (0:ℝ) (1/2),
      0<(solution a ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ) t).re ∧
        (solution a ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ) t).re≤
          C*Real.exp (t*y)*min (t^(gamma a)) (y^(-gamma a)) := by
  -- Both the integral positivity and the frequency estimate refer to the same previously defined reference function.
  obtain ⟨C,hC,hbound⟩ := wave_minimum_high_frequency ha
  refine ⟨C,hC,fun y hy t ht => ?_⟩
  have hyp : 0<y := lt_of_lt_of_le zero_lt_one hy
  have ht' : t∈Ioo (0:ℝ) 1 := ⟨ht.1,by linarith [ht.2]⟩
  have hn : ‖Complex.I*(y:ℂ)‖=y := by
    rw [norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hyp]
  have hb := hbound (Complex.I*(y:ℂ)) (by rw [hn]; exact hy) t ⟨ht.1.le,ht.2⟩
  simp only [hn,Complex.mul_im,Complex.I_re,Complex.I_im,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,one_mul,zero_add,abs_of_pos hyp] at hb
  rw [solution_negative_eq_wave]
  refine ⟨wave_imaginary_pos ha y ht',?_⟩
  exact ((le_trans (le_abs_self _) (Complex.abs_re_le_norm _)).trans hb).trans_eq (by ring)

/-- The original imaginary-frequency reference wave has a uniform lower bound with the exact exponential and inverse-frequency scale on every spatial interval away from zero.
Use: proves the lower half of Negative-energy bounds and supplies the true reference denominator for the midpoint comparison in Proposition C.2.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Proof: take the proved positive compact minimum of the regular
normalized density coefficient. Restrict the genuine integral to
0<s<1/y, where cosh((t-2s)*y)>=exp(t*y-2)/2. The singular power
integrates exactly to y^(-gamma)/gamma, giving a positive uniform
constant and an explicit finite threshold max(1,2/A). -/
theorem wave_imaginary_lower {a A : ℝ} (ha : -1<a) (hA : A∈Ioc (0:ℝ) (1/2)) :
    ∃ c Y : ℝ,0<c ∧ 1≤Y ∧ ∀ y : ℝ,Y≤y → ∀ t∈Icc A (1/2),
      c*Real.exp (t*y)*y^(-gamma a)≤(wave a (Complex.I*(y:ℂ)) t).re := by
  -- The lower coefficient is a proved minimum of the original normalized density, independent of t and y.
  obtain ⟨m,hm,hmin⟩ := betaDensityCoefficient_lower ha hA
  have hg : 0<gamma a := by linarith [(parameters ha).1]
  let c : ℝ := m/(2*gamma a)*Real.exp (-2)
  refine ⟨c,max 1 (2/A),by dsimp [c]; positivity,le_max_left _ _,fun y hy t ht => ?_⟩
  have hy1 : 1≤y := (le_max_left _ _).trans hy
  have hyp : 0<y := lt_of_lt_of_le zero_lt_one hy1
  have hcutA : 1/y≤A/2 := by
    have hh := (div_le_iff₀ hA.1).mp ((le_max_right _ _).trans hy)
    apply (div_le_iff₀ hyp).mpr
    nlinarith
  have hcut : 0<1/y := one_div_pos.mpr hyp
  have hcutt : 1/y≤t := by linarith [ht.1,hcutA,hA.1]
  have ht' : t∈Ioo (0:ℝ) 1 := ⟨hA.1.trans_le ht.1,by linarith [ht.2]⟩
  let P : ℝ := (betaNormalization (gamma a))⁻¹*(Real.sin (Real.pi*t)/Real.pi)^(1-gamma a)
  let G : ℝ → ℝ := fun s => P*(sineWeight (gamma a) t s*Real.cosh ((t-2*s)*y))
  let L : ℝ → ℝ := fun s => (m/2*Real.exp (t*y-2))*s^(gamma a-1)
  have hP : 0<P := mul_pos (inv_pos.mpr (betaNormalization_pos hg))
    (Real.rpow_pos_of_pos (div_pos (sine_pos ht') Real.pi_pos) _)
  have hC : ContinuousOn (fun s : ℝ => Real.cosh ((t-2*s)*y)) (uIcc (0:ℝ) t) := by fun_prop
  have hGI : IntervalIntegrable G volume 0 t :=
    ((sineWeight_integrable hg ht').mul_continuousOn hC).const_mul P
  have hprefix : uIcc (0:ℝ) (1/y) ⊆ uIcc (0:ℝ) t := by
    rw [uIcc_of_le hcut.le,uIcc_of_le ht'.1.le]
    exact Icc_subset_Icc le_rfl hcutt
  have hLI : IntervalIntegrable L volume 0 (1/y) :=
    (intervalIntegral.intervalIntegrable_rpow' (show -1<gamma a-1 by linarith)).const_mul _
  have hpoint (s : ℝ) (hs : s∈Ioo (0:ℝ) (1/y)) : L s≤G s := by
    have hst : s∈Ioo (0:ℝ) t := ⟨hs.1,hs.2.trans_le hcutt⟩
    have hcoef := hmin t ht s ⟨hs.1.le,hs.2.le.trans hcutA⟩
    have hcosh : Real.exp (t*y-2)/2≤Real.cosh ((t-2*s)*y) := by
      have hsy := (le_div_iff₀ hyp).mp hs.2.le
      have he := Real.exp_le_exp.mpr (show t*y-2≤(t-2*s)*y by nlinarith)
      rw [Real.cosh_eq]
      linarith [Real.exp_pos (-((t-2*s)*y))]
    have hGval : G s=s^(gamma a-1)*betaDensityCoefficient a (t,s)*Real.cosh ((t-2*s)*y) := by
      dsimp [G,P]
      rw [← mul_assoc,betaDensityCoefficient_identity a ht' hst]
    have hpow := Real.rpow_nonneg hs.1.le (gamma a-1)
    have hcoef0 : 0≤betaDensityCoefficient a (t,s) := hm.le.trans hcoef
    calc
      _ = (s^(gamma a-1)*m)*(Real.exp (t*y-2)/2) := by dsimp [L]; ring
      _ ≤ s^(gamma a-1)*betaDensityCoefficient a (t,s)*Real.cosh ((t-2*s)*y) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hcoef hpow) hcosh (by positivity) (mul_nonneg hpow hcoef0)
      _ = _ := hGval.symm
  have hcompare := intervalIntegral.integral_mono_on_of_le_Ioo hcut.le hLI
    (hGI.mono_set hprefix) hpoint
  have hGnonneg : ∀ s∈Icc (0:ℝ) t,0≤G s := fun s hs =>
    mul_nonneg hP.le (mul_nonneg (sineWeight_nonneg _ ht' hs) (Real.cosh_pos _).le)
  have hrestrict := intervalIntegral.integral_mono_interval (a := 0) (b := 1/y)
    (c := 0) (d := t) le_rfl hcut.le hcutt
      (ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => hGnonneg s ⟨hs.1.le,hs.2⟩) hGI
  have hpower : (∫ s in (0:ℝ)..(1/y),s^(gamma a-1))=y^(-gamma a)/gamma a := by
    rw [integral_rpow (Or.inl (show -1<gamma a-1 by linarith)),
      show gamma a-1+1=gamma a by ring,Real.zero_rpow hg.ne',sub_zero,
      one_div,← Real.rpow_neg_eq_inv_rpow]
  have hvalue : (∫ s in (0:ℝ)..(1/y),L s)=c*Real.exp (t*y)*y^(-gamma a) := by
    rw [show L=(fun s => (m/2*Real.exp (t*y-2))*s^(gamma a-1)) from rfl,
      intervalIntegral.integral_const_mul,hpower]
    dsimp [c]
    rw [show t*y-2=t*y+(-2) by ring,Real.exp_add]
    ring
  have hwave : (wave a (Complex.I*(y:ℂ)) t).re=∫ s in (0:ℝ)..t,G s := by
    rw [wave_beta_integral ha _ ⟨ht'.1.le,ht'.2⟩,betaWave_imaginary,Complex.ofReal_re]
    exact (intervalIntegral.integral_const_mul P _).symm
  rw [← hvalue,hwave]
  exact hcompare.trans hrestrict

/-- The actual shifted negative-energy solution has the article's uniform matching lower bound away from its selected singular endpoint.
Use: supplies the original f(t,c_0-y^2) denominator estimate in Proposition C.2, rather than a bound for an auxiliary wave.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Proof: specialize the proved wave lower bound using the exact genuine shifted negative-energy frequency identity. -/
theorem solution_negative_lower {a A : ℝ} (ha : -1<a) (hA : A∈Ioc (0:ℝ) (1/2)) :
    ∃ c Y : ℝ,0<c ∧ 1≤Y ∧ ∀ y : ℝ,Y≤y → ∀ t∈Icc A (1/2),
      c*Real.exp (t*y)*y^(-gamma a)≤
        (solution a ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ) t).re := by
  simpa only [solution_negative_eq_wave] using wave_imaginary_lower ha hA

end
end jacobi.Reference
