import jacobi.Reference.NegativeSlope
import jacobi.Reference.SolutionReality
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
The original negative-energy logarithmic derivative is y+O(1/y).
The actual potential forcing is integrated on [1/4,1/2], and the proved
positive lower bound for the original reference wave fixes its denominator.
Every bound is for the already constructed wave and its genuine slope.
Source: variation of constants and exponential decay of polynomial factors.
Use: bounds the inhomogeneous term in negative_midpoint_quotient_bound.
-/
namespace jacobi.Reference
noncomputable section
open Real Set MeasureTheory Filter _root_.Complex
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual potential forcing in the reference integrating-factor formula has the precise uniform negative-energy bound needed at the midpoint.
Use: bounds the inhomogeneous term in negative_midpoint_quotient_bound.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: the genuine inverse-square potential is bounded by a fixed
constant on [1/4,1/2]. The actual wave bound supplies y^(-gamma)*exp(y*s),
so the weighted forcing is at most a fixed multiple of
y^(-gamma)*exp(2*y*s). Its genuine exponential integral is at most exp(y)/y. -/
theorem negative_forcing_bound {a : ℝ} (ha : -1<a) :
    ∃ C : ℝ,0<C ∧ ∀ y : ℝ,1≤y →
      |∫ s in (1/4:ℝ)..(1/2:ℝ),Real.exp (y*s)*singularPotential a s*(wave a (Complex.I*(y:ℂ)) s).re|≤
        C*y^(-gamma a)*Real.exp y/y := by
  -- Both majorants come from the original potential and wave; no quotient asymptotic is assumed.
  obtain ⟨A,hA,hQ⟩ := singularPotential_bound a
  obtain ⟨B,hB,hf⟩ := wave_uniform_high_frequency ha
  let C := 16*A*B
  refine ⟨C,by dsimp [C]; positivity,fun y hy => ?_⟩
  have hyp : 0<y := lt_of_lt_of_le zero_lt_one hy
  have hn : ‖Complex.I*(y:ℂ)‖=y := by
    rw [norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hyp]
  have hpoint (s : ℝ) (hs : s∈Ioc (1/4:ℝ) (1/2)) :
      ‖Real.exp (y*s)*singularPotential a s*(wave a (Complex.I*(y:ℂ)) s).re‖≤
        (C*y^(-gamma a))*Real.exp ((2*y)*s) := by
    have hsp : 0<s := by linarith [hs.1]
    have hP : |singularPotential a s|≤16*A := by
      apply (hQ s ⟨hsp,hs.2⟩).trans
      apply (div_le_iff₀ (sq_pos_of_pos hsp)).mpr
      nlinarith [sq_nonneg (s-1/4),mul_nonneg hA.le (show 0≤s-1/4 by linarith [hs.1])]
    have hb := hf (Complex.I*(y:ℂ)) (by rw [hn]; exact hy) s ⟨hsp.le,hs.2⟩
    simp only [hn,Complex.mul_im,Complex.I_re,Complex.I_im,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,one_mul,zero_add,abs_of_pos hyp] at hb
    have hr := (Complex.abs_re_le_norm _).trans hb
    rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (y*s)*(16*A)*(B*y^(-gamma a)*Real.exp (s*y)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hP (Real.exp_pos _).le) hr (abs_nonneg _) (by positivity)
      _ = (C*y^(-gamma a))*(Real.exp (y*s)*Real.exp (y*s)) := by
        rw [mul_comm s y]
        dsimp [C]
        ring
      _ = _ := by rw [← Real.exp_add,show y*s+y*s=(2*y)*s by ring_nf]
  have hmajorant : IntervalIntegrable (fun s : ℝ => (C*y^(-gamma a))*Real.exp ((2*y)*s))
      volume (1/4) (1/2) := by apply Continuous.intervalIntegrable; fun_prop
  have hb := intervalIntegral.norm_integral_le_of_norm_le (by norm_num : (1/4:ℝ)≤1/2)
    (Eventually.of_forall fun s hs => hpoint s hs) hmajorant
  have he : (∫ s in (1/4:ℝ)..(1/2:ℝ),Real.exp ((2*y)*s))=
      (Real.exp y-Real.exp (y/2))/(2*y) := by
    rw [intervalIntegral.integral_comp_mul_left Real.exp (show 2*y≠0 by positivity),integral_exp]
    simp only [smul_eq_mul]
    rw [show (2*y)*(1/2:ℝ)=y by ring_nf,show (2*y)*(1/4:ℝ)=y/2 by ring_nf]
    ring_nf
  have he' : (Real.exp y-Real.exp (y/2))/(2*y)≤Real.exp y/y := by
    apply (div_le_div_iff₀ (by positivity : 0<2*y) hyp).mpr
    nlinarith [Real.exp_pos y,Real.exp_pos (y/2)]
  rw [Real.norm_eq_abs,intervalIntegral.integral_const_mul,he] at hb
  exact hb.trans ((mul_le_mul_of_nonneg_left he' (by dsimp [C]; positivity)).trans_eq (by ring_nf))

/-- The actual reference midpoint logarithmic derivative differs from y by one exponentially decaying initial term and one inverse-y forcing term.
Use: negative_midpoint_asymptotic converts this fully discharged estimate to the article's O(1/y) remainder.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: the genuine integrating-factor identity bounds the midpoint
slope defect by the proved quarter-point state and actual potential
forcing. Divide by the original positive lower bound for f(1/2),
then cancel the exact powers and exponential factors. -/
theorem negative_midpoint_quotient_bound {a : ℝ} (ha : -1<a) :
    ∃ B C Y : ℝ,0<B ∧ 0<C ∧ 1≤Y ∧ ∀ y : ℝ,Y≤y →
      |(waveSlope a (Complex.I*(y:ℂ)) (1/2)).re/(wave a (Complex.I*(y:ℂ)) (1/2)).re-y|≤
        B*y*Real.exp (-y/2)+C/y := by
  -- The denominator lower bound is proved for the same original wave used by the exact integrating-factor identity.
  obtain ⟨B,hB,hquarter⟩ := negativeSlopeDefect_quarter_bound ha
  obtain ⟨K,hK,hforcing⟩ := negative_forcing_bound ha
  obtain ⟨c,Y,hc,hY,hlower⟩ := wave_imaginary_lower ha (A := (1/2:ℝ)) (by norm_num)
  refine ⟨B/c,K/c,Y,by positivity,by positivity,hY,fun y hy => ?_⟩
  have hy1 : 1≤y := hY.trans hy
  have hyp : 0<y := lt_of_lt_of_le zero_lt_one hy1
  have hp := Real.rpow_pos_of_pos hyp (-gamma a)
  have hf := wave_imaginary_pos ha y (t := (1/2:ℝ)) (by norm_num)
  have hl := hlower y hy (1/2:ℝ) (by norm_num)
  rw [show (1/2:ℝ)*y=y/2 by ring] at hl
  have hl' : c*y^(-gamma a)*Real.exp (y/2)≤(wave a (Complex.I*(y:ℂ)) (1/2)).re := by nlinarith [hl]
  have hI := negativeSlopeDefect_integral ha y
  have hD := hquarter y hy1
  have hJ := hforcing y hy1
  have hsum : Real.exp (y/2)*negativeSlopeDefect a y (1/2)=
      Real.exp (y/4)*negativeSlopeDefect a y (1/4)+
        (∫ s in (1/4:ℝ)..(1/2:ℝ),Real.exp (y*s)*singularPotential a s*(wave a (Complex.I*(y:ℂ)) s).re) := by linarith
  have heq : Real.exp (y/4)*Real.exp (y/4)=Real.exp (y/2) := by
    rw [← Real.exp_add]; congr 1; ring
  have heq' : Real.exp (y/2)*Real.exp (y/2)=Real.exp y := by
    rw [← Real.exp_add]; congr 1; ring
  have hweighted : |negativeSlopeDefect a y (1/2)| *Real.exp (y/2)≤
      B*y*y^(-gamma a)*Real.exp (y/2)+K*y^(-gamma a)*Real.exp y/y := by
    calc
      _ = |Real.exp (y/2)*negativeSlopeDefect a y (1/2)| := by rw [abs_mul,abs_of_pos (Real.exp_pos _)]; ring
      _ ≤ |Real.exp (y/4)*negativeSlopeDefect a y (1/4)|+
          |∫ s in (1/4:ℝ)..(1/2:ℝ),Real.exp (y*s)*singularPotential a s*(wave a (Complex.I*(y:ℂ)) s).re| := by
            rw [hsum]; exact abs_add_le _ _
      _ ≤ Real.exp (y/4)*(B*y*y^(-gamma a)*Real.exp (y/4))+K*y^(-gamma a)*Real.exp y/y := by
        rw [abs_mul,abs_of_pos (Real.exp_pos _)]
        exact add_le_add (mul_le_mul_of_nonneg_left hD (Real.exp_pos _).le) hJ
      _ = _ := by
        have hh := congrArg (fun e : ℝ => B*y*y^(-gamma a)*e) heq
        linear_combination hh
  let R := B/c*y*Real.exp (-y/2)+(K/c)/y
  have hR : 0≤R := by dsimp [R]; positivity
  have hscale : (R*(c*y^(-gamma a)*Real.exp (y/2)))*Real.exp (y/2)=
      B*y*y^(-gamma a)*Real.exp (y/2)+K*y^(-gamma a)*Real.exp y/y := by
    dsimp [R]
    rw [show -y/2= -(y/2) by ring,Real.exp_neg,← heq']
    field_simp [hc.ne',hyp.ne',(Real.exp_pos (y/2)).ne']
  have hdefect : |negativeSlopeDefect a y (1/2)|≤R*(c*y^(-gamma a)*Real.exp (y/2)) :=
    (mul_le_mul_iff_left₀ (Real.exp_pos (y/2))).mp (hweighted.trans_eq hscale.symm)
  have hquot : (waveSlope a (Complex.I*(y:ℂ)) (1/2)).re/(wave a (Complex.I*(y:ℂ)) (1/2)).re-y=
      negativeSlopeDefect a y (1/2)/(wave a (Complex.I*(y:ℂ)) (1/2)).re := by
    dsimp [negativeSlopeDefect]
    field_simp [hf.ne']
  rw [hquot,abs_div,abs_of_pos hf]
  exact (div_le_iff₀ hf).mpr (hdefect.trans (mul_le_mul_of_nonneg_left hl' hR))

/-- The original midpoint logarithmic derivative has precisely the printed inverse-y remainder at shifted negative energy.
Use: fixes the reference comparison used to identify both transformed midpoint boundary conditions and w(1/2)=0 in Proposition C.2.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Source: exponential decay dominates every fixed real power, as proved in mathlib.
Proof: the proved actual quotient bound has remainder B*y*exp(-y/2)+C/y.
The true limit y^2*exp(-y/2)->0 bounds its first term by B/y beyond a
finite threshold. Combine both terms without any unproved asymptotic premise. -/
theorem negative_midpoint_asymptotic {a : ℝ} (ha : -1<a) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ y : ℝ in atTop,
      |(waveSlope a (Complex.I*(y:ℂ)) (1/2)).re/(wave a (Complex.I*(y:ℂ)) (1/2)).re-y|≤C/y := by
  -- The only asymptotic limit invoked concerns the explicit elementary exponential remainder, not an assumed special-function expansion.
  obtain ⟨B,C,Y,hB,hC,hY,hbound⟩ := negative_midpoint_quotient_bound ha
  have he : Tendsto (fun y : ℝ => y^2*Real.exp (-y/2)) atTop (𝓝 0) := by
    convert tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2:ℝ) (1/2:ℝ) (by norm_num) using 1
    funext y
    rw [Real.rpow_two]
    congr 2
    ring
  have hs := he.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))
  refine ⟨B+C,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop Y,hs] with y hy hexp
  have hyp : 0<y := lt_of_lt_of_le zero_lt_one (hY.trans hy)
  have hsmall : y*Real.exp (-y/2)≤1/y := (le_div_iff₀ hyp).mpr (by nlinarith [hexp.le])
  calc
    _ ≤ B*y*Real.exp (-y/2)+C/y := hbound y hy
    _ ≤ B*(1/y)+C/y := by nlinarith [mul_le_mul_of_nonneg_left hsmall hB.le]
    _ = (B+C)/y := by ring

/-- The genuine spatial slope of the energy-defined reference solution equals the imaginary-frequency slope on the shifted negative axis.
Use: transfers the proved logarithmic derivative asymptotic from the original wave to the exact energy function f(t,c_0-y^2).
Article: jacobi, Proposition C.2.
Proof: the actual solution and wave agree as functions of the spatial variable. Their genuine derivatives are therefore equal by uniqueness of the ordinary derivative. -/
theorem solutionSlope_negative_eq_wave (a y : ℝ) {t : ℝ} (ht : t∈Ioo (0:ℝ) 1) :
    solutionSlope a ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ) t=
      waveSlope a (Complex.I*(y:ℂ)) t := by
  have he : solution a ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ)=wave a (Complex.I*(y:ℂ)) :=
    funext (solution_negative_eq_wave a y)
  have hd := solution_hasDerivAt a ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ) ht
  rw [he] at hd
  exact hd.unique (wave_hasDerivAt a (Complex.I*(y:ℂ)) ht)

/-- The existing energy-defined reference midpoint quotient satisfies the article's full negative-energy asymptotic with its exact inverse-y remainder.
Use: gives the unconditional original b_0(c_0-y^2)/a_0(c_0-y^2) comparison needed to identify the target midpoint conditions in Proposition C.2.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: rewrite the actual energy solution and its genuine slope by their proved negative-frequency identities, then apply negative_midpoint_asymptotic. -/
theorem solution_negative_midpoint_asymptotic {a : ℝ} (ha : -1<a) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ y : ℝ in atTop,
      |(solutionSlope a ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ) (1/2)).re/
        (solution a ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ) (1/2)).re-y|≤C/y := by
  obtain ⟨C,hC,hbound⟩ := negative_midpoint_asymptotic ha
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with y hy
  simpa only [solution_negative_eq_wave,
    solutionSlope_negative_eq_wave a y (by norm_num : (1/2:ℝ)∈Ioo (0:ℝ) 1)] using hy

/-- The genuine spatial derivative of the original solution at every real energy is itself real throughout the physical interior.
Use: expresses the proved real negative-energy quotient bound as the norm bound for the original complex characteristic data.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: the original solution equals the inclusion of its real part as a
function of the spatial variable. Differentiate that true identity
using the continuous real-part map; uniqueness identifies its genuine
complex slope with the inclusion of its actual real part. -/
theorem solutionSlope_real (a E : ℝ) {t : ℝ} (ht : t∈Ioo (0:ℝ) 1) :
    ((solutionSlope a (E:ℂ) t).re:ℂ)=solutionSlope a (E:ℂ) t := by
  -- Reality is differentiated as an equality of actual functions, rather than imposed on an independently named slope.
  have hd := solution_hasDerivAt a (E:ℂ) ht
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hd
  have hc := hr.ofReal_comp
  change HasDerivAt (fun s : ℝ => ((solution a (E:ℂ) s).re:ℂ)) _ t at hc
  have he : (fun s : ℝ => ((solution a (E:ℂ) s).re:ℂ))=solution a (E:ℂ) :=
    funext (solution_real a E)
  rw [he] at hc
  exact hc.unique hd

/-- The original complex midpoint quotient has the exact article remainder at shifted negative energy, measured in the genuine complex norm.
Use: supplies the reference logarithmic derivative comparison in its original complex-energy notation for Proposition C.2.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: the actual reference value and its genuine slope are real at
every real energy. Embed the already proved real quotient bound into
the complex field, where its norm is the same absolute value. -/
theorem solution_negative_midpoint_norm_bound {a : ℝ} (ha : -1<a) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ y : ℝ in atTop,
      ‖solutionSlope a ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ) (1/2)/
        solution a ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ) (1/2)-(y:ℂ)‖≤C/y := by
  obtain ⟨C,hC,hbound⟩ := solution_negative_midpoint_asymptotic ha
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with y hy
  rw [← Real.norm_eq_abs,← Complex.norm_real,Complex.ofReal_sub,Complex.ofReal_div,
    solutionSlope_real a _ (by norm_num : (1/2:ℝ)∈Ioo (0:ℝ) 1),solution_real] at hy
  exact hy

end
end jacobi.Reference
