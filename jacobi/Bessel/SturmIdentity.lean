import jacobi.Bessel.Zeros
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
Article: jacobi, Theorem 2.1.
The regular singular endpoint has a genuine vanishing Green boundary
term. Weighted integration by parts proves a complex Rayleigh identity,
which will identify every Bessel zero as a positive real eigenvalue.
Source: the classical Sturm--Liouville Green identity for
(t^(alpha+1)*y')'+(z/4)*t^alpha*y=0.
Use: the Bessel Green identity divides only by the genuine positive spectral norm.
-/
namespace jacobi.Bessel
noncomputable section
open Complex Real Set MeasureTheory Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- A continuous complex function nonzero at zero has a strictly positive weighted square integral.
Use: the Bessel Green identity divides only by the genuine positive spectral norm.
Article: jacobi, Theorem 2.1.
Proof: t^alpha is integrable and positive on (0,1). Continuity gives a
nonzero function on a small initial interval; that positive-measure
interval lies in the support of the nonnegative weighted integrand. -/
theorem weighted_norm_integral_pos {a : ℝ} (ha : -1<a) {y : ℝ → ℂ}
    (hy : Continuous y) (h0 : y 0≠0) :
    0<∫ t in (0:ℝ)..1,‖y t‖^2*t^a := by
  -- The possibly singular endpoint power is integrated before positivity is asserted.
  have hi : IntervalIntegrable (fun t => ‖y t‖^2*t^a) volume 0 1 :=
    (intervalIntegral.intervalIntegrable_rpow' ha).continuousOn_mul (hy.norm.pow 2).continuousOn
  obtain ⟨ε,hε,hεn⟩ := Metric.mem_nhds_iff.mp (hy.continuousAt.eventually_ne h0)
  let δ := min ε 1/2
  have hδ : 0<δ := half_pos (lt_min hε (by norm_num : (0:ℝ)<1))
  have hδe : δ<ε := by dsimp [δ]; have := min_le_left ε 1; linarith
  have hδ1 : δ≤1 := by dsimp [δ]; have := min_le_right ε 1; linarith
  have hnon : 0≤ᵐ[volume.restrict (uIoc (0:ℝ) 1)] (fun t => ‖y t‖^2*t^a) := by
    rw [uIoc_of_le (by norm_num : (0:ℝ)≤1)]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg ht.1.le _)
  apply (intervalIntegral.integral_pos_iff_support_of_nonneg_ae' hnon hi).mpr
  refine ⟨by norm_num,((MeasureTheory.Measure.measure_Ioo_pos volume).mpr hδ).trans_le (measure_mono ?_)⟩
  intro t ht
  have hyn : y t≠0 := hεn (by
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos ht.1]
    exact ht.2.trans hδe)
  exact ⟨(mul_pos (sq_pos_of_pos (norm_pos_iff.mpr hyn)) (Real.rpow_pos_of_pos ht.1 _)).ne',
    ⟨ht.1,ht.2.le.trans hδ1⟩⟩

/-- Weighted Green integration by parts holds at the regular singular Bessel endpoint with its true zero boundary term.
Use: proves real positive location of the actual normalized Bessel zeros.
Article: jacobi, Theorem 2.1.
Proof: differentiate t^(alpha+1)*conj(y)*y' on (0,1), using the
actual differential equation. Its two terms are integrable. The primitive
is continuous at zero because alpha+1>0 and vanishes there; y(1)=0
removes the other boundary. Apply the genuine complex-valued fundamental theorem. -/
theorem weighted_green_identity {a : ℝ} {z : ℂ} (ha : -1<a)
    (y dy ddy : ℝ → ℂ) (hy : Continuous y) (hdy : Continuous dy)
    (hd : ∀ t∈Ioo (0:ℝ) 1,HasDerivAt y (dy t) t)
    (hdd : ∀ t∈Ioo (0:ℝ) 1,HasDerivAt dy (ddy t) t)
    (heq : ∀ t∈Ioo (0:ℝ) 1,(t:ℂ)*ddy t+(a+1:ℂ)*dy t+(z/4)*y t=0)
    (h1 : y 1=0) :
    (4:ℂ)*(∫ t in (0:ℝ)..1,‖dy t‖^2*t^(a+1))=
      z*(∫ t in (0:ℝ)..1,‖y t‖^2*t^a) := by
  -- Every endpoint and integrability fact is proved for the actual regular singular power.
  have hap : 0<a+1 := by linarith
  have hi0 : IntervalIntegrable (fun t => ‖y t‖^2*t^a) volume 0 1 :=
    (intervalIntegral.intervalIntegrable_rpow' ha).continuousOn_mul (hy.norm.pow 2).continuousOn
  have hi1 : IntervalIntegrable (fun t => ‖dy t‖^2*t^(a+1)) volume 0 1 :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1<a+1)).continuousOn_mul
      (hdy.norm.pow 2).continuousOn
  have hi0C : IntervalIntegrable (fun t => ((‖y t‖^2*t^a:ℝ):ℂ)) volume 0 1 := by
    constructor
    · exact hi0.1.ofReal
    · exact hi0.2.ofReal
  have hi1C : IntervalIntegrable (fun t => ((‖dy t‖^2*t^(a+1):ℝ):ℂ)) volume 0 1 := by
    constructor
    · exact hi1.1.ofReal
    · exact hi1.2.ofReal
  let f := fun t : ℝ => ((t^(a+1):ℝ):ℂ)*star (y t)*dy t
  have hf : ContinuousOn f (Icc (0:ℝ) 1) :=
    (((Complex.continuous_ofReal.comp (Real.continuous_rpow_const hap.le)).mul hy.star).mul hdy).continuousOn
  have hdF (t : ℝ) (ht : t∈Ioo (0:ℝ) 1) :
      HasDerivAt f
        (((‖dy t‖^2*t^(a+1):ℝ):ℂ)-(z/4)*((‖y t‖^2*t^a:ℝ):ℂ)) t := by
    have hp : HasDerivAt (fun x : ℝ => x^(a+1)) ((a+1)*t^a) t := by
      convert ((hasDerivAt_id t).rpow_const (p := a+1) (Or.inl ht.1.ne')) using 1 <;>
        simp only [id_eq,one_mul,add_sub_cancel_right]
    have h := ((hp.ofReal_comp.mul (hd t ht).star).mul (hdd t ht))
    convert h using 1
    dsimp only [id_eq,Pi.mul_apply]
    rw [Real.rpow_add_one ht.1.ne']
    push_cast
    have hN : star (dy t)*dy t=(‖dy t‖:ℂ)^2 := Complex.conj_mul' (dy t)
    have hY : star (y t)*y t=(‖y t‖:ℂ)^2 := Complex.conj_mul' (y t)
    linear_combination -((t^a:ℝ):ℂ)*star (y t)*(heq t ht)-
      ((t^a:ℝ):ℂ)*(t:ℂ)*hN+(z/4)*((t^a:ℝ):ℂ)*hY
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by norm_num : (0:ℝ)≤1) hf hdF (hi1C.sub (hi0C.const_mul (z/4)))
  rw [intervalIntegral.integral_sub hi1C (hi0C.const_mul (z/4)),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_ofReal,
    intervalIntegral.integral_ofReal] at hFTC
  have hzero : f 1-f 0=0 := by simp [f,h1,Real.zero_rpow hap.ne']
  rw [hzero] at hFTC
  linear_combination 4*hFTC

end
end jacobi.Bessel
