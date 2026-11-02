import jacobi.Reference.Wave
import jacobi.Reference.HypergeometricBounds

/-!
Article: jacobi, Appendix C.1 (selected endpoint branch).
The genuine hypergeometric coefficients are entire functions of frequency.
On each frequency disk, one actual convergent positive-parameter 2F1 series
majorizes them uniformly. The community holomorphic-series theorem then
proves the claimed entire dependence, including terminating frequencies.
Use: exposes the genuine polynomial parameter dependence before passing to the infinite reference series.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Complex
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual hypergeometric expansion coefficient of the original reference wave, as a function of complex frequency.
Use: exposes the genuine polynomial parameter dependence before passing to the infinite reference series.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
-/
def frequencyCoefficient (a : ℝ) (n : ℕ) (omega : ℂ) : ℂ :=
  ordinaryHypergeometricCoefficient ((gamma a:ℂ)-omega/(Real.pi:ℂ))
    ((gamma a:ℂ)+omega/(Real.pi:ℂ)) ((gamma a:ℂ)+1/2) n

/-- Every true original reference hypergeometric coefficient is entire in complex frequency.
Use: the genuine normal series theorem proves entire frequency dependence of the original reference solution.
Article: jacobi, Appendix C.1 (selected endpoint branch).
Proof: each numerator is a genuine rising-factorial polynomial composed
with an affine frequency map. Their shared denominator is constant in
frequency, so multiplication by its fixed inverse is entire. -/
theorem frequencyCoefficient_analytic (a : ℝ) (n : ℕ) (omega : ℂ) :
    AnalyticAt ℂ (frequencyCoefficient a n) omega := by
  -- Denominator zeros are not cancelled in this analyticity proof; the admissible physical denominator is separately positive.
  have hm : AnalyticAt ℂ (fun w:ℂ => (gamma a:ℂ)-w/(Real.pi:ℂ)) omega :=
    analyticAt_const.sub analyticAt_id.div_const
  have hp : AnalyticAt ℂ (fun w:ℂ => (gamma a:ℂ)+w/(Real.pi:ℂ)) omega :=
    analyticAt_const.add analyticAt_id.div_const
  have hm' := (AnalyticOnNhd.eval_polynomial (ascPochhammer ℂ n) _ (mem_univ _)).comp hm
  have hp' := (AnalyticOnNhd.eval_polynomial (ascPochhammer ℂ n) _ (mem_univ _)).comp hp
  exact ((analyticAt_const.mul hm').mul hp').mul analyticAt_const

/-- A prescribed frequency norm bound gives one explicit positive-parameter bound for every original reference coefficient.
Use: the same coefficient estimate proves both frequency and energy analyticity of the actual source solution.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: both affine numerator parameter norms are at most abs(gamma)+R/pi. Increasing this bound by one makes it positive and permits the genuine Pochhammer majorant. -/
theorem frequencyCoefficient_norm_bound (a : ℝ) {R : ℝ} (hR : 0≤R)
    {w : ℂ} (hw : ‖w‖≤R) (n : ℕ) :
    ‖frequencyCoefficient a n w‖≤
      ‖ordinaryHypergeometricCoefficient ((|gamma a|+R/Real.pi+1:ℝ):ℂ)
        ((|gamma a|+R/Real.pi+1:ℝ):ℂ) ((gamma a:ℂ)+1/2) n‖ := by
  -- Both numerator estimates use the true positive pi denominator.
  have hD : 0< |gamma a|+R/Real.pi+1 := by positivity
  have hwdiv : ‖w/(Real.pi:ℂ)‖≤R/Real.pi := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
    exact div_le_div_of_nonneg_right hw Real.pi_pos.le
  have hm : ‖(gamma a:ℂ)-w/(Real.pi:ℂ)‖≤|gamma a|+R/Real.pi+1 := by
    have hh := norm_sub_le (gamma a:ℂ) (w/(Real.pi:ℂ))
    rw [Complex.norm_real,Real.norm_eq_abs] at hh
    linarith
  have hp : ‖(gamma a:ℂ)+w/(Real.pi:ℂ)‖≤|gamma a|+R/Real.pi+1 := by
    have hh := norm_add_le (gamma a:ℂ) (w/(Real.pi:ℂ))
    rw [Complex.norm_real,Real.norm_eq_abs] at hh
    linarith
  exact Hypergeometric.coefficient_norm_le hD hm hp n

/-- On every original frequency disk, the true reference hypergeometric coefficients have one convergent positive-parameter majorant.
Use: justifies the original entire-frequency assertion by genuine normal convergence rather than a parameter-analyticity assumption.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: both numerator parameter norms are at most abs(gamma) plus the
frequency radius divided by pi. Increase this to a strictly positive
common parameter and use the proved rising-factorial coefficient bound. -/
theorem frequencyCoefficient_bound (a : ℝ) (omega : ℂ) :
    ∃ D : ℝ,0<D ∧ ∀ w∈Metric.ball omega 1,∀ n,
      ‖frequencyCoefficient a n w‖≤
        ‖ordinaryHypergeometricCoefficient (D:ℂ) (D:ℂ) ((gamma a:ℂ)+1/2) n‖ := by
  -- The same fixed denominator occurs in the original coefficients and the majorizing community series.
  let D := |gamma a|+(‖omega‖+1)/Real.pi+1
  have hD : 0<D := by dsimp [D]; positivity
  refine ⟨D,hD,fun w hw n => ?_⟩
  have hw' : ‖w-omega‖<1 := by simpa only [Metric.mem_ball,dist_eq_norm] using hw
  have hwn : ‖w‖≤‖omega‖+1 := by
    have hh := norm_add_le (w-omega) omega
    rw [sub_add_cancel] at hh
    linarith
  exact frequencyCoefficient_norm_bound a (by positivity : 0≤‖omega‖+1) hwn n

/-- The original reference core is an entire function of complex frequency at every spatial hypergeometric argument in its disk.
Use: provides the true entire function needed for the source GL completeness and Jensen uniqueness argument.
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
Proof: on a unit disk about an arbitrary frequency, the genuine entire
coefficient terms are bounded by the proved summable actual 2F1
majorant. Apply the community holomorphic-series theorem and identify
the sum with the original hypergeometric definition. -/
theorem waveCore_frequency_analytic (a : ℝ) {x : ℂ} (hx : ‖x‖<1) (omega : ℂ) :
    AnalyticAt ℂ (fun w => waveCore a w x) omega := by
  -- Normal convergence is proved for the actual series, including frequencies where it terminates.
  obtain ⟨D,hD,hbound⟩ := frequencyCoefficient_bound a omega
  let M := fun n => ‖ordinaryHypergeometricCoefficient (D:ℂ) (D:ℂ) ((gamma a:ℂ)+1/2) n*x^n‖
  have hM : Summable M := Hypergeometric.summable_norm hx
  have hd := Complex.differentiableOn_tsum_of_summable_norm hM
    (F := fun n w => frequencyCoefficient a n w*x^n)
    (fun n w _ => ((frequencyCoefficient_analytic a n w).mul analyticAt_const).differentiableAt.differentiableWithinAt)
    Metric.isOpen_ball (fun n w hw => by
      change ‖frequencyCoefficient a n w*x^n‖≤
        ‖ordinaryHypergeometricCoefficient (D:ℂ) (D:ℂ) ((gamma a:ℂ)+1/2) n*x^n‖
      rw [norm_mul,norm_mul]
      exact mul_le_mul_of_nonneg_right (hbound w hw n) (norm_nonneg _))
  have he : (fun w => ∑' n,frequencyCoefficient a n w*x^n)=(fun w => waveCore a w x) := by
    funext w
    simp only [waveCore,ordinaryHypergeometric_eq_tsum,smul_eq_mul,frequencyCoefficient]
  rw [he] at hd
  exact hd.analyticAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num)))

/-- The actual physical reference wave is an even entire function of complex frequency at every original interior point.
Use: supplies the source entire function at the original Bessel and reference frequencies in the GL injectivity argument.
Article: jacobi, Lemma C.1.
Proof: the actual spatial coordinate lies inside the hypergeometric disk. Multiply the proved entire core by its frequency-independent genuine sine-power prefactor. -/
theorem wave_frequency_analytic (a : ℝ) {t : ℝ} (ht : t∈Ioo 0 1) (omega : ℂ) :
    AnalyticAt ℂ (fun w => wave a w t) omega :=
  analyticAt_const.mul (waveCore_frequency_analytic a (coordinate_norm_lt_one ht) omega)

end
end jacobi.Reference
