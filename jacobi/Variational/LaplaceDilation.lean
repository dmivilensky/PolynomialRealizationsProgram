import jacobi.Variational.SecondMoment
import jacobi.Variational.DilationMoments

/-!
Article: jacobi, Appendix D.1 (strict concentration gain).
The exponential pairing has a strictly positive linear concentration gain
for every nonzero nonnegative L1 source. The coefficient is an actual
absolutely convergent double integral; it is never assumed positive.
Source: exp(v)>=1+v and the nullity of the diagonal in the Lebesgue plane.
Use: the same strict comparison treats G_2 and the top-eigenvector Rayleigh pairing.
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Real Filter Set
set_option backward.isDefEq.respectTransparency false

/-- Exponential pairing of a source at concentration scale t and kernel rate a.
Use: the same strict comparison treats G_2 and the top-eigenvector Rayleigh pairing.
Article: jacobi, Appendix D.1 (strict concentration gain).
-/
def laplacePair (j : ℝ → ℝ) (a t : ℝ) : ℝ :=
  ∫ z : ℝ × ℝ,j z.1*j z.2*exp (-(a*|z.1-z.2|)/t) ∂volume.prod volume

/-- The exact nonnegative first-order concentration coefficient of the pairing.
Use: supplies the proved strictly positive constant in local spectral dilation.
Article: jacobi, Appendix D.1 (strict concentration gain).
-/
def laplaceGain (j : ℝ → ℝ) (a : ℝ) : ℝ :=
  ∫ z : ℝ × ℝ,j z.1*j z.2*((a*|z.1-z.2|)*exp (-(a*|z.1-z.2|))) ∂volume.prod volume

/-- All scaled exponential pairings are absolutely integrable.
Use: licenses subtraction, comparison and the first-order gain estimate.
Article: jacobi, Appendix D.1 (strict concentration gain).
Proof: the nonnegative-rate kernel is bounded by one. -/
theorem laplace_integrable {j : ℝ → ℝ} (hj : Integrable j) (hm : Measurable j)
    {a t : ℝ} (ha : 0≤a) (ht : 0<t) :
    Integrable (fun z : ℝ × ℝ => j z.1*j z.2*exp (-(a*|z.1-z.2|)/t)) (volume.prod volume) := by
  apply (hj.abs.mul_prod hj.abs).mono'
  · fun_prop
  · exact Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_of_pos (exp_pos _)]
      exact mul_le_of_le_one_right (by positivity)
        (exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
          (neg_nonpos.mpr (mul_nonneg ha (abs_nonneg _))) ht.le))

/-- The concentration coefficient is also absolutely convergent.
Use: the strict gain is a genuine finite integral even without a first spatial moment of j.
Article: jacobi, Appendix D.1 (strict concentration gain).
Proof: r exp(-r)<=exp(-1)<=1, so the same independent L1 product dominates it. -/
theorem laplaceGain_integrable {j : ℝ → ℝ} (hj : Integrable j) (hm : Measurable j)
    {a : ℝ} (ha : 0≤a) :
    Integrable (fun z : ℝ × ℝ => j z.1*j z.2*((a*|z.1-z.2|)*exp (-(a*|z.1-z.2|))))
      (volume.prod volume) := by
  apply (hj.abs.mul_prod hj.abs).mono'
  · fun_prop
  · exact Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_of_nonneg (by positivity :
        0≤(a*|z.1-z.2|)*exp (-(a*|z.1-z.2|)))]
      exact mul_le_of_le_one_right (by positivity)
        ((mul_exp_neg_le_exp_neg_one _).trans (exp_le_one_iff.mpr (by norm_num)))

/-- A nonzero nonnegative integrable source has a strictly positive concentration coefficient.
Use: discharges the positivity premise in the G_2 and top spectral regularity directions.
Article: jacobi, Appendix D.1 (strict concentration gain).
Proof: if the coefficient vanished, its nonnegative integrand would vanish
a.e. Off the null diagonal the distance and exponential are positive, so
the product j(x)j(y) would vanish a.e., contradicting its positive product mass. -/
theorem laplaceGain_pos {j : ℝ → ℝ} (hj : Integrable j) (hm : Measurable j)
    (hn : ∀ x,0≤j x) (hp : 0<∫ x,j x) {a : ℝ} (ha : 0<a) : 0<laplaceGain j a := by
  -- Only the diagonal could annihilate the strictly positive kernel weight.
  have hi := laplaceGain_integrable hj hm ha.le
  have hnon : ∀ z : ℝ × ℝ,0≤j z.1*j z.2*((a*|z.1-z.2|)*exp (-(a*|z.1-z.2|))) :=
    fun z => mul_nonneg (mul_nonneg (hn _) (hn _)) (by positivity)
  have hzero_diag : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume,z.1≠z.2 := by
    apply (Measure.ae_prod_iff_ae_ae
      (isClosed_eq continuous_fst continuous_snd).measurableSet.compl).mpr
    exact Eventually.of_forall fun x => by simp [ae_iff]
  apply lt_of_le_of_ne (integral_nonneg hnon)
  intro hzero
  have hz := (integral_eq_zero_iff_of_nonneg hnon hi).mp hzero.symm
  have hprod : (fun z : ℝ × ℝ => j z.1*j z.2)=ᵐ[volume.prod volume] 0 := by
    filter_upwards [hz,hzero_diag] with z hz hne
    have hw : 0<(a*|z.1-z.2|)*exp (-(a*|z.1-z.2|)) :=
      mul_pos (mul_pos ha (abs_pos.mpr (sub_ne_zero.mpr hne))) (exp_pos _)
    exact (mul_eq_zero.mp hz).resolve_right hw.ne'
  have he : (∫ x,j x)*(∫ x,j x)=0 := by
    rw [← integral_prod_mul,integral_congr_ae hprod]
    simp only [Pi.zero_apply,integral_zero]
  nlinarith

/-- The literal exponential kernel has the global one-sided tangent gain in concentration.
Use: converts the positive coefficient to a local linear spectral gain.
Article: jacobi, Appendix D.1 (strict concentration gain).
Proof: factor exp(-r) and apply exp(v)>=1+v to v=r(1-1/t). -/
theorem exp_dilation_lower {r t : ℝ} (ht : 0<t) :
    exp (-r)+(1-1/t)*(r*exp (-r))≤exp (-r/t) := by
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (r*(1-1/t))) (exp_pos (-r)).le
  rw [← exp_add] at h
  have he : -r+r*(1-1/t)= -r/t := by field_simp; ring
  rw [he] at h
  nlinarith

/-- The actual double integral gains at least its positive tangent coefficient.
Use: the final local G_2 and top-eigenvalue dilation estimates.
Article: jacobi, Appendix D.1 (strict concentration gain).
Proof: integrate the scalar exponential inequality against j(x)j(y)>=0. -/
theorem laplace_dilation_lower {j : ℝ → ℝ} (hj : Integrable j) (hm : Measurable j)
    (hn : ∀ x,0≤j x) {a t : ℝ} (ha : 0≤a) (ht : 0<t) :
    laplacePair j a 1+(1-1/t)*laplaceGain j a≤laplacePair j a t := by
  -- Both the tangent and the perturbed pairing have independent integrable majorants.
  have hi := laplace_integrable hj hm ha zero_lt_one
  have hg := laplaceGain_integrable hj hm ha
  have hb (z : ℝ × ℝ) :
      j z.1*j z.2*exp (-(a*|z.1-z.2|)/1)+
        (1-1/t)*(j z.1*j z.2*((a*|z.1-z.2|)*exp (-(a*|z.1-z.2|))))≤
      j z.1*j z.2*exp (-(a*|z.1-z.2|)/t) := by
    have h := mul_le_mul_of_nonneg_left (exp_dilation_lower (r := a*|z.1-z.2|) ht)
      (mul_nonneg (hn z.1) (hn z.2))
    simp only [div_one]
    nlinarith
  have h := integral_mono (hi.add (hg.const_mul _)) (laplace_integrable hj hm ha ht) hb
  rw [integral_add' hi (hg.const_mul _),integral_const_mul] at h
  exact h

end
end jacobi.Variational
