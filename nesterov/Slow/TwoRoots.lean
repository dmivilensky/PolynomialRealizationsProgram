import nesterov.Slow.Roots
import nesterov.Slow.RootSelection
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-! Both slow roots of the actual characteristic polynomial, with multiplicity.
The deflation argument includes coincident roots at critical damping. -/
namespace nesterov.Slow
noncomputable section
open Polynomial Filter Set
open scoped Topology

/-- A continuous extension of `-log(1-εw)/ε` at `ε=0`. -/
def logCoordinate (ε : ℝ) (w : ℂ) : ℂ :=
  w*dslope Complex.log 1 (1-(ε:ℂ)*w)

theorem logCoordinate_tendsto {A : Type*} {l : Filter A} {e : A→ℝ}
    {w : A→ℂ} {w₀ : ℂ} (he : Tendsto e l (𝓝 0)) (hw : Tendsto w l (𝓝 w₀)) :
    Tendsto (fun a=>logCoordinate (e a) (w a)) l (𝓝 w₀) := by
  have hc : ContinuousAt (dslope Complex.log 1) 1 :=
    continuousAt_dslope_same.mpr (Complex.differentiableAt_log Complex.one_mem_slitPlane)
  have hv : dslope Complex.log 1 1=1 := by
    simpa only [dslope_same,inv_one] using (Complex.hasDerivAt_log Complex.one_mem_slitPlane).deriv
  have he' : Tendsto (fun a=>(e a:ℂ)) l (𝓝 0) := by
    convert (Complex.continuous_ofReal.tendsto 0).comp he using 1
    funext a
    rfl
  have hz : Tendsto (fun a=>1-(e a:ℂ)*w a) l (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (he'.mul hw)
  have ht := hw.mul (hc.tendsto.comp hz)
  rw [hv,mul_one] at ht
  convert ht using 1
  funext a
  rfl

theorem exp_logCoordinate {ε : ℝ} {w : ℂ} (hz : 1-(ε:ℂ)*w≠0) :
    Complex.exp (-(ε:ℂ)*logCoordinate ε w)=1-(ε:ℂ)*w := by
  have hh := sub_smul_dslope Complex.log 1 (1-(ε:ℂ)*w)
  simp only [smul_eq_mul,Complex.log_one,sub_zero] at hh
  have he : -(ε:ℂ)*logCoordinate ε w=Complex.log (1-(ε:ℂ)*w) := by
    rw [←hh]
    unfold logCoordinate
    ring
  rw [he,Complex.exp_log hz]

namespace SecondOrderFamily
variable {θ y : ℝ} (F : SecondOrderFamily θ y)

theorem limitCharacteristic_factor {a : ℂ} (ha : F.limitCharacteristic.eval a=0) :
    F.limitCharacteristic=(X-C a)*(X-C ((θ:ℂ)-a))*C ((1/y:ℝ):ℂ) := by
  have hy : (y:ℂ)≠0 := Complex.ofReal_ne_zero.mpr F.step_pos.ne'
  have hprod : a*((θ:ℂ)-a)=(y:ℂ) := by
    simp only [limitCharacteristic,eval_add,eval_mul,eval_sub,eval_C,eval_X] at ha
    push_cast at ha
    field_simp at ha
    linear_combination -ha
  apply Polynomial.funext
  intro z
  simp only [limitCharacteristic,eval_add,eval_mul,eval_sub,eval_C,eval_X]
  push_cast
  field_simp
  linear_combination -hprod

/-- Two convergent affine coordinates and an actual double factor, rather than
two applications of root existence that could select the same simple root. -/
theorem exists_two_affine_roots :
    ∃ a b : ℂ,∃ r s : ℝ→ℂ,
      a+b=(θ:ℂ) ∧ a*b=(y:ℂ) ∧ a.re=nesterov.Flow.cQ θ y ∧
      Tendsto r (𝓝[>] (0:ℝ)) (𝓝 a) ∧ Tendsto s (𝓝[>] (0:ℝ)) (𝓝 b) ∧
      ∀ᶠ ε in 𝓝[>] (0:ℝ),∃ q : Polynomial ℂ,
        F.scaledCharacteristic ε=(X-C (r ε))*(X-C (s ε))*q := by
  obtain ⟨a,ha,hare⟩ := F.exists_slow_root
  let b : ℂ := (θ:ℂ)-a
  let q₀ : Polynomial ℂ := (X-C b)*C ((1/y:ℝ):ℂ)
  have hfac : F.limitCharacteristic=(X-C a)*q₀ := by
    simpa only [q₀,b,mul_assoc] using F.limitCharacteristic_factor ha
  have hq : q₀≠0 := by
    exact mul_ne_zero (X_sub_C_ne_zero b) (C_ne_zero.mpr (Complex.ofReal_ne_zero.mpr
      (one_div_ne_zero F.step_pos.ne')))
  have hb : q₀.eval b=0 := by simp [q₀]
  have hd : F.limitCharacteristic.natDegree≤F.memory+2 := by
    rw [hfac]
    have hqd : q₀.natDegree≤1 := by
      exact natDegree_mul_le.trans (by simp)
    exact natDegree_mul_le.trans (by simp only [natDegree_X_sub_C];omega)
  obtain ⟨r,s,hr,hs,hroots⟩ := exists_two_root_selections
    F.scaledCharacteristic_degree hd F.scaledCharacteristic_tendsto hfac hq hb
  refine ⟨a,b,r,s,by dsimp [b];ring,?_,hare,hr,hs,hroots⟩
  have hh := congrArg (Polynomial.eval (0:ℂ)) (F.limitCharacteristic_factor ha)
  simp only [limitCharacteristic,eval_add,eval_mul,eval_sub,eval_C,eval_X,
    zero_mul,add_zero,zero_sub,neg_mul_neg] at hh
  dsimp [b]
  have hy : (y:ℂ)≠0 := Complex.ofReal_ne_zero.mpr F.step_pos.ne'
  push_cast at hh
  field_simp at hh
  linear_combination -hh

private theorem actual_double_factor {ε : ℝ} (hε : ε≠0) {r s : ℂ}
    {q : Polynomial ℂ}
    (hc : ∀ w : ℂ,(F.method ε).characteristic (ε^2) (1-(ε:ℂ)*w)=
      -(ε:ℂ)^2*(F.scaledCharacteristic ε).eval w)
    (hq : F.scaledCharacteristic ε=(X-C r)*(X-C s)*q) :
    (X-C (1-(ε:ℂ)*r))*(X-C (1-(ε:ℂ)*s)) ∣
      (F.method ε).characteristicPolynomial (ε^2) := by
  let inv : Polynomial ℂ := (C 1-X)*C ((ε:ℂ)⁻¹)
  refine ⟨-q.comp inv,?_⟩
  apply Polynomial.funext
  intro z
  have he : (ε:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hε
  have hi : 1-(ε:ℂ)*((1-z)/(ε:ℂ))=z := by field_simp;ring
  have hh := hc ((1-z)/(ε:ℂ))
  rw [hi,hq] at hh
  simp only [eval_mul,eval_sub,eval_X,eval_C] at hh
  rw [(F.method ε).characteristicPolynomial_eval,hh]
  simp only [eval_mul,eval_sub,eval_X,eval_C,eval_neg,eval_comp,inv]
  rw [div_eq_mul_inv]
  field_simp
  ring

/-- Literal exponential slow roots. The product of the two linear factors
divides the actual characteristic polynomial, including when the roots coincide. -/
theorem exists_two_exponential_roots :
    ∃ a b : ℂ,∃ v w : ℝ→ℂ,
      a+b=(θ:ℂ) ∧ a*b=(y:ℂ) ∧ a.re=nesterov.Flow.cQ θ y ∧
      Tendsto v (𝓝[>] (0:ℝ)) (𝓝 a) ∧ Tendsto w (𝓝[>] (0:ℝ)) (𝓝 b) ∧
      ∀ᶠ ε in 𝓝[>] (0:ℝ),
        (X-C (F.wave ε (v ε)))*(X-C (F.wave ε (w ε))) ∣
          (F.method ε).characteristicPolynomial (ε^2) := by
  obtain ⟨a,b,r,s,hab,hmul,hare,hr,hs,hroots⟩ := F.exists_two_affine_roots
  have he : Tendsto (fun ε : ℝ=>ε) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    continuous_id.continuousWithinAt.tendsto
  have he' : Tendsto (fun ε : ℝ=>(ε:ℂ)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    convert (Complex.continuous_ofReal.tendsto 0).comp he using 1
    funext ε
    rfl
  have hzr : Tendsto (fun ε : ℝ=>1-(ε:ℂ)*r ε) (𝓝[>] (0:ℝ)) (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (he'.mul hr)
  have hzs : Tendsto (fun ε : ℝ=>1-(ε:ℂ)*s ε) (𝓝[>] (0:ℝ)) (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (he'.mul hs)
  refine ⟨a,b,(fun ε=>logCoordinate ε (r ε)),(fun ε=>logCoordinate ε (s ε)),
    hab,hmul,hare,logCoordinate_tendsto he hr,logCoordinate_tendsto he hs,?_⟩
  filter_upwards [hroots,F.affine_characteristic_eq,self_mem_nhdsWithin,
    hzr.eventually_ne (by norm_num : (1:ℂ)≠0),hzs.eventually_ne (by norm_num : (1:ℂ)≠0)]
      with ε hq hc hε hnr hns
  obtain ⟨q,hq⟩ := hq
  simp only [wave,exp_logCoordinate hnr,exp_logCoordinate hns]
  exact F.actual_double_factor (ne_of_gt hε) hc hq

/-- The root assertion of the slow normal form, with the source quadratic and
its slowest real part stated literally. -/
theorem two_slow_roots :
    ∃ a b : ℂ,∃ v w : ℝ→ℂ,
      a^2-(θ:ℂ)*a+(y:ℂ)=0 ∧ b^2-(θ:ℂ)*b+(y:ℂ)=0 ∧
      min a.re b.re=nesterov.Flow.cQ θ y ∧
      Tendsto v (𝓝[>] (0:ℝ)) (𝓝 a) ∧ Tendsto w (𝓝[>] (0:ℝ)) (𝓝 b) ∧
      ∀ᶠ ε in 𝓝[>] (0:ℝ),
        (F.method ε).characteristic (ε^2) (F.wave ε (v ε))=0 ∧
        (F.method ε).characteristic (ε^2) (F.wave ε (w ε))=0 ∧
        (X-C (F.wave ε (v ε)))*(X-C (F.wave ε (w ε))) ∣
          (F.method ε).characteristicPolynomial (ε^2) := by
  obtain ⟨a,b,v,w,hab,hmul,hare,hv,hw,hfactor⟩ := F.exists_two_exponential_roots
  have ha : a^2-(θ:ℂ)*a+(y:ℂ)=0 := by rw [←hab,←hmul];ring
  have hb : b^2-(θ:ℂ)*b+(y:ℂ)=0 := by rw [←hab,←hmul];ring
  have hre : a.re+b.re=θ := by simpa only [Complex.add_re,Complex.ofReal_re] using congrArg Complex.re hab
  have hmin : min a.re b.re=nesterov.Flow.cQ θ y := by
    rw [min_eq_left (by linarith [nesterov.Flow.cQ_le_half θ y]),hare]
  refine ⟨a,b,v,w,ha,hb,hmin,hv,hw,?_⟩
  filter_upwards [hfactor] with ε hε
  obtain ⟨q,hq⟩ := hε
  refine ⟨?_,?_,⟨q,hq⟩⟩
  · rw [←(F.method ε).characteristicPolynomial_eval,hq]
    simp
  · rw [←(F.method ε).characteristicPolynomial_eval,hq]
    simp

end SecondOrderFamily
end
end nesterov.Slow
