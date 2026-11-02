import jacobi.Support.FrequencyEnvelope
import jacobi.Support.EnvelopeCircleBounds
import jacobi.Support.EdgeWaveDerivative

/-!
Article: jacobi, Appendix C.3 (polynomial and derivative envelopes).
Cauchy's estimate for the actual entire angular support polynomial
gives the full printed derivative envelope, with the original N
factor and exactly the original minimum on the smaller real strip.
Source: mathlib, Complex.norm_cderiv_le.
Use: the actual support interpolation derivative bound and the two-edge Gram comparison retain the original frequency decay at all growing spectral indices.
-/
namespace jacobi.Support
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology

/-- The genuine original angular support polynomial has the complete source complex derivative envelope.
Use: the actual support interpolation derivative bound and the two-edge Gram comparison retain the original frequency decay at all growing spectral indices.
Article: jacobi, Appendix C.3 (polynomial and derivative envelopes).
Source: Cauchy's derivative estimate, mathlib Complex.norm_cderiv_le.
Proof: use the actual circle of radius 1/N. The original real-strip margin and enlarged imaginary strip keep the whole circle in the proved wave envelope. At high frequency the genuine minimum changes by at most 2^gamma. At low frequency the actual transition estimate handles the entire circle, including zero, with the same original minimum at its nonzero center. Entire polynomial dependence permits the genuine Cauchy estimate. -/
theorem naturalWave_frequency_derivative {a b bnd:ℝ} (ha:-1<a) (hb:-1<b) (hbnd:0<bnd) :
    ∃C:ℝ,0<C ∧ ∀ᶠn:ℕ in atTop,∀m:ℕ,2*m≤n+3→∀theta:ℂ,theta≠0→
      |theta.re|≤3*π/4→|theta.im|≤bnd/ jacobi.Jacobi.frequency a b (n+1)→
      ‖deriv (fun z:ℂ => naturalWave a b ha hb n m (Complex.cos z)) theta‖≤
        C* jacobi.Jacobi.frequency a b (n+1)*min (((m:ℝ)+1)^gamma a) (‖theta‖^(-gamma a)) := by
  -- The same original entire angular polynomial is bounded on the actual Cauchy circle before taking its derivative.
  obtain ⟨P,hP,henv⟩ := naturalWave_frequency_envelope (bnd:=bnd+1) ha hb (by positivity)
  obtain ⟨A,hA,htransition⟩ := naturalWave_transition (R:=3) ha hb (by norm_num)
  let F := (2:ℝ)^gamma a
  refine ⟨(A+P)*F,by dsimp [F]; positivity,?_⟩
  have hnlarge := (tendsto_natCast_atTop_atTop : Tendsto (fun n:ℕ => (n:ℝ)) atTop atTop).eventually
    (eventually_ge_atTop (20/π))
  filter_upwards [henv,htransition,hnlarge,eventually_ge_atTop (8:ℕ)] with n hnP hnA hlarge hlargeNat
  intro m hm theta htheta hre him
  let N := jacobi.Jacobi.frequency a b (n+1)
  let x : ℝ := (m:ℝ)+1
  let g := fun z:ℂ => naturalWave a b ha hb n m (Complex.cos z)
  have hN0 : 0<N := jacobi.Jacobi.frequency_pos ha hb (by omega)
  have hN := natural_frequency_ge a b ha hb n
  have hx : 0<x := by dsimp [x]; positivity
  have hxn : x≤n := by dsimp [x]; exact_mod_cast (show m+1≤n by omega)
  have hxN : x≤N := hxn.trans hN
  have hg : 0≤gamma a := (parameter_pos ha hb).1.le
  have hr : 0<1/N := by positivity
  have hrsmall : 1/N≤π/20 := by
    have h20 : 20≤N*π := ((div_le_iff₀ pi_pos).mp hlarge).trans (mul_le_mul_of_nonneg_right hN pi_pos.le)
    apply (div_le_iff₀ hN0).mpr
    nlinarith only [h20]
  have hcircle (z:ℂ) (hz:z∈Metric.sphere theta (1/N)) :
      ‖g z‖≤((A+P)*F)*min (x^gamma a) (‖theta‖^(-gamma a)) := by
    have hdist : ‖z-theta‖=1/N := by simpa only [Metric.mem_sphere,dist_eq_norm] using hz
    have hnorm : ‖z‖≤‖theta‖+1/N := by
      have h := norm_add_le theta (z-theta)
      rw [show theta+(z-theta)=z by ring,hdist] at h
      exact h
    have hminor : 0≤min (x^gamma a) (‖theta‖^(-gamma a)) := by positivity
    by_cases hhigh:2/N≤‖theta‖
    · have hcircle' := frequency_decay_circle hg htheta (r:=1/N)
        (by simpa only [mul_one_div] using hhigh) hdist.le
      have hre' : |z.re|≤4*π/5 := by
        have h := abs_add_le theta.re (z-theta).re
        rw [show theta.re+(z-theta).re=z.re by simp only [Complex.sub_re]; ring] at h
        have hzre := Complex.abs_re_le_norm (z-theta)
        rw [hdist] at hzre
        linarith only [h,hzre,hre,hrsmall]
      have him' : |z.im|≤(bnd+1)/N := by
        have h := abs_add_le theta.im (z-theta).im
        rw [show theta.im+(z-theta).im=z.im by simp only [Complex.sub_im]; ring] at h
        have hzim := Complex.abs_im_le_norm (z-theta)
        rw [hdist] at hzim
        calc
          _ ≤ |theta.im|+1/N := h.trans (add_le_add le_rfl hzim)
          _ ≤ bnd/N+1/N := add_le_add him le_rfl
          _ = _ := by ring
      have henv' := hnP m hm z (norm_pos_iff.mp hcircle'.1) hre' him'
      have hcompare := frequency_min_circle_high hg (rpow_pos_of_pos hx (gamma a)).le htheta
        (r:=1/N) (by simpa only [mul_one_div] using hhigh) hdist.le
      calc
        _ ≤ P*min (x^gamma a) (‖z‖^(-gamma a)) := henv'
        _ ≤ P*(F*min (x^gamma a) (‖theta‖^(-gamma a))) := mul_le_mul_of_nonneg_left hcompare hP.le
        _ ≤ ((A+P)*F)*min (x^gamma a) (‖theta‖^(-gamma a)) := by
          have h := mul_nonneg (mul_nonneg hA.le (by dsimp [F]; positivity : 0≤F)) hminor
          nlinarith only [h]
    · have hlow : ‖theta‖≤2/N := (lt_of_not_ge hhigh).le
      have hcenter : ‖theta‖*x≤2 := by
        calc
          _ ≤ (2/N)*x := mul_le_mul_of_nonneg_right hlow hx.le
          _ ≤ (2/N)*N := mul_le_mul_of_nonneg_left hxN (by positivity)
          _ = _ := by field_simp
      have hscaled : ‖z‖*x≤3 := by
        calc
          _ ≤ (3/N)*x := mul_le_mul_of_nonneg_right (hnorm.trans (by
            calc
              _ ≤ 2/N+1/N := add_le_add hlow le_rfl
              _ = _ := by ring)) hx.le
          _ ≤ (3/N)*N := mul_le_mul_of_nonneg_left hxN (by positivity)
          _ = _ := by field_simp
      have h := (hnA m hm z hscaled).1
      have hcompare := frequency_min_circle_low hg hx htheta hcenter
      calc
        _ ≤ A*x^gamma a := h
        _ ≤ A*(F*min (x^gamma a) (‖theta‖^(-gamma a))) := mul_le_mul_of_nonneg_left hcompare hA.le
        _ ≤ ((A+P)*F)*min (x^gamma a) (‖theta‖^(-gamma a)) := by
          have h := mul_nonneg (mul_nonneg hP.le (by dsimp [F]; positivity : 0≤F)) hminor
          nlinarith only [h]
  have hd : DifferentiableOn ℂ g univ :=
    ((naturalWave_differentiable a b ha hb n m).comp Complex.differentiable_cos).differentiableOn
  change ‖deriv g theta‖≤_
  rw [← Complex.cderiv_eq_deriv isOpen_univ hd hr (subset_univ _)]
  exact (Complex.norm_cderiv_le hr hcircle).trans_eq (by dsimp [N,x]; field_simp)

end
end jacobi.Support
