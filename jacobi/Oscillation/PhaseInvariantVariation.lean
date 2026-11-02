import jacobi.Oscillation.PhaseInvariantBounds

/-!
Article: jacobi, Proposition B.1.
Finite-interval integration of the exact modified-phase derivative gives
its cubic variation bound. No improper integral or asymptotic phase
assumption is used: the later Bessel application evaluates this bound
along the actual exhaustive numbered zero sequence.
Use: evaluates the dominating finite integral in the actual McMahon remainder proof.
-/
namespace jacobi.Oscillation
noncomputable section
open Real Set
set_option backward.isDefEq.respectTransparency false

/-- The elementary cubic tail primitive has the exact fourth-order derivative.
Use: evaluates the dominating finite integral in the actual McMahon remainder proof.
Article: jacobi, Proposition B.1.
Proof: differentiate the reciprocal cubic explicitly and clear positive denominators. -/
theorem inverseCube_hasDerivAt (D : ℝ) {x : ℝ} (hx : 0<x) :
    HasDerivAt (fun t : ℝ => -D/(3*t^3)) (D/x^4) x := by
  convert (hasDerivAt_const x (-D)).div (((hasDerivAt_id x).pow 3).const_mul 3)
    (by positivity : 3*x^3≠0) using 1
  · rfl
  · norm_num only [Pi.pow_apply,id_eq,Nat.cast_ofNat,Nat.reduceSub,mul_one,zero_mul,zero_sub]
    field_simp [hx.ne']

/-- The corrected actual inverse-square phase varies by at most an explicit cubic tail on every finite interval.
Use: passage along genuine numbered Bessel zeros determines the McMahon correction with its cubic remainder.
Article: jacobi, Proposition B.1.
Proof: apply the fundamental theorem of calculus to the exact modified
phase and to the elementary reciprocal cubic primitive. Bound the norm
of the genuine derivative integral by its fourth-order majorant, then
discard the nonnegative terminal cubic tail. -/
theorem phaseInvariant_variation {theta : ℝ → ℝ} {c x y : ℝ}
    (hx : 1≤x) (hxy : x≤y)
    (ht : ∀ t∈Icc x y,HasDerivAt theta (1+c/t^2*sin (theta t)^2) t) :
    |phaseInvariant c theta y-phaseInvariant c theta x|≤(c^2+|c|)/(3*x^3) := by
  -- Both integrals are over a finite interval of the original actual phase; their integrability follows from the proved ordinary derivatives.
  have hp : ∀ t∈Icc x y,0<t := fun t ht => by linarith [ht.1]
  have hs : ContinuousOn (phaseInvariantSlope c theta) (Icc x y) := by
    intro t hmem
    have ht0 := hp t hmem
    have htc := (ht t hmem).continuousAt
    apply ContinuousAt.continuousWithinAt
    unfold phaseInvariantSlope
    fun_prop (disch := positivity)
  have hb : ContinuousOn (fun t : ℝ => (c^2+|c|)/t^4) (Icc x y) := by
    intro t hmem
    have ht0 := hp t hmem
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := positivity)
  have hsi := hs.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hxy
  have hbi := hb.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hxy
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht' => phaseInvariant_hasDerivAt (hp t (by simpa only [uIcc_of_le hxy] using ht'))
      (ht t (by simpa only [uIcc_of_le hxy] using ht'))) hsi
  have hg := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht' => inverseCube_hasDerivAt (c^2+|c|)
      (hp t (by simpa only [uIcc_of_le hxy] using ht'))) hbi
  have hn := intervalIntegral.norm_integral_le_of_norm_le hxy
    (Filter.Eventually.of_forall (fun t ht' => by
      rw [Real.norm_eq_abs]
      exact phaseInvariantSlope_bound c theta (by linarith [ht'.1]))) hbi
  rw [hf,Real.norm_eq_abs,hg] at hn
  simp only [neg_div,sub_neg_eq_add] at hn
  have hy : 0<y := by linarith
  have ht0 : 0≤(c^2+|c|)/(3*y^3) := by positivity
  linarith

end
end jacobi.Oscillation
