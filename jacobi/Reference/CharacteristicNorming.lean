import jacobi.Reference.CharacteristicGamma

/-!
Article: jacobi, Appendix C.2 (exact parity splitting).
The simple zeros and alternating derivatives belong to the literal Gamma
characteristic. The squared norms remain the genuine reference integrals;
their equality with the reciprocal characteristic derivatives is proved,
rather than used as a new definition of either object.
Use: computes characteristicTau_derivative in the true energy coordinate.
-/
namespace jacobi.Reference
noncomputable section
open Real Set _root_.Complex
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] characteristicTau

/-- The actual Gamma characteristic has its exact signed derivative at every positive reference frequency.
Use: computes characteristicTau_derivative in the true energy coordinate.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: the first Gamma reciprocal vanishes and has derivative
-(-1)^k*k!, while the second has the literal nonzero value
1/Gamma(k+2*gamma). The product rule therefore has only one nonzero term. -/
theorem characteristicGamma_hasDerivAt (a : ℝ) (k : ℕ) :
    HasDerivAt (characteristicGamma a)
      ((-1:ℂ)^(k+1)*(k.factorial:ℂ)/(Complex.Gamma ((k:ℂ)+2*(gamma a:ℂ))))
      ((k:ℂ)+(gamma a:ℂ)) := by
  -- Both factors are the actual entire reciprocal Gamma functions, even at the first factor's zero.
  let x : ℂ := (k:ℂ)+(gamma a:ℂ)
  have hm : (gamma a:ℂ)-x= -(k:ℂ) := by dsimp [x]; ring
  have hp : (gamma a:ℂ)+x=(k:ℂ)+2*(gamma a:ℂ) := by dsimp [x]; ring
  have hG : HasDerivAt (fun s : ℂ => (Complex.Gamma s)⁻¹)
      ((-1:ℂ)^k*(k.factorial:ℂ)) ((gamma a:ℂ)-x) := by
    rw [hm,← reciprocalGamma_derivative_neg_nat]
    exact (Complex.differentiable_one_div_Gamma _).hasDerivAt
  have hM : HasDerivAt (fun u : ℂ => (gamma a:ℂ)-u) (-1) x := by
    convert! (hasDerivAt_const x (gamma a:ℂ)).sub (hasDerivAt_id x) using 1
    norm_num
  have hP : HasDerivAt (fun u : ℂ => (gamma a:ℂ)+u) 1 x := by
    convert! (hasDerivAt_const x (gamma a:ℂ)).add (hasDerivAt_id x) using 1
    norm_num
  have h1 := HasDerivAt.comp (h₂ := fun s : ℂ => (Complex.Gamma s)⁻¹)
    (h := fun u : ℂ => (gamma a:ℂ)-u) x hG hM
  have h2 := HasDerivAt.comp (h₂ := fun s : ℂ => (Complex.Gamma s)⁻¹)
    (h := fun u : ℂ => (gamma a:ℂ)+u) x
      (Complex.differentiable_one_div_Gamma _).hasDerivAt hP
  have hd := h1.mul h2
  change HasDerivAt (fun u : ℂ =>
    (Complex.Gamma ((gamma a:ℂ)-u))⁻¹*(Complex.Gamma ((gamma a:ℂ)+u))⁻¹) _ x at hd
  have he : (fun u : ℂ => (Complex.Gamma ((gamma a:ℂ)-u))⁻¹*
      (Complex.Gamma ((gamma a:ℂ)+u))⁻¹)=characteristicGamma a := rfl
  rw [he] at hd
  convert hd using 1
  simp only [Function.comp_apply,hm,hp,Complex.Gamma_neg_nat_eq_zero,inv_zero,
    zero_mul,add_zero,pow_succ,div_eq_mul_inv]
  ring

/-- The actual reference characteristic composed with the exact polynomial energy map is the literal Gamma frequency function.
Use: differentiates characteristicTau without differentiating a square-root branch.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: choose omega=pi*x in characteristicTau_eq and cancel the genuine nonzero pi. -/
theorem characteristicTau_frequency (a : ℝ) (x : ℂ) :
    characteristicTau a ((jacobi.Jacobi.endpointCorrection a:ℂ)+(Real.pi:ℂ)^2*x^2)=
      characteristicGamma a x := by
  rw [characteristicTau_eq a (omega := (Real.pi:ℂ)*x) (by ring),
    mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)]

/-- The literal reference characteristic has the exact article derivative, with its true alternating sign at every actual reference eigenvalue.
Use: proves simplicity and the exact reciprocal-derivative norming rule from the independently evaluated reference norm integrals.
Article: jacobi, Appendix C.2 (norming ratios).
Proof: differentiate the polynomial energy parametrization at x=k+gamma.
The reference characteristic is entire, so its actual chain derivative
equals the computed Gamma derivative. The positive reference frequency
and nonzero pi justify division by 2*pi^2*(k+gamma). -/
theorem characteristicTau_derivative {a : ℝ} (ha : -1<a) (k : ℕ) :
    deriv (characteristicTau a) (eigenvalue a k:ℂ)=
      (-1:ℂ)^(k+1)*(k.factorial:ℂ)/
        (2*(Real.pi:ℂ)^2*((k:ℂ)+(gamma a:ℂ))*Complex.Gamma ((k:ℂ)+2*(gamma a:ℂ))) := by
  -- Compare derivatives of the same entire function in the two genuine coordinates.
  let x : ℂ := (k:ℂ)+(gamma a:ℂ)
  let E : ℂ → ℂ := fun u => (jacobi.Jacobi.endpointCorrection a:ℂ)+(Real.pi:ℂ)^2*u^2
  have hE : E x=(eigenvalue a k:ℂ) := by dsimp [E,x,eigenvalue]; push_cast; ring
  have hp : HasDerivAt E (2*(Real.pi:ℂ)^2*x) x := by
    convert! (((hasDerivAt_id x).pow 2).const_mul ((Real.pi:ℂ)^2)).const_add
      (jacobi.Jacobi.endpointCorrection a:ℂ) using 1
    norm_num [E]
    ring
  have hf : HasDerivAt (characteristicTau a)
      (deriv (characteristicTau a) (E x)) (E x) :=
    (characteristicTau_analytic a (E x)).differentiableAt.hasDerivAt
  have hd := HasDerivAt.comp (h₂ := characteristicTau a) (h := E) x hf hp
  have he : (characteristicTau a ∘ E)=characteristicGamma a :=
    funext (characteristicTau_frequency a)
  rw [he] at hd
  have hh := hd.unique (characteristicGamma_hasDerivAt a k)
  rw [hE] at hh
  have hx : x≠0 := by
    have hxcast : x=(((k:ℝ)+gamma a:ℝ):ℂ) := by dsimp [x]; push_cast; rfl
    rw [hxcast]
    apply Complex.ofReal_ne_zero.mpr (show (k:ℝ)+gamma a≠0 from ne_of_gt (by
      have hg : 0<gamma a := by linarith [(parameters ha).1]
      positivity))
  have hpi : (Real.pi:ℂ)≠0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hG : Complex.Gamma ((k:ℂ)+2*(gamma a:ℂ))≠0 := Complex.Gamma_ne_zero_of_re_pos (by
    have hre : ((k:ℂ)+2*(gamma a:ℂ)).re=(k:ℝ)+2*gamma a := by norm_num
    rw [hre]
    have hg : 0<gamma a := by linarith [(parameters ha).1]
    positivity)
  apply (eq_div_iff (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hpi)) hx) hG)).mpr
  have hmul := (eq_div_iff hG).mp hh
  change deriv (characteristicTau a) (eigenvalue a k:ℂ)*
    (2*(Real.pi:ℂ)^2*x*Complex.Gamma ((k:ℂ)+2*(gamma a:ℂ)))=_
  linear_combination hmul

end
end jacobi.Reference
