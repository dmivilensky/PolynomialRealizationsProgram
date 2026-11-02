import jacobi.GelfandLevitan.Fredholm
import chebyshev2.Continuum.CompactEigenbasis

/-!
Article: jacobi, Appendix C.2 (uniform GL coercivity).
The actual original positive operator has a genuine bounded inverse.
The complete compact eigenbasis theorem from chebyshev2 then gives
one positive lower bound for its entire original quadratic form.
Every smaller physical interval uses the same bound by actual zero
extension, so no interval-dependent spectral gap is assumed.
Use: the actual inverse norm bounds each true shifted eigenvalue in the source uniform coercivity argument.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set MeasureTheory jacobi.Reference
open scoped Topology InnerProductSpace
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false

/-- A genuine original kernel eigenvector is an eigenvector of the actual positive identity perturbation with the exactly shifted eigenvalue.
Use: the actual inverse norm bounds each true shifted eigenvalue in the source uniform coercivity argument.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
Proof: expand the genuine identity perturbation and combine its actual scalar multiples of the same original vector. -/
theorem positiveOperator_on_eigenvector (a : ℝ) (ha : -1<a) {eig : ℝ} {v : halfSubspace}
    (he : kernelOperator a ha v=eig • v) : positiveOperator a ha v=(1+eig) • v := by
  change v+kernelOperator a ha v=(1+eig) • v
  rw [he,add_smul,one_smul]

/-- Every genuine normalized kernel eigenvector has a positive shifted eigenvalue bounded below by one fixed actual inverse norm.
Use: supplies the common positive coefficient bound at every index of the actual complete compact eigenbasis.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
Proof: true source quadratic positivity makes the actual shifted
eigenvalue positive. Apply the proved bounded-inverse input/output
inequality to the same genuine unit vector. Its actual eigenvalue
equation and true unit norm give the original uniform lower bound. -/
theorem shifted_eigenvalue_lower (a : ℝ) (ha : -1<a) {eig : ℝ} (v : halfSubspace)
    (hv : ‖v‖=1) (he : kernelOperator a ha v=eig • v) :
    (‖positiveInverse a ha‖+1)⁻¹≤1+eig := by
  -- Both positivity and the inverse norm concern this same actual original operator and genuine Hilbert vector.
  have hv0 : (v:Space)≠0 := by
    intro h
    have hh : v=0 := Subtype.ext h
    rw [hh,norm_zero] at hv
    norm_num at hv
  have hpos := quadratic_pos a ha (v:Space) (halfSubspace_supported v) hv0
  have hQ := positiveOperator_on_eigenvector a ha he
  rw [← positiveOperator_quadratic,hQ,real_inner_smul_left v v (1+eig),real_inner_self_eq_norm_sq,hv] at hpos
  simp only [one_pow,mul_one] at hpos
  have hn := positiveOperator_norm_lower a ha v
  rw [hQ,norm_smul,hv,Real.norm_eq_abs,abs_of_pos hpos,mul_one] at hn
  rw [inv_eq_one_div]
  apply (div_le_iff₀ (by positivity : (0:ℝ)<‖positiveInverse a ha‖+1)).mpr
  nlinarith

/-- The actual original identity-plus-GL-kernel operator has a genuine positive uniform quadratic lower bound on its full original half-interval Hilbert domain.
Use: supplies the unconditional source coercivity constant required for solving the true GL equation on every smaller physical interval.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
Proof: reuse the earlier article's complete eigenbasis for the actual
compact symmetric kernel operator. Every actual shifted eigenvalue
is at least the same positive inverse-norm constant. Expand both the
true operator quadratic form and the original norm by community
Parseval. Compare their genuinely convergent scalar series termwise. -/
theorem positiveOperator_coercive (a : ℝ) (ha : -1<a) :
    ∃ κ:ℝ,0<κ ∧ ∀ v:halfSubspace,κ*‖v‖^2≤ inner ℝ (positiveOperator a ha v) v := by
  -- The complete basis and all spectral lower bounds are obtained from the actual original compact operator.
  obtain ⟨ι,b,eig,hdiag⟩ := chebyshev2.Continuum.exists_compact_eigenbasis
    (kernelOperator a ha) (kernelOperator_compact a ha) (kernelOperator_symmetric a ha)
  let κ := (‖positiveInverse a ha‖+1)⁻¹
  have hκ : 0<κ := by dsimp [κ]; positivity
  have hlow (i : ι) : κ≤1+eig i := shifted_eigenvalue_lower a ha (b i)
    (b.orthonormal.norm_eq_one i) (hdiag i)
  have hQ (i : ι) : positiveOperator a ha (b i)=(1+eig i) • b i :=
    positiveOperator_on_eigenvector a ha (hdiag i)
  refine ⟨κ,hκ,fun v => ?_⟩
  have hcoef (i : ι) : inner ℝ v (b i)*inner ℝ (b i) v=(inner ℝ (b i) v)^2 := by
    have hc : inner ℝ v (b i)=inner ℝ (b i) v := real_inner_comm _ _
    rw [hc]
    ring
  have hpair (i : ι) : inner ℝ v (b i)*inner ℝ (b i) (positiveOperator a ha v)=
      (1+eig i)*(inner ℝ (b i) v)^2 := by
    have hs : inner ℝ (b i) (positiveOperator a ha v)=inner ℝ (positiveOperator a ha (b i)) v :=
      (positiveOperator_symmetric a ha (b i) v).symm
    have hc : inner ℝ v (b i)=inner ℝ (b i) v := real_inner_comm _ _
    rw [hs,hQ i,real_inner_smul_left (b i) v (1+eig i),hc]
    ring
  have hbase : HasSum (fun i => κ*(inner ℝ (b i) v)^2) (κ*‖v‖^2) := by
    simpa only [hcoef,real_inner_self_eq_norm_sq] using (b.hasSum_inner_mul_inner v v).mul_left κ
  have hspectral := b.hasSum_inner_mul_inner v (positiveOperator a ha v)
  have hcomm : inner ℝ v (positiveOperator a ha v)=inner ℝ (positiveOperator a ha v) v := real_inner_comm _ _
  rw [hcomm] at hspectral
  have hweighted : HasSum (fun i => (1+eig i)*(inner ℝ (b i) v)^2)
      (inner ℝ (positiveOperator a ha v) v) := by
    simpa only [hpair] using hspectral
  exact hasSum_le (fun i => mul_le_mul_of_nonneg_right (hlow i) (sq_nonneg _)) hbase hweighted

/-- The original genuine double-integral GL quadratic form has a strictly positive uniform lower bound for every actual half-supported original L2 input.
Use: the same true source kappa_star applies to all smaller intervals after actual zero extension, giving the original uniform GL inverse bound.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
Proof: a true half-supported original input is exactly an element of
the actual closed half-interval Hilbert domain. Apply the proved
genuine operator coercivity there, then use its already proved exact
original kernel integral quadratic identity and inherited L2 norm. -/
theorem quadratic_coercive (a : ℝ) (ha : -1<a) :
    ∃ κ:ℝ,0<κ ∧ ∀ v:Space,HalfSupported v → κ*‖v‖^2≤quadratic a ha v := by
  obtain ⟨κ,hκ,hbound⟩ := positiveOperator_coercive a ha
  refine ⟨κ,hκ,fun v hv => ?_⟩
  let w : halfSubspace := ⟨v,(mem_halfSubspace_iff v).mpr hv⟩
  have hh := hbound w
  rw [positiveOperator_quadratic] at hh
  exact hh

/-- One genuine original GL coercivity constant works on every smaller source interval, for all actual original L2 zero extensions.
Use: provides the unconditional uniform original lower bound required by the source GL construction for every 0<t<=1/2.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
Proof: an original input zero outside (0,t) with t<=1/2 is genuinely
half-supported. The proved actual full-half quadratic lower bound
therefore applies to that same original zero extension, with exactly
the same positive constant, independently of t. -/
theorem quadratic_coercive_all_intervals (a : ℝ) (ha : -1<a) :
    ∃ κ:ℝ,0<κ ∧ ∀ t∈Ioc (0:ℝ) (1/2),∀ v:Space,
      (∀ᵐ s:Interval,t<(s:ℝ) → v s=0) → κ*‖v‖^2≤quadratic a ha v := by
  obtain ⟨κ,hκ,hbound⟩ := quadratic_coercive a ha
  refine ⟨κ,hκ,fun t ht v hv => hbound v ?_⟩
  filter_upwards [hv] with s hs
  intro hhalf
  exact hs (ht.2.trans_lt hhalf)

end
end jacobi.GelfandLevitan
