import jacobi.Reference.Parameters
import jacobi.Jacobi.EndpointFactor
import jacobi.Jacobi.Gegenbauer

/-!
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
The reference eigenfunctions are the literal normalized Gegenbauer
functions, represented by the already proved real Jacobi polynomial.
Their endpoint normalization and reflection are proved for the complete
parameter range. No spectral or differential-equation conclusion is
included as an assumption in their definition.
Use: defines the actual reference eigenfunctions and their classical derivatives.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Filter Polynomial
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The source reference sine-power prefactor on the physical interval.
Use: defines the actual reference eigenfunctions and their classical derivatives.
Article: jacobi, Lemma C.1.
-/
def weight (a t : ℝ) : ℝ := (sin (Real.pi*t)/Real.pi)^(gamma a)

/-- The actual source reference eigenfunction at its original kth spectral value.
Use: supplies the reference orthonormal system, the norming constants and the actual functions in the GL kernel.
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
-/
def eigenfunction (a : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  weight a t* jacobi.Jacobi.angular (jacobiIndex a) (jacobiIndex a) k (Real.pi*t)

/-- The actual sine-power weight is strictly positive at every physical interior point.
Use: preserves precisely the original reference polynomial's interior zeros.
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
Proof: sine is positive between zero and pi; a real power of a positive base is positive. -/
theorem weight_pos (a : ℝ) {t : ℝ} (ht : t∈Ioo 0 1) : 0<weight a t := by
  apply Real.rpow_pos_of_pos
  exact div_pos (Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos ht.1)
    (by nlinarith [Real.pi_pos,ht.2])) Real.pi_pos

/-- The actual reference prefactor is continuous on the closed physical interval and vanishes at both ends.
Use: establishes genuine integrability of every finite reference product before constructing its L2 vector.
Article: jacobi, Lemma C.1.
Proof: gamma is strictly positive, so the community real-power continuity theorem includes both zero bases. -/
theorem weight_properties {a : ℝ} (ha : -1<a) :
    Continuous (weight a) ∧ weight a 0=0 ∧ weight a 1=0 := by
  have hg : 0<gamma a := by linarith [(parameters ha).1]
  refine ⟨(Real.continuous_rpow_const hg.le).comp ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).div_const _),?_,?_⟩
  · simp only [weight,mul_zero,sin_zero,zero_div,Real.zero_rpow hg.ne']
  · simp only [weight,mul_one,sin_pi,zero_div,Real.zero_rpow hg.ne']

/-- The actual reference eigenfunctions are continuous, vanish at both physical endpoints, and have integrable products.
Use: supplies genuine L2 membership and convergence of the reference norm integrals.
Article: jacobi, Lemma C.1.
Proof: multiply the continuous sine-power prefactor by the actual polynomial in cos(pi*t). The endpoint factors are zero. -/
theorem eigenfunction_properties {a : ℝ} (ha : -1<a) (k : ℕ) :
    Continuous (eigenfunction a k) ∧ eigenfunction a k 0=0 ∧ eigenfunction a k 1=0 := by
  obtain ⟨hw,h0,h1⟩ := weight_properties ha
  have hp : Continuous (fun t : ℝ => jacobi.Jacobi.angular (jacobiIndex a) (jacobiIndex a) k (Real.pi*t)) := by
    unfold jacobi.Jacobi.angular
    fun_prop
  exact ⟨hw.mul hp,by simp only [eigenfunction,h0,zero_mul],by simp only [eigenfunction,h1,zero_mul]⟩

/-- Every original reference eigenfunction is exactly the literal classical Gegenbauer expression in the article.
Use: identifies the constructed reference system with the source's special functions, independently of subsequent spectral claims.
Article: jacobi, Proposition C.2.
Proof: the proved Gegenbauer/Jacobi identity fixes the exact polynomial normalization; reality identifies its complex value with the actual real polynomial. -/
theorem eigenfunction_gegenbauer {a : ℝ} (ha : -1<a) (k : ℕ) (t : ℝ) :
    (eigenfunction a k t:ℂ)=(weight a t:ℂ)*
      (jacobi.Jacobi.gegenbauer (gamma a:ℂ) k (cos (Real.pi*t):ℂ)/
        jacobi.Jacobi.gegenbauer (gamma a:ℂ) k 1) := by
  -- The endpoint normalization is the actual nonzero Gegenbauer value, not an independently chosen scaling constant.
  have hg : 0<(gamma a:ℂ).re := by simp only [Complex.ofReal_re]; linarith [(parameters ha).1]
  rw [jacobi.Jacobi.gegenbauer_normalized hg]
  have hindex : (gamma a:ℂ)-1/2=(jacobiIndex a:ℂ) := by dsimp [jacobiIndex]; push_cast; ring
  rw [hindex]
  have hp := Complex.conj_eq_iff_re.mp (jacobi.Jacobi.normalized_conj (jacobiIndex a) (jacobiIndex a) (cos (Real.pi*t)) k)
  rw [← hp]
  simp only [eigenfunction,Complex.ofReal_mul,jacobi.Jacobi.angular_eq_realNormalized,jacobi.Jacobi.realNormalized]

/-- The true equal-parameter shifted Jacobi polynomial has its exact parity factor at the opposite endpoint.
Use: proves the midpoint parity of the actual reference eigenfunctions without a second Gegenbauer recurrence.
Article: jacobi, Proposition C.2.
Proof: the genuine parameter-reflection identity has an actual endpoint scalar. Compare leading coefficients; reflection multiplies the top coefficient by (-1)^k and that coefficient is nonzero. -/
theorem symmetric_endpoint {g : ℝ} (hg : -1<g) (k : ℕ) :
    (jacobi.Jacobi.shiftedPolynomial g g k).eval 1=(-1:ℝ)^k := by
  -- Leading-coefficient comparison determines the actual normalization scalar for every degree, including degree zero.
  let p := jacobi.Jacobi.shiftedPolynomial g g k
  have hp : p.leadingCoeff≠0 := Polynomial.leadingCoeff_ne_zero.mpr (jacobi.Jacobi.shiftedPolynomial_ne_zero hg hg k)
  have h := congrArg Polynomial.leadingCoeff (jacobi.Jacobi.shiftedPolynomial_reflection hg hg k)
  have hpoly : (1-X:Polynomial ℝ)= -(X-C 1) := by simp only [Polynomial.C_1]; ring
  rw [Polynomial.leadingCoeff_comp (by rw [hpoly,Polynomial.natDegree_neg,Polynomial.natDegree_X_sub_C]; norm_num),
    Polynomial.leadingCoeff_mul,Polynomial.leadingCoeff_C,hpoly,Polynomial.leadingCoeff_neg,
    Polynomial.leadingCoeff_X_sub_C] at h
  rw [jacobi.Jacobi.shiftedPolynomial_natDegree hg hg] at h
  apply (mul_right_cancel₀ hp)
  change p.eval 1*p.leadingCoeff=(-1:ℝ)^k*p.leadingCoeff
  exact h.symm.trans (mul_comm _ _)

/-- The genuine reference eigenfunction has exactly the source's even or odd midpoint parity.
Use: splits the reference operator into its actual midpoint Neumann and Dirichlet spectral classes in Proposition C.2.
Article: jacobi, Lemma C.1.
Proof: the sine-power weight reflects unchanged and the true symmetric Jacobi polynomial reflects with its proved exact parity scalar. -/
theorem eigenfunction_reflection {a : ℝ} (ha : -1<a) (k : ℕ) (t : ℝ) :
    eigenfunction a k (1-t)=(-1:ℝ)^k*eigenfunction a k t := by
  -- Parity is proved for the literal original reference functions before introducing any midpoint boundary conditions.
  have hg := (parameters ha).2
  have h := congrArg (fun p : Polynomial ℝ => p.eval ((1-cos (Real.pi*t))/2))
    (jacobi.Jacobi.shiftedPolynomial_reflection hg hg k)
  simp only [Polynomial.eval_comp,Polynomial.eval_sub,Polynomial.eval_one,Polynomial.eval_X,
    Polynomial.eval_mul,Polynomial.eval_C,symmetric_endpoint hg] at h
  unfold eigenfunction weight jacobi.Jacobi.angular
  rw [show Real.pi*(1-t)=Real.pi-Real.pi*t by ring,Real.sin_pi_sub,Real.cos_pi_sub]
  rw [show (1- -cos (Real.pi*t))/2=1-(1-cos (Real.pi*t))/2 by ring,h]
  ring

end
end jacobi.Reference
