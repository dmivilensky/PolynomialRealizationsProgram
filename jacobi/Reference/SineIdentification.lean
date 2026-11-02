import jacobi.Reference.HalfIntegerCharacteristics
import jacobi.Jacobi.EquationUniqueness
import chebyshev2.SineContinuum.LegendreEigenfunctions

/-!
Article: jacobi, Proposition C.4.
The actual reference eigenfunctions and norms are identified with the
already verified sine--Legendre realization of chebyshev2.
Polynomial uniqueness reuses the two existing differential equations;
no second Legendre orthogonality, completeness or Mercer proof is needed.
Use: sine_eigenfunction_square identifies the actual special-order reference functions with the previously verified sine--Legendre basis.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Polynomial
set_option backward.isDefEq.respectTransparency false

/-- The original Jacobi polynomial with both parameters zero is the same community shifted Legendre polynomial used in the earlier article.
Use: sine_eigenfunction_square identifies the actual special-order reference functions with the previously verified sine--Legendre basis.
Article: jacobi, Proposition C.4.
Source: the classical Jacobi--Legendre specialization, DLMF 18.7.9.
Proof: both actual polynomials solve the same Jacobi equation and
have endpoint value one. The already proved coefficient uniqueness
identifies them at every degree, including the constant polynomial. -/
theorem shiftedPolynomial_legendre (k : ℕ) :
    jacobi.Jacobi.shiftedPolynomial 0 0 k=chebyshev2.SineContinuum.shifted k := by
  -- The two existing polynomial constructions are identified, rather than recreated.
  apply jacobi.Jacobi.equation_unique (a := 0) (b := 0) (by norm_num) k
    _ _ (jacobi.Jacobi.shiftedPolynomial_residual (by norm_num) k)
  · ext l
    rw [jacobi.Jacobi.equationResidual_coeff,coeff_zero]
    have h := chebyshev2.SineContinuum.shifted_coeff_recurrence k l
    linear_combination h
  · rw [jacobi.Jacobi.shiftedPolynomial_zero,← coeff_zero_eq_eval_zero,
      chebyshev2.SineContinuum.shifted_coeff]
    norm_num

/-- The actual source angular Jacobi eigenfunction at zero parameters is exactly the earlier article's Legendre polynomial in the cosine coordinate.
Use: sine_eigenfunction_square transfers the actual normalized reference profiles to the existing genuine sine--Legendre Mercer series.
Article: jacobi, Proposition C.4.
Proof: substitute the proved equality of the actual shifted polynomials in their common original cosine coordinate. -/
theorem angular_legendre (k : ℕ) (t : ℝ) :
    jacobi.Jacobi.angular 0 0 k (Real.pi*t)=
      chebyshev2.SineContinuum.legendre k (Real.cos (Real.pi*t)) := by
  rw [jacobi.Jacobi.angular,shiftedPolynomial_legendre]
  rfl

/-- The actual source norm scalar at order -1/2 is exactly pi^(-2).
Use: sine_norming computes the genuine reference integral norms before identifying normalized eigenfunctions.
Article: jacobi, Proposition C.4.
Proof: gamma=1/2, Gamma(1)=1 and Gamma(1/2)=sqrt(pi) in the original printed scalar. -/
theorem sine_normConstant : normConstant (-(1/2))=1/Real.pi^2 := by
  have hg : gamma (-(1/2))=1/2 := by norm_num [gamma]
  rw [normConstant,hg]
  norm_num only [show (1:ℝ)-2*(1/2)=0 by ring,show 2*(1/2:ℝ)=1 by ring,
    Real.rpow_zero,Real.Gamma_one,one_pow,one_mul,Real.rpow_one,Real.Gamma_one_half_eq,
    Real.sq_sqrt Real.pi_pos.le]
  ring

/-- Every genuine reference integral norm at order -1/2 has exactly its sine--Legendre value.
Use: sine_eigenfunction_square identifies the actual normalized reference basis without an unproved norm formula.
Article: jacobi, Proposition C.4.
Proof: specialize the previously proved actual Gamma norm formula.
The same positive Gamma(k+1) cancels from numerator and denominator. -/
theorem sine_norming (k : ℕ) : norming (-(1/2)) k=1/(Real.pi^2*((k:ℝ)+1/2)) := by
  have hg : gamma (-(1/2))=1/2 := by norm_num [gamma]
  rw [norming_formula (by norm_num),sine_normConstant,hg,
    show (2:ℝ)*(1/2)=1 by ring]
  field_simp [(Real.Gamma_pos_of_pos (by positivity : 0<(k:ℝ)+1)).ne']

/-- Every original reference spectral value at order -1/2 is exactly the earlier sine--Legendre eigenvalue.
Use: the actual special-case Green and profile series retain the original eigenvalue normalization.
Article: jacobi, Proposition C.4.
Proof: substitute gamma=1/2 and c_0=0 in the literal reference spectrum. -/
theorem sine_eigenvalue (k : ℕ) :
    eigenvalue (-(1/2)) k=chebyshev2.SineContinuum.mu k := by
  norm_num [eigenvalue,gamma,jacobi.Jacobi.endpointCorrection,chebyshev2.SineContinuum.mu]

/-- The actual normalized reference eigenfunction square at order -1/2 equals the existing genuine sine--Legendre basis square everywhere on the closed physical interval.
Use: the actual source persymmetric profile and constant are identified with the already verified sine Green diagonal and c_sin.
Article: jacobi, Proposition C.4.
Proof: use the proved original Jacobi--Legendre identification and
genuine reference norm. The positive-base half power squares to
sin(pi*t)/pi, whereas the previous basis uses sqrt(sin(pi*t)). Their literal normalization factors coincide. -/
theorem sine_eigenfunction_square (k : ℕ) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    (eigenfunction (-(1/2)) k t)^2/norming (-(1/2)) k=
      (chebyshev2.SineContinuum.upsilon k t)^2 := by
  -- The closed interval includes both singular endpoints, where both original eigenfunctions vanish.
  have hg : gamma (-(1/2))=1/2 := by norm_num [gamma]
  have hj : jacobiIndex (-(1/2))=0 := by norm_num [jacobiIndex,gamma]
  have hsin : 0≤Real.sin (Real.pi*t) :=
    Real.sin_nonneg_of_mem_Icc ⟨mul_nonneg Real.pi_pos.le ht.1,by nlinarith [Real.pi_pos,ht.2]⟩
  have hbase : 0≤Real.sin (Real.pi*t)/Real.pi := div_nonneg hsin Real.pi_pos.le
  have hweight : (weight (-(1/2)) t)^2=Real.sin (Real.pi*t)/Real.pi := by
    rw [weight,hg,← Real.sqrt_eq_rpow,Real.sq_sqrt hbase]
  rw [eigenfunction,hj,mul_pow,hweight,sine_norming,angular_legendre]
  rw [chebyshev2.SineContinuum.upsilon,mul_pow,mul_pow,
    Real.sq_sqrt (by positivity : 0≤Real.pi*((k:ℝ)+1/2)),
    chebyshev1.SineJacobi.profileWeight,Real.sq_sqrt hsin]
  field_simp

end
end jacobi.Reference
