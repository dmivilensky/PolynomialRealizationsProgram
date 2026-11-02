import jacobi.Young.SineEigenvectors

/-!
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
The explicit positive eigenvalues are strictly decreasing. Self-adjointness
makes their nonzero eigenvectors orthogonal; normalization therefore gives
actual finite orthonormal frames. The existing min--max theorem from
chebyshev2 bounds every ordered kernel eigenvalue from below.
Source: orthogonality of self-adjoint eigenvectors and the min--max principle.
Use: identifies a positive complete distinguished spectrum after trace exhaustion.
-/
namespace jacobi.Young
noncomputable section
open Real MeasureTheory jacobi.Variational chebyshev2.Continuum
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/-- The explicit target eigenvalues are all strictly positive.
Use: identifies a positive complete distinguished spectrum after trace exhaustion.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: the squared Dirichlet frequency is strictly positive. -/
theorem sineEigenvalue_pos (n : ℕ) : 0 < sineEigenvalue n :=
  div_pos (by norm_num) (sq_pos_of_pos (frequency_pos n))

/-- Target eigenvalues decrease strictly, with no multiplicities.
Use: establishes orthogonality and orders each finite min--max eigenframe.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: frequencies increase strictly, and reciprocal positive squares reverse order. -/
theorem sineEigenvalue_strictAnti : StrictAnti sineEigenvalue := by
  intro i j hij
  have hf : frequency i < frequency j := by
    unfold frequency
    exact mul_lt_mul_of_pos_left (by exact_mod_cast Nat.add_lt_add_right hij 1) Real.pi_pos
  exact div_lt_div_of_pos_left (by norm_num) (sq_pos_of_pos (frequency_pos i))
    (sq_lt_sq₀ (frequency_pos i).le (frequency_pos j).le |>.mpr hf)

/-- Distinct actual intrinsic sine eigenvectors are orthogonal.
Use: their normalized finite initial segments are min--max frames.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: self-adjointness gives (lambda_i-lambda_j) times the inner product zero;
strict decrease ensures that the scalar factor is nonzero. -/
theorem sineVector_orthogonal {i j : ℕ} (hij : i ≠ j) :
    inner ℝ (sineVector i) (sineVector j)=0 := by
  -- The spectral difference is nonzero, so self-adjointness forces the cross inner product to vanish.
  have h := (kernelOperator_positive distinguishedDensity.integrable
    distinguishedDensity.nonneg).isSymmetric (sineVector i) (sineVector j)
  change inner ℝ (kernelOperator distinguishedDensity.integrable distinguishedDensity.nonneg (sineVector i))
    (sineVector j)=inner ℝ (sineVector i)
      (kernelOperator distinguishedDensity.integrable distinguishedDensity.nonneg (sineVector j)) at h
  rw [sineVector_equation,sineVector_equation,real_inner_smul_left,real_inner_smul_right] at h
  have he := sineEigenvalue_strictAnti.injective.ne hij
  exact (mul_eq_zero.mp (show (sineEigenvalue i-sineEigenvalue j)*
    inner ℝ (sineVector i) (sineVector j)=0 by nlinarith)).resolve_left (sub_ne_zero.mpr he)

/-- Unit L2 sine eigenvectors, normalized in the actual Hilbert norm.
Use: supplies a single coherent family of finite orthonormal eigenframes.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
-/
def unitSineVector (n : ℕ) : FeatureSpace := ‖sineVector n‖⁻¹ • sineVector n

/-- The entire normalized family is orthonormal.
Use: every finite initial segment meets the hypotheses of the existing min--max theorem.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: orthogonality handles distinct indices; the squared nonzero norm cancels on the diagonal. -/
theorem unitSineVector_orthonormal : Orthonormal ℝ unitSineVector := by
  -- The normalization uses genuine nonzero L2 vectors, not formal sine symbols.
  rw [orthonormal_iff_ite]
  intro i j
  change inner ℝ (‖sineVector i‖⁻¹ • sineVector i) (‖sineVector j‖⁻¹ • sineVector j)=_
  rw [real_inner_smul_left,real_inner_smul_right]
  by_cases h : i=j
  · subst j
    rw [real_inner_self_eq_norm_sq]
    simp only [ite_true]
    field_simp [(norm_pos_iff.mpr (sineVector_ne_zero i)).ne']
  · rw [sineVector_orthogonal h]
    simp only [mul_zero,ite_false,h]

/-- Normalization preserves the actual kernel eigenvector equation.
Use: finite normalized frames provide ordered spectral lower bounds.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: linearity of the actual operator commutes with normalization. -/
theorem unitSineVector_equation (n : ℕ) :
    kernelOperator distinguishedDensity.integrable distinguishedDensity.nonneg (unitSineVector n)=
      sineEigenvalue n • unitSineVector n := by
  unfold unitSineVector
  rw [map_smul,sineVector_equation,smul_comm]

/-- Every actual sorted eigenvalue is at least its explicit sine target.
Use: equality of the known total trace will force equality in every entry.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: the first n+1 actual orthonormal eigenvectors all have eigenvalue at
least the nth target; apply the reused finite-eigenframe min--max theorem. -/
theorem sineEigenvalue_le_spectrum (n : ℕ) : sineEigenvalue n ≤ distinguishedDensity.spectrum n := by
  let v : Fin (n+1) → FeatureSpace := fun i => unitSineVector i
  have hv : Orthonormal ℝ v := unitSineVector_orthonormal.comp (fun i : Fin (n+1) => (i : ℕ))
    (fun _ _ h => Fin.ext h)
  apply eigenvalue_ge_of_eigenframe
    (kernelSpectralData distinguishedDensity.integrable distinguishedDensity.nonneg) hv
    (fun i => unitSineVector_equation i) (fun i => sineEigenvalue_strictAnti.antitone (by omega)) n
  simp

end
end jacobi.Young
