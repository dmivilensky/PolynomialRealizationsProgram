import chebyshev2.Continuum.DiagonalOperator
import chebyshev2.Continuum.SpectralMoments
import chebyshev2.GroundState.SpectralTop

/-!
Article: jacobi, Appendix D.1 (infinite-dimensional Klein inequality and Fredholm variation).
A nonnegative summable function of the actual compact spectral data is a
genuine positive trace-class operator. Its trace in every Hilbert basis
equals the same function summed over the actual sorted spectrum.
Source: the proved nuclear diagonal operator and spectral sorting invariance.
Use: the printed Fredholm pole margin controls the full eigenbasis used in functional calculus.
-/
namespace jacobi.Continuum
noncomputable section
open Real chebyshev2.Continuum
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Every eigenbasis eigenvalue is bounded by the same actual sorted top eigenvalue.
Use: the printed Fredholm pole margin controls the full eigenbasis used in functional calculus.
Article: jacobi, Appendix D.1 (infinite-dimensional Klein inequality and Fredholm variation).
Proof: evaluate the established top quadratic bound on the corresponding unit eigenbasis vector. -/
theorem eigenbasis_le_top {T : E →L[ℝ] E} (D : PositiveSpectralData T) (i : D.Index) :
    D.eig i≤D.eigenvalue 0 := by
  have h := D.top_quadratic_bound (D.basis i)
  rw [D.diagonal_eq,D.basis.orthonormal.norm_eq_one,one_pow,mul_one] at h
  exact h

/-- The genuine positive spectral function operator with its complete original eigenbasis.
Use: evaluates the regularized Fredholm logarithm as an actual trace-class operator.
Article: jacobi, Appendix D.1 (infinite-dimensional Klein inequality and Fredholm variation).
-/
def positiveFunctionData {T : E →L[ℝ] E} (D : PositiveSpectralData T) (φ : ℝ → ℝ)
    (hs : Summable (fun i => φ (D.eig i))) (hn : ∀ x,0≤x → 0≤φ x) :
    PositiveSpectralData (diagonalOperator D.basis (fun i => φ (D.eig i))) where
  -- Retain the original complete basis, including its zero eigenspace.
  Index := D.Index
  basis := D.basis
  eig i := φ (D.eig i)
  equation := diagonalOperator_basis D.basis (by simpa only [abs_of_nonneg (hn _ (D.nonneg _))] using hs.abs)
  nonneg i := hn _ (D.nonneg i)
  summable := hs

/-- The spectral function has the correct actual trace in every Hilbert basis.
Use: Klein's inequality compares spectral traces in the eigenbasis of the other actual operator.
Article: jacobi, Appendix D.1 (infinite-dimensional Klein inequality and Fredholm variation).
Proof: use the complete positive spectral function data, then the already
proved invariance of nonnegative summable moments under spectral sorting. -/
theorem positiveFunction_hasSum_trace {T : E →L[ℝ] E} (D : PositiveSpectralData T)
    (φ : ℝ → ℝ) (hφ0 : φ 0=0) (hn : ∀ x,0≤x → 0≤φ x)
    (hs : Summable (fun i => φ (D.eig i))) {ι : Type*} (b : HilbertBasis ι ℝ E) :
    HasSum (fun i => inner ℝ (b i) (diagonalOperator D.basis (fun j => φ (D.eig j)) (b i)))
      (∑' n,φ (D.eigenvalue n)) := by
  -- Both sides retain the original complete spectrum, its multiplicities and its zero eigenspace.
  have h := (positiveFunctionData D φ hs hn).hasSum_trace b
  have hm := (spectralSorted_moment D.summable D.nonneg φ hφ0 hn hs).2
  change (∑' n,φ (D.eigenvalue n))=∑' i,φ (D.eig i) at hm
  rw [hm]
  exact h

end
end jacobi.Continuum
