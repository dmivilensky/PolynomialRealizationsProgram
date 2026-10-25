import chebyshev1.SineJacobi.SpectralMeasure
import chebyshev1.Jacobi.Orthogonality

/-!
Article: chebyshev1, Lemma E.2.
E.2's monic orthogonality, derived from the explicit chain and its actual spectral weights.
Result: `chebyshev1.SineJacobi.leading_norm_positive` supplies the stated article conclusion.
-/
namespace chebyshev1.SineJacobi
noncomputable section
open Polynomial
open scoped BigOperators

/--
The first spectral measure of the explicit sine chain acts on every polynomial as the discrete
sine measure in E.2.

Exact identity `(aeval ((data N).matrix 0 N) p) (⟨0,hN⟩ : Fin N) (⟨0,hN⟩ : Fin N) = ∑ j : Fin
N, sineWeight N j*p.eval (node N j)`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev1, Lemma E.2.

Proof: Use the identities/estimates `chebyshev1.JacobiData.matrix_isHermitian`,
`chebyshev1.SpectralBasis.moment`, `chebyshev1.SineJacobi.spectral_weight` with the
arguments shown in the proof.
-/
theorem spectral_moment (N : ℕ) (hN : 0 < N) (p : ℝ[X]) :
    (aeval ((data N).matrix 0 N) p) (⟨0,hN⟩ : Fin N) (⟨0,hN⟩ : Fin N) =
      ∑ j : Fin N, sineWeight N j*p.eval (node N j) := by
  -- Use the identities/estimates `chebyshev1.JacobiData.matrix_isHermitian`,
  -- `chebyshev1.SpectralBasis.moment`, `chebyshev1.SineJacobi.spectral_weight` with
  -- the arguments shown in the proof.
  rw [SpectralBasis.moment p (JacobiData.matrix_isHermitian _ 0 N)]
  change (∑ j : Fin N, (basis N).weight (⟨0,hN⟩ : Fin N) j*p.eval ((basis N).eigenvalues j)) = _
  rw [← (nodeIndex N hN).sum_comp]
  simp only [spectral_weight N hN, eigenvalue_nodeIndex]

/--
E.2's monic orthogonality, derived from the explicit chain and its actual spectral weights.

Exact identity `∑ j : Fin N, sineWeight N j*((data N).leading s).eval (node N j)* ((data
N).leading t).eval (node N j) = if s = t then ((data N).linkProduct s)^2 else 0`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev1, Lemma E.2.

Proof: Use the identities/estimates `chebyshev1.JacobiData.leading_orthogonality`,
`chebyshev1.SineJacobi.data_aSq_nonneg`, `chebyshev1.SineJacobi.spectral_weight` with
the arguments shown in the proof.
-/
theorem leading_orthogonality (N s t : ℕ) (hN : 0 < N) (hs : s < N) (ht : t < N) :
    ∑ j : Fin N, sineWeight N j*((data N).leading s).eval (node N j)*
      ((data N).leading t).eval (node N j) =
        if s = t then ((data N).linkProduct s)^2 else 0 := by
  -- Use the identities/estimates `chebyshev1.JacobiData.leading_orthogonality`,
  -- `chebyshev1.SineJacobi.data_aSq_nonneg`, `chebyshev1.SineJacobi.spectral_weight`
  -- with the arguments shown in the proof.
  have hh := (data N).leading_orthogonality N s t hN hs ht (data_aSq_nonneg N)
  change (∑ j : Fin N, (basis N).weight (⟨0,hN⟩ : Fin N) j*
    ((data N).leading s).eval ((basis N).eigenvalues j)*
      ((data N).leading t).eval ((basis N).eigenvalues j)) = _ at hh
  rw [← (nodeIndex N hN).sum_comp] at hh
  simpa only [spectral_weight N hN, eigenvalue_nodeIndex] using hh

/--
The precise assertion is `((data N).leading s).Monic`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev1, Lemma E.2.

Proof: Use the identities/estimates `chebyshev1.JacobiData.block_monic`,
`chebyshev1.SineJacobi.data_aSq_nonneg` with the arguments shown in the proof.
-/
theorem leading_monic (N s : ℕ) : ((data N).leading s).Monic :=
  (data N).block_monic (data_aSq_nonneg N) 0 s

/--
Exact identity `((data N).leading s).natDegree = s`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev1, Lemma E.2.

Proof: Use the identities/estimates `chebyshev1.JacobiData.block_natDegree`,
`chebyshev1.SineJacobi.data_aSq_nonneg` with the arguments shown in the proof.
-/
theorem leading_degree (N s : ℕ) : ((data N).leading s).natDegree = s :=
  (data N).block_natDegree (data_aSq_nonneg N) 0 s

/--
The stated quantitative bound `0 < ((data N).linkProduct s)^2`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev1, Lemma E.2.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.data_aSq`,
`chebyshev1.SineJacobi.couplingSq_pos` with the arguments shown in the proof.
-/
theorem leading_norm_positive (N s : ℕ) (hs : s < N) : 0 < ((data N).linkProduct s)^2 := by
  -- Use the identities/estimates `chebyshev1.SineJacobi.data_aSq`,
  -- `chebyshev1.SineJacobi.couplingSq_pos` with the arguments shown in the proof.
  apply sq_pos_of_pos
  unfold JacobiData.linkProduct
  apply Finset.prod_pos
  intro t ht
  apply Real.sqrt_pos.mpr
  have htN : t+1 < N := by have := Finset.mem_range.mp ht; omega
  rw [data_aSq N (t+1) (by omega) htN]
  exact couplingSq_pos N (t+1) (by omega) htN

end
end chebyshev1.SineJacobi
