import chebyshev1.Background.FiniteFavard

/-! Explicit public signatures for the signed endpoint formula used in the article. -/
namespace chebyshev1.Background
noncomputable section

theorem signed_endpoint_residue {n : ℕ} (J : chebyshev2.Jacobi (n+1))
    (B : SpectralBasis J.matrix) (k : Fin (n+1)) :
    B.Q 0 k * B.Q (Fin.last n) k * J.matrix.charpoly.derivative.eval (B.eigenvalues k) =
      ∏ i : Fin n, Real.sqrt (J.data.aSq (i.val+1)) :=
  jacobi.Finite.spectral_endpoint_signed J B k

theorem endpoint_adjugate {n : ℕ} (J : chebyshev2.Jacobi (n+1)) (x : ℝ) :
    (Matrix.scalar _ x-J.matrix).adjugate 0 (Fin.last n) =
      ∏ i : Fin n, Real.sqrt (J.data.aSq (i.val+1)) :=
  jacobi.Finite.endpoint_adjugate J x

end
end chebyshev1.Background
