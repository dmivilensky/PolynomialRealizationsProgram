import chebyshev2.Finite.Basic
import chebyshev1.Jacobi.SpectralWeights

/-!
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
Finite Jacobi data, resolvent energy and the inverse spectral weight criterion
are imported from chebyshev2 and chebyshev1.

Use: these are the existing finite-dimensional ingredients for the arbitrary
polynomial fibre, reversal and Appendix C.4 arguments in jacobi. In particular,
the type chebyshev2.Jacobi and its matrix, green and energy definitions do not
fix the spectrum. Its separate Terminal predicate fixes a Chebyshev polynomial
and must not serve as the arbitrary-polynomial fibre condition here.

The existing persymmetric_iff_spectral_weights theorem supplies the weight
criterion for an already given irreducible matrix. Existence of a matrix for
arbitrary positive spectral weights still requires spectral reconstruction.
-/
