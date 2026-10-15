import «2610.05164v2».Green.Energy
import «2610.05164v2».Green.SpectralCoordinates

/-!
Article: 2610.05164v2, Theorem A.1.
The second spectral identity of Lemma 1, throughout the complete fiber.
Use: `«2610.05164v2».Jacobi.green_trace_square` feeds
`«2610.05164v2».Continuum.finiteEigenvalue_square_sum` (finite Eigenvalue square sum).
-/
namespace «2610.05164v2».Jacobi
noncomputable section
open «2606.16671v2» Polynomial Polynomial.Chebyshev Filter
open scoped BigOperators Topology
variable {N : ℕ} (J : Jacobi N)

/--
A resolvent trace identity obtained by differentiating the logarithmic derivative of the actual
characteristic polynomial.

Exact identity `Matrix.trace (J.green*J.green) = (J.matrix.charpoly.derivative.eval
1/J.matrix.charpoly.eval 1)^2 - J.matrix.charpoly.derivative.derivative.eval
1/J.matrix.charpoly.eval 1`.

Use: `«2610.05164v2».Jacobi.green_trace_square` rewrites with this identity to establish exact
identity `Matrix.trace (J.green*J.green) = (2*(N:ℝ)^4+(N:ℝ)^2)/3`.

Article: 2610.05164v2, Theorem A.1 via `«2610.05164v2».Jacobi.green_trace_square`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Clear the denominators using the available nonzero
hypotheses, then verify the remaining algebraic identity.
-/
theorem green_trace_square_logDerivative (hN : 0 < N) (ht : J.Terminal) :
    Matrix.trace (J.green*J.green) =
      (J.matrix.charpoly.derivative.eval 1/J.matrix.charpoly.eval 1)^2 -
        J.matrix.charpoly.derivative.derivative.eval 1/J.matrix.charpoly.eval 1 := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  let hM := J.matrix_isHermitian
  let eigs := hM.eigenvalues
  let P := J.matrix.charpoly
  have hp : P.eval 1 ≠ 0 := by
    change J.matrix.charpoly.eval 1 ≠ 0
    rw [J.charpoly_eq ht, ← ht]
    exact (J.leading_endpoint_pos hN ht).ne'
  have heigs : ∀ i, 1-eigs i ≠ 0 := by
    intro i
    exact (sub_pos.mpr ((J.spectrum_subset_open hN ht)
      (hM.eigenvalues_mem_spectrum_real i)).2).ne'
  have hlog (x : ℝ) (hx : P.eval x ≠ 0) :
      P.derivative.eval x/P.eval x = ∑ i, 1/(x-eigs i) := by
    have he := hM.splits_charpoly.eval_derivative_div_eval_of_ne_zero hx
    rw [hM.roots_charpoly_eq_eigenvalues] at he
    simpa [Multiset.map_map, Function.comp_def, Finset.sum, P, eigs] using he
  have he : (fun x => ∑ i, 1/(x-eigs i)) =ᶠ[nhds (1:ℝ)]
      (fun x => P.derivative.eval x/P.eval x) := by
    filter_upwards [P.continuous.continuousAt.eventually_ne hp] with x hx
    exact (hlog x hx).symm
  have hd := ((P.derivative.hasDerivAt 1).div (P.hasDerivAt 1) hp).congr_of_eventuallyEq he
  have hd' : HasDerivAt (fun x => ∑ i, 1/(x-eigs i))
      (∑ i, -(1-eigs i)⁻¹^2) 1 := by
    have hh (i : Fin N) : HasDerivAt (fun x : ℝ => 1/(x-eigs i)) (-(1-eigs i)⁻¹^2) 1 := by
      convert (hasDerivAt_const (1:ℝ) (1:ℝ)).div
        ((hasDerivAt_id (1:ℝ)).sub_const (eigs i)) (heigs i) using 1
      · rfl
      · simp [div_eq_mul_inv, inv_pow]
    exact HasDerivAt.fun_sum (fun i (_ : i ∈ Finset.univ) => hh i)
  have hu := hd.unique hd'
  rw [Finset.sum_neg_distrib] at hu
  have hs := SpectralCoordinates.trace_resolvent_square (SpectralBasis.ofHermitian J.matrix hM) heigs
  change Matrix.trace (J.green*J.green) = ∑ i, (1-eigs i)⁻¹^2 at hs
  rw [hs]
  change (∑ i, (1-eigs i)⁻¹^2) = (P.derivative.eval 1/P.eval 1)^2-
    P.derivative.derivative.eval 1/P.eval 1
  field_simp [hp] at hu ⊢
  linarith [hu]

/--
The second spectral identity of Lemma 1, throughout the complete fiber.

Exact identity `Matrix.trace (J.green*J.green) = (2*(N:ℝ)^4+(N:ℝ)^2)/3`.

Use: `«2610.05164v2».Continuum.finiteEigenvalue_square_sum` rewrites with this identity to
establish exact identity `(∑ j : Fin N, finiteEigenvalue N j ^ 2) = 2 / 3 + 1 / (3 * (N :
ℝ)^2)`.

Article: 2610.05164v2, Theorem A.1.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem green_trace_square (hN : 0 < N) (ht : J.Terminal) :
    Matrix.trace (J.green*J.green) = (2*(N:ℝ)^4+(N:ℝ)^2)/3 := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  rw [J.green_trace_square_logDerivative hN ht, J.charpoly_eq ht, fiberPolynomial_eq N hN]
  have hT : (T ℝ N).derivative.derivative.eval 1 =
      (N:ℝ)^2*((N:ℝ)^2-1)/3 := by
    have hh := iterate_derivative_T_eval_one_eq_div (𝔽 := ℝ) N 2
    simpa [Finset.prod_range_succ, Function.iterate_succ_apply'] using hh
  simp only [derivative_mul, derivative_C, zero_mul, zero_add, eval_mul, eval_C,
    T_eval_one, mul_one, derivative_T_eval_one, hT, Int.cast_natCast]
  field_simp
  ring

end
end «2610.05164v2».Jacobi
