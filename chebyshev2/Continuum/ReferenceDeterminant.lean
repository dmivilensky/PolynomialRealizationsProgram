import chebyshev2.Continuum.Observations
import chebyshev1.Chebyshev.AmplificationLimit

/-!
Article: chebyshev2, Theorem 2.4.
The exact finite Fredholm product used in the proof of Theorem 2.4.
Use: `chebyshev2.Continuum.reference_logDeterminant` feeds
`chebyshev2.Continuum.reference_fredholmDeterminant` (The reference infinite Fredholm product
equals cosh(sqrt(s))).
-/
namespace chebyshev2.Continuum
noncomputable section
open Real Filter Polynomial Polynomial.Chebyshev
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false

/--
Exact identity `(∏ j : Fin N, (z - chebyshev1.SineJacobi.node N j)) = 2 / (2 : ℝ)^N * (T ℝ
N).eval z`.

Use: `chebyshev2.Continuum.finite_determinant_product` rewrites with this identity to
establish exact identity `(∏ j : Fin N, (1 + s / 2 * finiteEigenvalue N j)) = (T ℝ N).eval (1 +
s / (2 * (N : ℝ)^2))`.

Article: chebyshev2, Theorem 2.4 via `chebyshev2.Continuum.reference_logDeterminant`.

Proof: Use the identities/estimates `chebyshev2.SineJacobi.terminal`,
`chebyshev2.Jacobi.eigenvalue_nodeIndex`, `chebyshev2.Jacobi.matrix_isHermitian` with
the arguments shown in the proof.
-/
theorem chebyshev_node_product {N : ℕ} (hN : 0 < N) (z : ℝ) :
    (∏ j : Fin N, (z - chebyshev1.SineJacobi.node N j)) = 2 / (2 : ℝ)^N * (T ℝ N).eval z := by
  -- Use the identities/estimates `chebyshev2.SineJacobi.terminal`,
  -- `chebyshev2.Jacobi.eigenvalue_nodeIndex`, `chebyshev2.Jacobi.matrix_isHermitian`
  -- with the arguments shown in the proof.
  let J := SineJacobi.chain N
  have ht := SineJacobi.terminal N hN
  have he : (∏ j : Fin N, (z - chebyshev1.SineJacobi.node N j)) =
      ∏ i : Fin N, (z - J.basis.eigenvalues i) := by
    have h := (chebyshev1.SineJacobi.nodeIndex N hN).prod_comp (fun i => z - J.basis.eigenvalues i)
    simpa only [J.eigenvalue_nodeIndex hN ht] using h
  rw [he]
  have hp := J.matrix_isHermitian.charpoly_eq
  have hh := congrArg (fun P : ℝ[X] => P.eval z) hp
  simp only [eval_prod, eval_sub, eval_X, eval_C, RCLike.ofReal_real_eq_id, id_eq] at hh
  change J.matrix.charpoly.eval z = ∏ i : Fin N, (z - J.basis.eigenvalues i) at hh
  rw [← hh, J.charpoly_eq ht, fiberPolynomial_eq N hN]
  simp

/--
The exact finite Fredholm product used in the proof of Theorem 2.4.

Exact identity `(∏ j : Fin N, (1 + s / 2 * finiteEigenvalue N j)) = (T ℝ N).eval (1 + s / (2 *
(N : ℝ)^2))`.

Use: `chebyshev2.Continuum.finite_logDeterminant` rewrites with this identity to establish
exact identity `logDeterminant (finiteEigenvalue N) s = log ((T ℝ N).eval (1 + s / (2 * (N :
ℝ)^2)))`.

Article: chebyshev2, Theorem 2.4 via `chebyshev2.Continuum.reference_logDeterminant`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem finite_determinant_product {N : ℕ} (hN : 0 < N) (s : ℝ) :
    (∏ j : Fin N, (1 + s / 2 * finiteEigenvalue N j)) =
      (T ℝ N).eval (1 + s / (2 * (N : ℝ)^2)) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have he (j : Fin N) : 1 + s / 2 * finiteEigenvalue N j =
      (1 + s / (2 * (N : ℝ)^2) - chebyshev1.SineJacobi.node N j) / (1 - chebyshev1.SineJacobi.node N j) := by
    have ha := chebyshev1.SineJacobi.nodeAngle_mem N j
    have hj : chebyshev1.SineJacobi.node N j < 1 := by
      have h := cos_lt_cos_of_nonneg_of_le_pi (by norm_num) ha.2.le ha.1
      simpa only [cos_zero, chebyshev1.SineJacobi.node] using h
    have hd : 1 - chebyshev1.SineJacobi.node N j ≠ 0 := (sub_pos.mpr hj).ne'
    simp only [finiteEigenvalue, j.isLt, dite_eq_left, Jacobi.normalizedGreenValue_eq]
    field_simp [hd, hn]
    ring
  simp_rw [he]
  rw [Finset.prod_div_distrib, chebyshev_node_product hN, chebyshev_node_product hN]
  simp [T_eval_one]

/--
Exact identity `logDeterminant (finiteEigenvalue N) s = log ((T ℝ N).eval (1 + s / (2 * (N :
ℝ)^2)))`.

Use: `chebyshev2.Continuum.reference_logDeterminant` uses this identity to establish exact
identity `logDeterminant referenceEigenvalue s = log (cosh (sqrt s))`.

Article: chebyshev2, Theorem 2.4 via `chebyshev2.Continuum.reference_logDeterminant`.

Proof: Use the identities/estimates `chebyshev2.Continuum.finiteEigenvalue_nonneg`,
`chebyshev2.Continuum.finite_determinant_product` with the arguments shown in the proof.
-/
theorem finite_logDeterminant {N : ℕ} (hN : 0 < N) {s : ℝ} (hs : 0 ≤ s) :
    logDeterminant (finiteEigenvalue N) s = log ((T ℝ N).eval (1 + s / (2 * (N : ℝ)^2))) := by
  -- Use the identities/estimates `chebyshev2.Continuum.finiteEigenvalue_nonneg`,
  -- `chebyshev2.Continuum.finite_determinant_product` with the arguments shown in the
  -- proof.
  have he : (∑' j, log (1 + s / 2 * finiteEigenvalue N j)) =
      ∑ j : Fin N, log (1 + s / 2 * finiteEigenvalue N j) := by
    rw [tsum_eq_sum (s := Finset.range N)]
    · exact (Fin.sum_univ_eq_sum_range _ N).symm
    · intro j hj
      simp [finiteEigenvalue, show ¬j < N from fun h => hj (Finset.mem_range.mpr h)]
  have hprod := log_prod (s := Finset.univ) (f := fun j : Fin N => 1 + s / 2 * finiteEigenvalue N j)
    (fun j _ => (show 0 < 1 + s / 2 * finiteEigenvalue N j by
    have h := finiteEigenvalue_nonneg N j
    positivity).ne')
  rw [logDeterminant, he, ← hprod, finite_determinant_product hN]

/--
Convergence along the specified source filter to the specified limit: `Tendsto (fun N : ℕ => (T
ℝ N).eval (1 + s / (2 * (N : ℝ)^2))) atTop (nhds (cosh (sqrt s)))`.

Use: `chebyshev2.Continuum.reference_logDeterminant` uses this limit to establish exact
identity `logDeterminant referenceEigenvalue s = log (cosh (sqrt s))`.

Article: chebyshev2, Theorem 2.4 via `chebyshev2.Continuum.reference_logDeterminant`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Clear the denominators using the available nonzero
hypotheses, then verify the remaining algebraic identity.
-/
theorem finite_determinant_limit {s : ℝ} (hs : 0 ≤ s) :
    Tendsto (fun N : ℕ => (T ℝ N).eval (1 + s / (2 * (N : ℝ)^2))) atTop (nhds (cosh (sqrt s))) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  let u : ℕ → ℝ := fun N => (1 / (2 * (N : ℝ)))^2
  -- Record the convergence hu with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hu : Tendsto u atTop (nhds 0) := by
    have h := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const 2 |>.pow 2
    simpa [u, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using h
  -- Record the convergence hNu with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hNu : Tendsto (fun N : ℕ => (N : ℝ) * sqrt (u N)) atTop (nhds (1 / 2 : ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hn : (0 : ℝ) < N := by exact_mod_cast hN
    dsimp [u]
    rw [sqrt_sq_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * N))]
    field_simp
  have h := chebyshev1.chebyshev_small_gap_limit (N := id) (u := u) (a := 1 / 2) hs
    (Eventually.of_forall (fun N => sq_nonneg _)) hu hNu
  norm_num only [show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_mul] at h
  apply h.congr'
  exact Eventually.of_forall (fun N => by
    dsimp [u]
    congr 1
    field_simp)

/--
Exact identity `logDeterminant referenceEigenvalue s = log (cosh (sqrt s))`.

Use: `chebyshev2.Continuum.reference_fredholmDeterminant` rewrites with this identity to
establish exact identity `fredholmDeterminant referenceEigenvalue s = cosh (sqrt s)`.

Article: chebyshev2, Theorem 2.4.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem reference_logDeterminant {s : ℝ} (hs : 0 ≤ s) :
    logDeterminant referenceEigenvalue s = log (cosh (sqrt s)) := by
  -- Record the convergence hc with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hc : Tendsto (fun N : ℕ => logDeterminant (finiteEigenvalue N) s) atTop
      (nhds (log (cosh (sqrt s)))) := by
    have h := (continuousAt_log (cosh_pos _).ne').tendsto.comp (finite_determinant_limit hs)
    apply h.congr'
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact (finite_logDeterminant hN hs).symm
  have ht := tendsto_tsum_of_dominated_convergence
    (f := fun N j => log (1 + s / 2 * finiteEigenvalue N j))
    (g := fun j => log (1 + s / 2 * referenceEigenvalue j))
    (summable_dominator.mul_left (s / 2))
    (fun j => by
      have hp : 0 < 1 + s / 2 * referenceEigenvalue j := by
        have hj := referenceEigenvalue_pos j
        positivity
      exact (continuousAt_log hp.ne').tendsto.comp
        (tendsto_const_nhds.add ((finiteEigenvalue_limit j).const_mul (s / 2))))
    (Eventually.of_forall (fun N j => by
      have hp : 1 ≤ 1 + s / 2 * finiteEigenvalue N j := by
        exact le_add_of_nonneg_right (mul_nonneg (by positivity) (finiteEigenvalue_nonneg N j))
      rw [Real.norm_eq_abs, abs_of_nonneg (log_nonneg hp)]
      have hl := log_le_sub_one_of_pos (lt_of_lt_of_le zero_lt_one hp)
      have hb := mul_le_mul_of_nonneg_left (finiteEigenvalue_le N j) (by positivity : 0 ≤ s / 2)
      linarith))
  exact tendsto_nhds_unique ht hc

end
end chebyshev2.Continuum
