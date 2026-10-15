import «2610.05164v2».Green.NormalizedSpectrum
import «2610.05164v2».SineJacobi.Finite
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
Article: 2610.05164v2, Theorem 2.4.
The actual finite Green spectrum, padded with zeros.
Use: `«2610.05164v2».Continuum.reference_square_mass` feeds
`«2610.05164v2».Packing.packed_square_trace_distance` (Theorem 2.4, equation (9): the quadratic
trace observation).
Proof chain: `«2610.05164v2».Packing.packed_square_integral_distance` — 2610.05164v2, Theorem 2.4;
Uniform l1 spectral transfer, ground parameter and Fredholm/cosh observations.
-/
namespace «2610.05164v2».Continuum
noncomputable section
open Real Filter
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false

/--
The limiting spectrum in Theorem 2.4, indexed from zero.

Use: `«2610.05164v2».Continuum.finiteEigenvalue_limit` uses this definition to establish
convergence along the specified source filter to the specified limit: `Tendsto (fun N =>
finiteEigenvalue N j) atTop (nhds (referenceEigenvalue j))`.

Article: 2610.05164v2, Theorem 2.4 via
`«2610.05164v2».Continuum.finite_reference_distance_bound`.
-/
def referenceEigenvalue (j : ℕ) : ℝ := 8 / (Real.pi ^ 2 * (2 * (j : ℝ) + 1) ^ 2)

/--
The actual finite Green spectrum, padded with zeros.

Use: `«2610.05164v2».Continuum.finiteEigenvalue_angle` rewrites with this definition to
establish exact identity `finiteEigenvalue N j = 1 / (2 * (N : ℝ) ^ 2 * sin ((2 * (j : ℝ) + 1)
* Real.pi / (4 * N)) ^ 2)`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packed_spectral_distance`.
-/
def finiteEigenvalue (N j : ℕ) : ℝ :=
  if h : j < N then Jacobi.normalizedGreenValue N ⟨j, h⟩ else 0

/--
The stated quantitative bound `0 < referenceEigenvalue j`.

Use: `«2610.05164v2».Continuum.summable_reference` uses this bound to establish summability of
the displayed sequence: `Summable referenceEigenvalue`.

Article: 2610.05164v2, Theorem 2.4 via `«2610.05164v2».Continuum.reference_logDeterminant`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem referenceEigenvalue_pos (j : ℕ) : 0 < referenceEigenvalue j := by
  unfold referenceEigenvalue
  positivity

/--
Exact identity `referenceEigenvalue j = 2 / (Real.pi ^ 2 * ((j : ℝ) + 1 / 2) ^ 2)`.

Use: `«2610.05164v2».SineContinuum.mu_reference` rewrites with this identity to establish exact
identity `(mu n)⁻¹=(1/2)*Continuum.referenceEigenvalue n`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.sine_kernel_eigenvalue`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem referenceEigenvalue_eq (j : ℕ) :
    referenceEigenvalue j = 2 / (Real.pi ^ 2 * ((j : ℝ) + 1 / 2) ^ 2) := by
  unfold referenceEigenvalue
  field_simp
  ring

/--
The stated quantitative bound `0 ≤ finiteEigenvalue N j`.

Use: `«2610.05164v2».Continuum.reference_mass` rewrites with this bound to establish exact
identity `(∑' j, referenceEigenvalue j) = 1`.

Article: 2610.05164v2, Theorem 2.4 via `«2610.05164v2».Continuum.reference_logDeterminant`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem finiteEigenvalue_nonneg (N j : ℕ) : 0 ≤ finiteEigenvalue N j := by
  unfold finiteEigenvalue Jacobi.normalizedGreenValue
  split_ifs <;> positivity

/--
Exact identity `finiteEigenvalue N j = 1 / (2 * (N : ℝ) ^ 2 * sin ((2 * (j : ℝ) + 1) * Real.pi
/ (4 * N)) ^ 2)`.

Use: `«2610.05164v2».Continuum.finiteEigenvalue_bounds` rewrites with this identity to
establish the stated quantitative bound `referenceEigenvalue j ≤ finiteEigenvalue N j ∧
finiteEigenvalue N j ≤ 2 / (2 * (j : ℝ) + 1) ^ 2`.

Article: 2610.05164v2, Theorem 2.4 via `«2610.05164v2».Continuum.reference_logDeterminant`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem finiteEigenvalue_angle {N j : ℕ} (hj : j < N) :
    finiteEigenvalue N j =
      1 / (2 * (N : ℝ) ^ 2 * sin ((2 * (j : ℝ) + 1) * Real.pi / (4 * N)) ^ 2) := by simp [finiteEigenvalue, hj, Jacobi.normalizedGreenValue]

/--
Membership in the specified domain/enclosure: `(2 * (j : ℝ) + 1) * Real.pi / (4 * N) ∈ Set.Ioo
(0 : ℝ) (Real.pi / 2)`.

Use: `«2610.05164v2».Continuum.finiteEigenvalue_bounds` uses this assertion to establish the
stated quantitative bound `referenceEigenvalue j ≤ finiteEigenvalue N j ∧ finiteEigenvalue N j
≤ 2 / (2 * (j : ℝ) + 1) ^ 2`.

Article: 2610.05164v2, Theorem 2.4 via `«2610.05164v2».Continuum.reference_logDeterminant`.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
theorem angle_mem {N j : ℕ} (hj : j < N) :
    (2 * (j : ℝ) + 1) * Real.pi / (4 * N) ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hj' : (j : ℝ) + 1 ≤ N := by exact_mod_cast hj
  constructor
  · positivity
  · apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 4 * N)).mpr
    nlinarith [Real.pi_pos]

/--
The stated quantitative bound `referenceEigenvalue j ≤ finiteEigenvalue N j ∧ finiteEigenvalue
N j ≤ 2 / (2 * (j : ℝ) + 1) ^ 2`.

Use: `«2610.05164v2».Continuum.finiteEigenvalue_le` uses this bound to establish the stated
quantitative bound `finiteEigenvalue N j ≤ 2 / (2 * (j : ℝ) + 1) ^ 2`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packed_spectral_distance`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem finiteEigenvalue_bounds {N j : ℕ} (hj : j < N) :
    referenceEigenvalue j ≤ finiteEigenvalue N j ∧
      finiteEigenvalue N j ≤ 2 / (2 * (j : ℝ) + 1) ^ 2 := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  let a := (2 * (j : ℝ) + 1) * Real.pi / (4 * N)
  have ha := angle_mem hj
  change a ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) at ha
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hs : 0 < sin a := sin_pos_of_pos_of_lt_pi ha.1
    (ha.2.trans (by linarith [Real.pi_pos] : Real.pi / 2 < Real.pi))
  have hu : sin a ≤ a := sin_le ha.1.le
  have hl : 2 / Real.pi * a ≤ sin a := mul_le_sin ha.1.le ha.2.le
  rw [finiteEigenvalue_angle hj]
  change referenceEigenvalue j ≤ 1 / (2 * (N : ℝ) ^ 2 * sin a ^ 2) ∧ _
  constructor
  · unfold referenceEigenvalue
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hab : sin a ^ 2 ≤ a ^ 2 := sq_le_sq₀ hs.le ha.1.le |>.mpr hu
    dsimp [a] at hab
    field_simp at hab
    nlinarith
  · apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hab : (2 / Real.pi * a) ^ 2 ≤ sin a ^ 2 :=
      (sq_le_sq₀ (by positivity) hs.le).mpr hl
    dsimp [a] at hab
    field_simp at hab
    simp only [mul_comm (2 * (j : ℝ) + 1) Real.pi] at *
    nlinarith [sq_pos_of_pos Real.pi_pos]

/--
The stated quantitative bound `finiteEigenvalue N j ≤ 2 / (2 * (j : ℝ) + 1) ^ 2`.

Use: `«2610.05164v2».Continuum.finiteEigenvalue_le_two` uses this bound to establish the stated
quantitative bound `finiteEigenvalue N j ≤ 2`.

Article: 2610.05164v2, Theorem 2.4 via `«2610.05164v2».Continuum.reference_logDeterminant`.

Proof: Separate `j < N` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem finiteEigenvalue_le (N j : ℕ) :
    finiteEigenvalue N j ≤ 2 / (2 * (j : ℝ) + 1) ^ 2 := by
  by_cases hj : j < N
  · exact (finiteEigenvalue_bounds hj).2
  · simp only [finiteEigenvalue, dite_eq_right hj]
    positivity

/--
Convergence along the specified source filter to the specified limit: `Tendsto (fun N =>
finiteEigenvalue N j) atTop (nhds (referenceEigenvalue j))`.

Use: `«2610.05164v2».Continuum.referenceEigenvalue_le` uses this limit to establish the stated
quantitative bound `referenceEigenvalue j ≤ 2 / (2 * (j : ℝ) + 1) ^ 2`.

Article: 2610.05164v2, Theorem 2.4 via `«2610.05164v2».Continuum.reference_logDeterminant`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Clear the denominators using the available nonzero
hypotheses, then verify the remaining algebraic identity.
-/
theorem finiteEigenvalue_limit (j : ℕ) :
    Tendsto (fun N => finiteEigenvalue N j) atTop (nhds (referenceEigenvalue j)) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  let a : ℕ → ℝ := fun N => (2 * (j : ℝ) + 1) * Real.pi / (4 * N)
  -- Record the convergence ha with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have ha : Tendsto a atTop (nhds 0) := by
    have h := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
      ((2 * (j : ℝ) + 1) * Real.pi / 4)
    simpa [a, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h
  -- Record the convergence hs with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hs : Tendsto (fun N => sinc (a N)) atTop (nhds 1) := by
    simpa only [sinc_zero, Function.comp_def] using continuous_sinc.continuousAt.tendsto.comp ha
  -- Record the convergence ht with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have ht : Tendsto (fun N => referenceEigenvalue j / sinc (a N) ^ 2) atTop
      (nhds (referenceEigenvalue j)) := by
    convert (tendsto_const_nhds (x := referenceEigenvalue j)).div
      (hs.pow 2) (by norm_num : (1 : ℝ) ^ 2 ≠ 0) using 1
    simp
  apply ht.congr'
  filter_upwards [eventually_gt_atTop j] with N hN
  rw [finiteEigenvalue_angle hN, sinc_of_ne_zero (show a N ≠ 0 from (angle_mem hN).1.ne')]
  dsimp [referenceEigenvalue, a]
  field_simp
  ring

/--
Summability of the displayed sequence: `Summable (fun j : ℕ => 2 / (2 * (j : ℝ) + 1) ^ 2)`.

Use: `«2610.05164v2».Continuum.reference_mass` uses this summability result to establish exact
identity `(∑' j, referenceEigenvalue j) = 1`.

Article: 2610.05164v2, Theorem 2.4 via `«2610.05164v2».Continuum.reference_logDeterminant`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem summable_dominator : Summable (fun j : ℕ => 2 / (2 * (j : ℝ) + 1) ^ 2) := by
  have hs := (summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))).comp_injective
    (show Function.Injective (fun j : ℕ => 2 * j + 1) from fun _ _ h => by dsimp at h; omega)
  simpa [Function.comp_def, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat,
    div_eq_mul_inv] using hs.mul_left 2

/--
The stated quantitative bound `referenceEigenvalue j ≤ 2 / (2 * (j : ℝ) + 1) ^ 2`.

Use: `«2610.05164v2».Continuum.summable_reference` uses this bound to establish summability of
the displayed sequence: `Summable referenceEigenvalue`.

Article: 2610.05164v2, Theorem 2.4 via `«2610.05164v2».Packing.packed_reference_distance`.

Proof: Pass the established inequalities to the limit using the displayed filter convergence.
-/
theorem referenceEigenvalue_le (j : ℕ) :
    referenceEigenvalue j ≤ 2 / (2 * (j : ℝ) + 1) ^ 2 :=
  le_of_tendsto (finiteEigenvalue_limit j) (Eventually.of_forall (fun N => finiteEigenvalue_le N j))

/--
Summability of the displayed sequence: `Summable referenceEigenvalue`.

Use: `«2610.05164v2».Continuum.finite_reference_distance` uses this summability result to
establish exact identity `(∑' j, |finiteEigenvalue N j - referenceEigenvalue j|) = 2 * ∑' j,
referenceEigenvalue (j + N)`.

Article: 2610.05164v2, Theorem 2.4 via `«2610.05164v2».Packing.packed_reference_distance`.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.referenceEigenvalue_pos`,
`«2610.05164v2».Continuum.referenceEigenvalue_le`,
`«2610.05164v2».Continuum.summable_dominator` with the arguments shown in the proof.
-/
theorem summable_reference : Summable referenceEigenvalue :=
  summable_dominator.of_nonneg_of_le (fun j => (referenceEigenvalue_pos j).le) referenceEigenvalue_le

/--
Exact identity `(∑ j : Fin N, finiteEigenvalue N j) = 1`.

Use: `«2610.05164v2».Continuum.reference_mass` uses this identity to establish the identity
`(∑' j, referenceEigenvalue j) = 1`.

Article: 2610.05164v2, Theorem 2.4 via
`«2610.05164v2».Continuum.finite_reference_distance_bound`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem finiteEigenvalue_sum {N : ℕ} (hN : 0 < N) :
    (∑ j : Fin N, finiteEigenvalue N j) = 1 := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  let J := SineJacobi.chain N
  have ht := SineJacobi.terminal N hN
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have he : (∑ j : Fin N, finiteEigenvalue N j) =
      (∑ i : Fin N, (1 - J.basis.eigenvalues i)⁻¹) / (N : ℝ)^2 := by
    calc
      _ = ∑ j : Fin N, (1 - J.basis.eigenvalues ((«2606.16671v2».SineJacobi.nodeIndex N hN) j))⁻¹ /
          (N : ℝ)^2 := by
        apply Finset.sum_congr rfl
        intro j _
        simp only [finiteEigenvalue, j.isLt, dite_eq_left, Jacobi.normalizedGreenValue_eq,
          J.eigenvalue_nodeIndex hN ht]
      _ = _ := by
        rw [← Finset.sum_div]
        congr 1
        exact («2606.16671v2».SineJacobi.nodeIndex N hN).sum_comp (fun i => (1 - J.basis.eigenvalues i)⁻¹)
  rw [he, ← SpectralCoordinates.trace_resolvent J.basis
    (fun i => (sub_pos.mpr (J.basis_eigenvalues_lt_one hN ht i)).ne')]
  change Matrix.trace J.green / (N : ℝ)^2 = 1
  rw [J.green_trace hN ht, div_self (pow_ne_zero 2 hn)]

/--
Exact identity `(∑ j : Fin N, finiteEigenvalue N j ^ 2) = 2 / 3 + 1 / (3 * (N : ℝ)^2)`.

Use: `«2610.05164v2».Continuum.reference_square_mass` uses this identity to establish exact
identity `(∑' j, referenceEigenvalue j ^ 2) = 2 / 3`.

Article: 2610.05164v2, Theorem 2.4 via
`«2610.05164v2».Packing.packed_square_integral_distance`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral. Clear the denominators using the available nonzero hypotheses, then verify the
remaining algebraic identity.
-/
theorem finiteEigenvalue_square_sum {N : ℕ} (hN : 0 < N) :
    (∑ j : Fin N, finiteEigenvalue N j ^ 2) = 2 / 3 + 1 / (3 * (N : ℝ)^2) := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  let J := SineJacobi.chain N
  have ht := SineJacobi.terminal N hN
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have he : (∑ j : Fin N, finiteEigenvalue N j ^ 2) =
      (∑ i : Fin N, (1 - J.basis.eigenvalues i)⁻¹ ^ 2) / (N : ℝ)^4 := by
    calc
      _ = ∑ j : Fin N, (1 - J.basis.eigenvalues ((«2606.16671v2».SineJacobi.nodeIndex N hN) j))⁻¹ ^ 2 /
          (N : ℝ)^4 := by
        apply Finset.sum_congr rfl
        intro j _
        simp only [finiteEigenvalue, j.isLt, dite_eq_left, Jacobi.normalizedGreenValue_eq,
          J.eigenvalue_nodeIndex hN ht, div_pow, ← pow_mul]
      _ = _ := by
        rw [← Finset.sum_div]
        congr 1
        exact («2606.16671v2».SineJacobi.nodeIndex N hN).sum_comp (fun i => (1 - J.basis.eigenvalues i)⁻¹ ^ 2)
  rw [he, ← SpectralCoordinates.trace_resolvent_square J.basis
    (fun i => (sub_pos.mpr (J.basis_eigenvalues_lt_one hN ht i)).ne')]
  change Matrix.trace (J.green * J.green) / (N : ℝ)^4 = _
  rw [J.green_trace_square hN ht]
  field_simp [hn]

/--
Exact identity `(∑' j, finiteEigenvalue N j ^ (p + 1)) = ∑ j : Fin N, finiteEigenvalue N j ^ (p
+ 1)`.

Use: `«2610.05164v2».Continuum.reference_mass` uses this identity to establish the identity
`(∑' j, referenceEigenvalue j) = 1`.

Article: 2610.05164v2, Theorem 2.4 via
`«2610.05164v2».Continuum.finite_reference_distance_bound`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem finiteEigenvalue_tsum (N : ℕ) (p : ℕ) :
    (∑' j, finiteEigenvalue N j ^ (p + 1)) = ∑ j : Fin N, finiteEigenvalue N j ^ (p + 1) := by
  rw [tsum_eq_sum (s := Finset.range N)]
  · exact (Fin.sum_univ_eq_sum_range _ N).symm
  · intro j hj
    simp [finiteEigenvalue, show ¬j < N from fun h => hj (Finset.mem_range.mpr h)]

/--
Exact identity `(∑' j, referenceEigenvalue j) = 1`.

Use: `«2610.05164v2».Continuum.finite_reference_distance` rewrites with this identity to
establish exact identity `(∑' j, |finiteEigenvalue N j - referenceEigenvalue j|) = 2 * ∑' j,
referenceEigenvalue (j + N)`.

Article: 2610.05164v2, Theorem 2.4 via
`«2610.05164v2».Continuum.finite_reference_distance_bound`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem reference_mass : (∑' j, referenceEigenvalue j) = 1 := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  have ht := tendsto_tsum_of_dominated_convergence summable_dominator finiteEigenvalue_limit
    (Eventually.of_forall (fun N j => by
      rw [Real.norm_eq_abs, abs_of_nonneg (finiteEigenvalue_nonneg N j)]
      exact finiteEigenvalue_le N j))
  -- Record the convergence he with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have he : Tendsto (fun N => ∑' j, finiteEigenvalue N j) atTop (nhds (1 : ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop 0] with N hN
    have h := finiteEigenvalue_tsum N 0
    simp only [Nat.zero_add, pow_one] at h
    exact (h.trans (finiteEigenvalue_sum hN)).symm
  exact tendsto_nhds_unique ht he

/--
The stated quantitative bound `finiteEigenvalue N j ≤ 2`.

Use: `«2610.05164v2».Continuum.reference_square_mass` uses this bound to establish exact
identity `(∑' j, referenceEigenvalue j ^ 2) = 2 / 3`.

Article: 2610.05164v2, Theorem 2.4 via
`«2610.05164v2».Packing.packed_square_integral_distance`.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.finiteEigenvalue_le` with the
arguments shown in the proof.
-/
theorem finiteEigenvalue_le_two (N j : ℕ) : finiteEigenvalue N j ≤ 2 := by
  apply (finiteEigenvalue_le N j).trans
  apply div_le_self (by norm_num)
  nlinarith [Nat.cast_nonneg (α := ℝ) j]

/--
Exact identity `(∑' j, referenceEigenvalue j ^ 2) = 2 / 3`.

Use: `«2610.05164v2».Packing.packed_square_trace_distance` rewrites with this identity to
establish the stated quantitative bound `|(∑' j, packedEigenvalue J hN ht j^2)-(2/3 : ℝ)| ≤
2*transferError N`.

Article: 2610.05164v2, Theorem 2.4 via
`«2610.05164v2».Packing.packed_square_integral_distance`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem reference_square_mass : (∑' j, referenceEigenvalue j ^ 2) = 2 / 3 := by
  -- Prove the summability hb needed for the later infinite-sum manipulations.
  have hb : Summable (fun j : ℕ => 4 / (2 * (j : ℝ) + 1)^2) := by
    convert summable_dominator.mul_left 2 using 1
    ext j
    ring
  have ht := tendsto_tsum_of_dominated_convergence hb (fun j => (finiteEigenvalue_limit j).pow 2)
    (Eventually.of_forall (fun N j => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      calc
        finiteEigenvalue N j ^ 2 ≤ 2 * finiteEigenvalue N j := by
          nlinarith [finiteEigenvalue_nonneg N j, finiteEigenvalue_le_two N j]
        _ ≤ 4 / (2 * (j : ℝ) + 1)^2 := by
          convert mul_le_mul_of_nonneg_left (finiteEigenvalue_le N j) (by norm_num : (0 : ℝ) ≤ 2)
            using 1
          ring))
  -- Record the convergence hzero with its source filter and target limit before taking limits
  -- in the subsequent identities/bounds.
  have hzero : Tendsto (fun N : ℕ => 1 / (3 * (N : ℝ)^2)) atTop (nhds (0 : ℝ)) := by
    have h := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2 |>.div_const 3
    simpa [div_pow, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
  -- Record the convergence he with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have he : Tendsto (fun N => ∑' j, finiteEigenvalue N j ^ 2) atTop (nhds (2 / 3 : ℝ)) := by
    -- Record the convergence hh with its source filter and target limit before taking limits
    -- in the subsequent identities/bounds.
    have hh : Tendsto (fun N : ℕ => (2 / 3 : ℝ) + 1 / (3 * (N : ℝ)^2)) atTop
        (nhds (2 / 3 : ℝ)) := by simpa using (tendsto_const_nhds (x := (2 / 3 : ℝ))).add hzero
    apply hh.congr'
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact ((finiteEigenvalue_tsum N 1).trans (finiteEigenvalue_square_sum hN)).symm
  exact tendsto_nhds_unique ht he

end
end «2610.05164v2».Continuum
