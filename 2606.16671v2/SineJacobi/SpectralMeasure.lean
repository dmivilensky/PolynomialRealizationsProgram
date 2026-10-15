import «2606.16671v2».SineJacobi.Reversal
import «2606.16671v2».Jacobi.SpectralWeights

/-!
Article: 2606.16671v2, Theorem E.1.
The explicit finite chain has exactly the sine spectral weights used in the paper.
Use: `«2606.16671v2».SineJacobi.spectral_weight` feeds
`«2606.16671v2».SineJacobi.leading_orthogonality` (E.2's monic orthogonality, derived from the
explicit chain and its actual spectral weights).
-/
namespace «2606.16671v2».SineJacobi
noncomputable section
open Polynomial Real
open Polynomial.Chebyshev (T U)
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false

/--
Defines `nodeAngle` of type `ℝ` by `(2*(j:ℝ)+1)*π/(2*(N:ℝ))`.

Use: `«2606.16671v2».SineJacobi.node` uses this definition in the displayed construction of
`node`. Its inputs and component formulas are fixed by that definition.

Article: 2606.16671v2, Theorem E.1 via `«2606.16671v2».SineJacobi.spectral_weight`.
-/
def nodeAngle (N : ℕ) (j : Fin N) : ℝ := (2*(j:ℝ)+1)*π/(2*(N:ℝ))
/--
Defines `node` of type `ℝ` by `cos (nodeAngle N j)`.

Use: `«2606.16671v2».SineJacobi.node_has_eigenvalue` uses this definition to establish
constructs witnesses with the exact properties `∃ k : Fin N, (basis N).eigenvalues k = node N
j`.

Article: 2606.16671v2, Theorem E.1 via `«2606.16671v2».SineJacobi.spectral_weight`.
-/
def node (N : ℕ) (j : Fin N) : ℝ := cos (nodeAngle N j)
/--
Defines `sineWeight` of type `ℝ` by `sin (nodeAngle N j)/(∑ k : Fin N, sin (nodeAngle N k))`.

Use: `«2606.16671v2».SineJacobi.sineWeight_reverse` rewrites with this definition to establish
exact identity `sineWeight N j.rev = sineWeight N j`.

Article: 2606.16671v2, Theorem E.1 via `«2606.16671v2».SineJacobi.spectral_weight`.
-/
def sineWeight (N : ℕ) (j : Fin N) : ℝ := sin (nodeAngle N j)/(∑ k : Fin N, sin (nodeAngle N k))

/--
Defines `basis` of type `SpectralBasis ((data N).matrix 0 N)` by `SpectralBasis.ofHermitian _
(JacobiData.matrix_isHermitian _ 0 N)`.

Use: `«2606.16671v2».SineJacobi.basis_eigenvalues_injective` uses this definition to establish
the precise assertion is `Function.Injective (basis N).eigenvalues`.

Article: 2606.16671v2, Theorem E.1 via `«2606.16671v2».SineJacobi.spectral_weight`.
-/
def basis (N : ℕ) : SpectralBasis ((data N).matrix 0 N) :=
  SpectralBasis.ofHermitian _ (JacobiData.matrix_isHermitian _ 0 N)

/--
Membership in the specified domain/enclosure: `nodeAngle N j ∈ Set.Ioo (0:ℝ) π`.

Use: `«2606.16671v2».SineJacobi.node_sin_pos` uses this assertion to establish the stated
quantitative bound `0 < sin (nodeAngle N j)`.

Article: 2606.16671v2, Theorem E.1 via `«2606.16671v2».SineJacobi.spectral_weight`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem nodeAngle_mem (N : ℕ) (j : Fin N) : nodeAngle N j ∈ Set.Ioo (0:ℝ) π := by
  have hn : (0:ℝ) < N := by exact_mod_cast (show 0 < N by have := j.isLt; omega)
  have hj : (j:ℝ)+1 ≤ N := by exact_mod_cast j.isLt
  constructor
  · unfold nodeAngle; positivity
  · unfold nodeAngle
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [pi_pos]

/--
The stated quantitative bound `0 < sin (nodeAngle N j)`.

Use: `«2606.16671v2».SineJacobi.sineWeight_pos` uses this bound to establish the stated
quantitative bound `0 < sineWeight N j`.

Article: 2606.16671v2, Theorem E.1 via `«2606.16671v2».SineJacobi.spectral_weight`.

Proof: Use the identities/estimates `«2606.16671v2».SineJacobi.nodeAngle_mem` with the
arguments shown in the proof.
-/
theorem node_sin_pos (N : ℕ) (j : Fin N) : 0 < sin (nodeAngle N j) :=
  sin_pos_of_mem_Ioo (nodeAngle_mem N j)

/--
Exact identity `(N:ℝ)*nodeAngle N j = π/2+(j:ℝ)*π`.

Use: `«2606.16671v2».SineJacobi.node_frequency_sin_abs` rewrites with this identity to
establish exact identity `|sin ((N:ℝ)*nodeAngle N j)| = 1`.

Article: 2606.16671v2, Theorem E.1 via `«2606.16671v2».SineJacobi.spectral_weight`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem nodeAngle_frequency (N : ℕ) (j : Fin N) :
    (N:ℝ)*nodeAngle N j = π/2+(j:ℝ)*π := by
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by have := j.isLt; omega)
  unfold nodeAngle
  field_simp
  ring

/--
Exact identity `|sin ((N:ℝ)*nodeAngle N j)| = 1`.

Use: `«2606.16671v2».SineJacobi.terminal_derivative_abs` rewrites with this identity to
establish exact identity `|((data N).leading N).derivative.eval (node N j)| =
(2/(2:ℝ)^N)*(N:ℝ)/sin (nodeAngle N j)`.

Article: 2606.16671v2, Theorem E.1 via `«2606.16671v2».SineJacobi.spectral_weight`.

Proof: Use the identities/estimates `«2606.16671v2».SineJacobi.nodeAngle_frequency` with the
arguments shown in the proof.
-/
theorem node_frequency_sin_abs (N : ℕ) (j : Fin N) :
    |sin ((N:ℝ)*nodeAngle N j)| = 1 := by
  rw [nodeAngle_frequency, sin_add_nat_mul_pi]
  simp [abs_pow]

/--
Exact identity `|((data N).leading N).derivative.eval (node N j)| = (2/(2:ℝ)^N)*(N:ℝ)/sin
(nodeAngle N j)`.

Use: `«2606.16671v2».SineJacobi.spectral_weight` rewrites with this identity to establish exact
identity `(basis N).weight (⟨0,hN⟩ : Fin N) (nodeIndex N hN j) = sineWeight N j`.

Article: 2606.16671v2, Theorem E.1 via `«2606.16671v2».SineJacobi.spectral_weight`.

Proof: Use the identities/estimates `«2606.16671v2».SineJacobi.terminal`,
`«2606.16671v2».SineJacobi.node_sin_pos`, `«2606.16671v2».SineJacobi.node_frequency_sin_abs`
with the arguments shown in the proof.
-/
theorem terminal_derivative_abs (N : ℕ) (hN : 0 < N) (j : Fin N) :
    |((data N).leading N).derivative.eval (node N j)| =
      (2/(2:ℝ)^N)*(N:ℝ)/sin (nodeAngle N j) := by
  -- Use the identities/estimates `«2606.16671v2».SineJacobi.terminal`,
  -- `«2606.16671v2».SineJacobi.node_sin_pos`,
  -- `«2606.16671v2».SineJacobi.node_frequency_sin_abs` with the arguments shown in the proof.
  have hu := Polynomial.Chebyshev.U_real_cos (nodeAngle N j) ((N:ℤ)-1)
  simp only [Int.cast_sub, Int.cast_natCast, Int.cast_one, sub_add_cancel] at hu
  have hh : ((data N).leading N).derivative.eval (node N j)*sin (nodeAngle N j) =
      (2/(2:ℝ)^N)*(N:ℝ)*sin ((N:ℝ)*nodeAngle N j) := by
    rw [terminal N hN, derivative_mul]
    simp only [derivative_C, zero_mul, zero_add, Polynomial.Chebyshev.T_derivative_eq_U,
      eval_mul, eval_C, Int.cast_natCast, eval_natCast, node]
    linear_combination (2/(2:ℝ)^N)*(N:ℝ)*hu
  have hp2 : 0 < (2/(2:ℝ)^N) := by positivity
  have hnR : (0:ℝ) < N := by exact_mod_cast hN
  have habs := congrArg abs hh
  rw [abs_mul, abs_of_pos (node_sin_pos N j), abs_mul, abs_mul,
    abs_of_pos hp2, abs_of_pos hnR, node_frequency_sin_abs, mul_one] at habs
  exact (eq_div_iff (ne_of_gt (node_sin_pos N j))).mpr habs

/--
The precise assertion is `((data N).leading N).derivative.eval (node N j) ≠ 0`.

Use: `«2606.16671v2».SineJacobi.basis_eigenvalues_injective` uses this assertion to establish
the precise assertion is `Function.Injective (basis N).eigenvalues`.

Article: 2606.16671v2, Theorem E.1 via `«2606.16671v2».SineJacobi.spectral_weight`.

Proof: Use the identities/estimates `«2606.16671v2».SineJacobi.terminal_derivative_abs`,
`«2606.16671v2».SineJacobi.node_sin_pos` with the arguments shown in the proof.
-/
theorem terminal_derivative_node_ne (N : ℕ) (hN : 0 < N) (j : Fin N) :
    ((data N).leading N).derivative.eval (node N j) ≠ 0 := by
  apply abs_ne_zero.mp
  rw [terminal_derivative_abs N hN]
  exact ne_of_gt (div_pos (mul_pos (div_pos (by norm_num) (pow_pos (by norm_num) N))
    (by exact_mod_cast hN)) (node_sin_pos N j))

/--
The precise assertion is `Function.Injective (node N)`.

Use: `«2606.16671v2».SineJacobi.nodeIndex` uses this assertion in the displayed construction of
`nodeIndex`. Its inputs and component formulas are fixed by that definition.

Article: 2606.16671v2, Theorem E.1 via `«2606.16671v2».SineJacobi.spectral_weight`.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
theorem node_injective (N : ℕ) : Function.Injective (node N) := by
  have hi := (Finset.range N).nodup_map_iff_injOn.mp (Polynomial.Chebyshev.roots_T_real_nodup N)
  intro i j he
  apply Fin.ext
  exact hi (Finset.mem_range.mpr i.isLt) (Finset.mem_range.mpr j.isLt) he

/--
Constructs witnesses with the exact properties `∃ k : Fin N, node N k = (basis N).eigenvalues
j`.

Use: `«2606.16671v2».SineJacobi.basis_eigenvalues_injective` uses this identity to establish
the precise assertion is `Function.Injective (basis N).eigenvalues`.

Article: 2606.16671v2, Theorem E.1 via `«2606.16671v2».SineJacobi.spectral_weight`.

Proof: Use the identities/estimates `«2606.16671v2».JacobiData.matrix_isHermitian`,
`«2606.16671v2».SineJacobi.spectrum_eq_nodes` with the arguments shown in the proof.
-/
theorem basis_eigenvalue_is_node (N : ℕ) (hN : 0 < N) (j : Fin N) :
    ∃ k : Fin N, node N k = (basis N).eigenvalues j := by
  have hs := (JacobiData.matrix_isHermitian (data N) 0 N).eigenvalues_mem_spectrum_real j
  rw [spectrum_eq_nodes N hN] at hs
  exact hs

/--
The precise assertion is `Function.Injective (basis N).eigenvalues`.

Use: `«2606.16671v2».SineJacobi.spectral_weight` uses this assertion to establish exact
identity `(basis N).weight (⟨0,hN⟩ : Fin N) (nodeIndex N hN j) = sineWeight N j`.

Article: 2606.16671v2, Theorem E.1 via `«2606.16671v2».SineJacobi.spectral_weight`.

Proof: Assume the failure of the desired conclusion and derive a contradiction from the
available bounds/identities.
-/
theorem basis_eigenvalues_injective (N : ℕ) (hN : 0 < N) :
    Function.Injective (basis N).eigenvalues := by
  -- Assume the failure of the desired conclusion and derive a contradiction from the available
  -- bounds/identities.
  intro i j he
  by_contra hij
  obtain ⟨k,hk⟩ := basis_eigenvalue_is_node N hN i
  have hd : (((data N).matrix 0 N).charpoly).derivative.eval ((basis N).eigenvalues i) ≠ 0 := by
    rw [← JacobiData.block_eq_charpoly _ (data_aSq_nonneg N), ← JacobiData.leading, ← hk]
    exact terminal_derivative_node_ne N hN k
  apply hd
  rw [SpectralBasis.charpoly_derivative]
  exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩)
    (sub_eq_zero.mpr he)

/--
Constructs witnesses with the exact properties `∃ k : Fin N, (basis N).eigenvalues k = node N
j`.

Use:
`_private.«2606.16671v2».SineJacobi.SpectralMeasure.0.«2606.16671v2».SineJacobi.nodeIndexFun`
uses this identity in the displayed construction of `nodeIndexFun`. Its inputs and component
formulas are fixed by that definition.

Article: 2606.16671v2, Theorem E.1 via `«2606.16671v2».SineJacobi.spectral_weight`.

Proof: Use the identities/estimates `«2606.16671v2».SineJacobi.spectrum_eq_nodes`,
`«2606.16671v2».JacobiData.matrix_isHermitian` with the arguments shown in the proof.
-/
theorem node_has_eigenvalue (N : ℕ) (hN : 0 < N) (j : Fin N) :
    ∃ k : Fin N, (basis N).eigenvalues k = node N j := by
  have hs : node N j ∈ spectrum ℝ ((data N).matrix 0 N) := by
    rw [spectrum_eq_nodes N hN]; exact ⟨j,rfl⟩
  rw [(JacobiData.matrix_isHermitian (data N) 0 N).spectrum_real_eq_range_eigenvalues] at hs
  exact hs

/--
Defines `nodeIndexFun` of type `Fin N` by `Classical.choose (node_has_eigenvalue N hN j)`.

Use: `«2606.16671v2».SineJacobi.nodeIndex` uses this definition in the displayed construction
of `nodeIndex`. Its inputs and component formulas are fixed by that definition.

Article: 2606.16671v2, Theorem E.1 via `«2606.16671v2».SineJacobi.spectral_weight`.
-/
private def nodeIndexFun (N : ℕ) (hN : 0 < N) (j : Fin N) : Fin N :=
  Classical.choose (node_has_eigenvalue N hN j)

/--
Exact identity `(basis N).eigenvalues (nodeIndexFun N hN j) = node N j`.

Use: `«2606.16671v2».SineJacobi.eigenvalue_nodeIndex` uses this identity to establish exact
identity `(basis N).eigenvalues (nodeIndex N hN j) = node N j`.

Article: 2606.16671v2, Theorem E.1 via `«2606.16671v2».SineJacobi.spectral_weight`.

Proof: Use the identities/estimates `«2606.16671v2».SineJacobi.node_has_eigenvalue` with the
arguments shown in the proof.
-/
private theorem nodeIndexFun_spec (N : ℕ) (hN : 0 < N) (j : Fin N) :
    (basis N).eigenvalues (nodeIndexFun N hN j) = node N j :=
  Classical.choose_spec (node_has_eigenvalue N hN j)

/--
Match the spectral theorem's enumeration with the article's half-grid nodes.

Use: `«2606.16671v2».SineJacobi.spectral_weight` rewrites with this definition to establish
exact identity `(basis N).weight (⟨0,hN⟩ : Fin N) (nodeIndex N hN j) = sineWeight N j`.

Article: 2606.16671v2, Theorem E.1 via `«2606.16671v2».SineJacobi.spectral_weight`.
-/
def nodeIndex (N : ℕ) (hN : 0 < N) : Fin N ≃ Fin N :=
  Equiv.ofBijective (nodeIndexFun N hN) (by
    have hi : Function.Injective (nodeIndexFun N hN) := by
      intro i j he
      apply node_injective N
      rw [← nodeIndexFun_spec N hN i, ← nodeIndexFun_spec N hN j, he]
    exact ⟨hi, (Finite.injective_iff_surjective).mp hi⟩)

/--
Exact identity `(basis N).eigenvalues (nodeIndex N hN j) = node N j`.

Use: `«2606.16671v2».SineJacobi.spectral_weight` rewrites with this identity to establish exact
identity `(basis N).weight (⟨0,hN⟩ : Fin N) (nodeIndex N hN j) = sineWeight N j`.

Article: 2606.16671v2, Theorem E.1 via `«2606.16671v2».SineJacobi.spectral_weight`.

Proof: Use the identities/estimates
`_private.«2606.16671v2».SineJacobi.SpectralMeasure.0.«2606.16671v2».SineJacobi.nodeIndexFun_spec`
with the arguments shown in the proof.
-/
@[simp] theorem eigenvalue_nodeIndex (N : ℕ) (hN : 0 < N) (j : Fin N) :
    (basis N).eigenvalues (nodeIndex N hN j) = node N j := nodeIndexFun_spec N hN j

/--
The explicit finite chain has exactly the sine spectral weights used in the paper.

Exact identity `(basis N).weight (⟨0,hN⟩ : Fin N) (nodeIndex N hN j) = sineWeight N j`.

Use: `«2606.16671v2».SineJacobi.leading_orthogonality` uses this identity to establish exact
identity `∑ j : Fin N, sineWeight N j*((data N).leading s).eval (node N j)* ((data N).leading
t).eval (node N j) = if s = t then ((data N).linkProduct s)^2 else 0`.

Article: 2606.16671v2, Theorem E.1.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem spectral_weight (N : ℕ) (hN : 0 < N) (j : Fin N) :
    (basis N).weight (⟨0,hN⟩ : Fin N) (nodeIndex N hN j) = sineWeight N j := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  have hpos : ∀ s, 0 < s → s < n+1 → 0 < (data (n+1)).aSq s := by
    intro s hs hsN
    rw [data_aSq _ _ hs hsN]
    exact couplingSq_pos _ _ hs hsN
  have hw := (data (n+1)).spectral_weights_of_persymmetric (basis (n+1))
    (data_aSq_nonneg (n+1)) hpos (basis_eigenvalues_injective (n+1) hN) (matrix_persymmetric (n+1))
  let c := sqrt ((data (n+1)).couplingProduct 1 n)/((2/(2:ℝ)^(n+1))*(n+1:ℝ))
  have hh (k : Fin (n+1)) : (basis (n+1)).weight 0 (nodeIndex (n+1) hN k) =
      c*sin (nodeAngle (n+1) k) := by
    rw [hw, eigenvalue_nodeIndex, terminal_derivative_abs _ hN]
    dsimp [c]
    field_simp
    push_cast
    ring
  have hs : c*(∑ k : Fin (n+1), sin (nodeAngle (n+1) k)) = 1 := by
    rw [Finset.mul_sum]
    simp_rw [← hh]
    rw [(nodeIndex (n+1) hN).sum_comp]
    exact (basis (n+1)).weight_sum 0
  have hsum : (∑ k : Fin (n+1), sin (nodeAngle (n+1) k)) ≠ 0 :=
    ne_of_gt (Finset.sum_pos (fun k _ => node_sin_pos _ k) Finset.univ_nonempty)
  change (basis (n+1)).weight (⟨0,hN⟩ : Fin (n+1)) (nodeIndex (n+1) hN j) = sineWeight (n+1) j
  have hfirst : (⟨0,hN⟩ : Fin (n+1)) = 0 := by apply Fin.ext; simp
  rw [hfirst, hh]
  unfold sineWeight
  apply (eq_div_iff hsum).mpr
  linear_combination sin (nodeAngle (n+1) j)*hs


/--
The stated quantitative bound `0 < sineWeight N j`.

Use: a standalone supporting bound for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2606.16671v2, Theorem E.1.

Proof: Use the identities/estimates `«2606.16671v2».SineJacobi.node_sin_pos` with the arguments
shown in the proof.
-/
theorem sineWeight_pos (N : ℕ) (j : Fin N) : 0 < sineWeight N j := by
  have hN : 0 < N := by have := j.isLt; omega
  let : NeZero N := ⟨Nat.ne_of_gt hN⟩
  exact div_pos (node_sin_pos N j) (Finset.sum_pos (fun k _ => node_sin_pos N k) Finset.univ_nonempty)

/--
Exact identity `∑ j : Fin N, sineWeight N j = 1`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2606.16671v2, Theorem E.1.

Proof: Use the identities/estimates `«2606.16671v2».SineJacobi.node_sin_pos` with the arguments
shown in the proof.
-/
theorem sineWeight_sum (N : ℕ) (hN : 0 < N) : ∑ j : Fin N, sineWeight N j = 1 := by
  let : NeZero N := ⟨Nat.ne_of_gt hN⟩
  unfold sineWeight
  rw [← Finset.sum_div, div_self]
  exact ne_of_gt (Finset.sum_pos (fun k _ => node_sin_pos N k) Finset.univ_nonempty)

/--
Exact identity `nodeAngle N j.rev = π-nodeAngle N j`.

Use: `«2606.16671v2».SineJacobi.node_reverse` rewrites with this identity to establish exact
identity `node N j.rev = -node N j`.

Article: 2606.16671v2, Theorem E.1.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem nodeAngle_reverse (N : ℕ) (j : Fin N) : nodeAngle N j.rev = π-nodeAngle N j := by
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by have := j.isLt; omega)
  unfold nodeAngle
  simp only [Fin.rev, Fin.val_mk, Nat.cast_sub (Nat.succ_le_of_lt j.isLt)]
  field_simp
  push_cast
  ring

/--
Exact identity `node N j.rev = -node N j`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2606.16671v2, Theorem E.1.

Proof: Use the identities/estimates `«2606.16671v2».SineJacobi.nodeAngle_reverse` with the
arguments shown in the proof.
-/
theorem node_reverse (N : ℕ) (j : Fin N) : node N j.rev = -node N j := by simp [node, nodeAngle_reverse, cos_pi_sub]

/--
Exact identity `sineWeight N j.rev = sineWeight N j`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2606.16671v2, Theorem E.1.

Proof: Use the identities/estimates `«2606.16671v2».SineJacobi.nodeAngle_reverse` with the
arguments shown in the proof.
-/
theorem sineWeight_reverse (N : ℕ) (j : Fin N) : sineWeight N j.rev = sineWeight N j := by simp only [sineWeight, nodeAngle_reverse, sin_pi_sub]

end
end «2606.16671v2».SineJacobi
