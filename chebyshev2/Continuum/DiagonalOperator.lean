import chebyshev2.Continuum.NuclearSeries
import chebyshev2.Continuum.SpectralQuadratic

/-!
Article: chebyshev2, Theorem 2.3.
The absolutely summable bounded diagonal operator used in the trace-class spectral perturbation
argument.
Use: `chebyshev2.Continuum.diagonalOperator_positive` feeds
`chebyshev2.SineContinuum.greenOperator_positive` (green Operator positive).
Proof chain: `chebyshev2.Packing.packed_spectral_distance` — chebyshev2, Theorem 2.3; Block
packing, exact masses/energy and spectral distance.
-/
namespace chebyshev2.Continuum
noncomputable section
open Real
open scoped InnerProductSpace BigOperators
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
The absolutely summable bounded diagonal operator used in the trace-class spectral perturbation
argument.

Use: `chebyshev2.Continuum.diagonalOperator_positive` rewrites with this definition to
establish the precise assertion is `(diagonalOperator b eig).IsPositive`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.
-/
def diagonalOperator {ι : Type*} (b : HilbertBasis ι ℝ E) (eig : ι → ℝ) : E →L[ℝ] E :=
  ∑' i, eig i • InnerProductSpace.rankOne ℝ (b i) (b i)

/--
Summability of the displayed sequence: `Summable (fun i => eig i • InnerProductSpace.rankOne ℝ
(b i) (b i))`.

Use: `chebyshev2.Continuum.diagonalOperator_basis` uses this summability result to
establish exact identity `diagonalOperator b eig (b j)=eig j • b j`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem diagonalOperator_summable {ι : Type*} (b : HilbertBasis ι ℝ E) {eig : ι → ℝ}
    (hs : Summable (fun i => |eig i|)) :
    Summable (fun i => eig i • InnerProductSpace.rankOne ℝ (b i) (b i)) := by
  apply Summable.of_norm
  simpa only [norm_smul,InnerProductSpace.norm_rankOne,b.orthonormal.norm_eq_one,
    mul_one,Real.norm_eq_abs] using hs

/--
Exact identity `diagonalOperator b eig (b j)=eig j • b j`.

Use: `chebyshev2.Continuum.diagonalOperator_positive` rewrites with this identity to
establish the precise assertion is `(diagonalOperator b eig).IsPositive`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Proof: Separate `i=j` from its negation; prove the goal under each of these mutually exclusive
hypotheses. Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem diagonalOperator_basis {ι : Type*} (b : HilbertBasis ι ℝ E) {eig : ι → ℝ}
    (hs : Summable (fun i => |eig i|)) (j : ι) : diagonalOperator b eig (b j)=eig j • b j := by
  -- Separate `i=j` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  have h := (ContinuousLinearMap.apply ℝ E (b j)).hasSum (diagonalOperator_summable b hs).hasSum
  apply h.unique
  classical
  have he : (fun i => (eig i • InnerProductSpace.rankOne ℝ (b i) (b i)) (b j))=
      Pi.single j (eig j • b j) := by
    funext i
    by_cases hi : i=j
    · subst i
      simp [InnerProductSpace.rankOne_apply,b.orthonormal.norm_eq_one]
    · simp [InnerProductSpace.rankOne_apply,b.orthonormal.inner_eq_zero hi,hi]
  change HasSum (fun i => (eig i • InnerProductSpace.rankOne ℝ (b i) (b i)) (b j)) (eig j • b j)
  rw [he]
  exact hasSum_pi_single j (eig j • b j)

/--
The precise assertion is `TraceBound (diagonalOperator b eig) (∑' i, |eig i|)`.

Use: `chebyshev2.Continuum.eigenvalue_l1_le_traceBound` uses this assertion to establish
the stated quantitative bound `(∑' n, |DA.eigenvalue n - DB.eigenvalue n|) ≤ C`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Proof: Use the identities/estimates `chebyshev2.Continuum.eigenbasis_traceBound`,
`chebyshev2.Continuum.diagonalOperator_basis` with the arguments shown in the proof.
-/
theorem diagonalOperator_traceBound {ι : Type*} (b : HilbertBasis ι ℝ E) {eig : ι → ℝ}
    (hs : Summable (fun i => |eig i|)) : TraceBound (diagonalOperator b eig) (∑' i, |eig i|) :=
  eigenbasis_traceBound b _ (diagonalOperator_basis b hs) hs

/--
Compactness of the displayed operator: `IsCompactOperator (diagonalOperator b eig)`.

Use: `chebyshev2.Continuum.eigenvalue_l1_le_traceBound` uses this assertion to establish
the stated quantitative bound `(∑' n, |DA.eigenvalue n - DB.eigenvalue n|) ≤ C`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Proof: Use the identities/estimates `chebyshev2.Continuum.diagonalOperator_summable`,
`chebyshev2.Continuum.rankOne_isCompact` with the arguments shown in the proof.
-/
theorem diagonalOperator_isCompact {ι : Type*} (b : HilbertBasis ι ℝ E) {eig : ι → ℝ}
    (hs : Summable (fun i => |eig i|)) : IsCompactOperator (diagonalOperator b eig) := by
  apply isClosed_setOfPred_isCompactOperator.mem_of_tendsto
    (diagonalOperator_summable b hs).hasSum
  apply Filter.Eventually.of_forall
  intro s
  exact (compactOperator (RingHom.id ℝ) E E).sum_mem
    (fun i _ => (rankOne_isCompact (b i) (b i)).smul (eig i))

/--
The precise assertion is `(diagonalOperator b eig).IsPositive`.

Use: `chebyshev2.Continuum.eigenvalue_l1_le_traceBound` uses this assertion to establish
the stated quantitative bound `(∑' n, |DA.eigenvalue n - DB.eigenvalue n|) ≤ C`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem diagonalOperator_positive {ι : Type*} (b : HilbertBasis ι ℝ E) {eig : ι → ℝ}
    (hs : Summable (fun i => |eig i|)) (hp : ∀ i, 0 ≤ eig i) :
    (diagonalOperator b eig).IsPositive := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  have hsym : (diagonalOperator b eig).IsSymmetric := by
    intro u v
    have h := diagonalOperator_summable b hs
    have hu := (ContinuousLinearMap.apply ℝ E u).hasSum h.hasSum
    have hv := (ContinuousLinearMap.apply ℝ E v).hasSum h.hasSum
    have h₁ := hu.mapL (innerSL ℝ v)
    have h₂ := hv.mapL (innerSL ℝ u)
    have he : (fun i => inner ℝ v ((eig i • InnerProductSpace.rankOne ℝ (b i) (b i)) u))=
        (fun i => inner ℝ u ((eig i • InnerProductSpace.rankOne ℝ (b i) (b i)) v)) := by
      funext i
      simp only [InnerProductSpace.rankOne_apply,smul_apply,
        real_inner_smul_right]
      rw [real_inner_comm (b i) v,real_inner_comm (b i) u]
      ring
    change HasSum (fun i => inner ℝ v ((eig i • InnerProductSpace.rankOne ℝ (b i) (b i)) u))
      (inner ℝ v (diagonalOperator b eig u)) at h₁
    change HasSum (fun i => inner ℝ u ((eig i • InnerProductSpace.rankOne ℝ (b i) (b i)) v))
      (inner ℝ u (diagonalOperator b eig v)) at h₂
    rw [he] at h₁
    rw [real_inner_comm (diagonalOperator b eig u) v] at h₁
    exact h₁.unique h₂
  refine ⟨hsym,?_⟩
  intro u
  change 0 ≤ inner ℝ (diagonalOperator b eig u) u
  rw [real_inner_comm u (diagonalOperator b eig u),← (eigenbasis_quadratic_hasSum b _ (diagonalOperator_basis b hs) u).tsum_eq]
  exact tsum_nonneg (fun i => mul_nonneg (hp i) (sq_nonneg _))

end
end chebyshev2.Continuum
