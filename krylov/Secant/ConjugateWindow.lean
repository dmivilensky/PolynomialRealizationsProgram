import krylov.Secant.HiddenSequence
import krylov.LinearAlgebra.NormOrder

/-!
Article: main_krylov, thm:window, the exact conjugate-window information radius.
Use: combine the physical envelope with the genuine canonical spectral norm;
the oldest-coordinate witnesses supply the matching obstruction.
Source: the proved flag identities, Loewner envelope and spectral norm criterion.
-/

namespace krylov.Secant
noncomputable section
open Matrix Finset
open scoped Matrix MatrixOrder BigOperators
variable {n p : ℕ}

/-- Compressing a nonnegative diagonal Gram matrix by an old flag decreases it.
Use: conjugate windows do not amplify the physical budget envelope.
Article: main_krylov, thm:window, the conjugate-window upper bound.
Proof: the discarded diagonal entries are nonnegative, including empty flags. -/
theorem prefix_diagonal_le (c : Fin p → ℝ) (hc : ∀ i, 0 ≤ c i) (l : ℕ) :
    prefixProjection p l * diagonal c * prefixProjection p l ≤ diagonal c := by
  -- The discarded form is the nonnegative complementary diagonal.
  have he : diagonal c - prefixProjection p l * diagonal c * prefixProjection p l =
      diagonal (fun i => if i.val ≤ l then 0 else c i) := by
    ext i j
    rw [Matrix.sub_apply, prefix_compression_apply]
    by_cases hij : i = j
    · subst j
      simp only [max_self, diagonal_apply_eq]
      split_ifs <;> simp_all
    · simp [hij]
  rw [Matrix.le_iff, he, posSemidef_diagonal_iff]
  intro i
  split_ifs <;> simp_all

/-- The entire conjugate-window envelope is bounded by the summed budget times G.
Use: the matching upper bound retains the full sum W and needs no loss in p.
Article: main_krylov, thm:window, conjugate-window radius at most W.
Proof: each old diagonal compression is bounded by G; sum its nonnegative budget multiple. -/
theorem diagonal_envelope_le (c : Fin p → ℝ) (hc : ∀ i, 0 ≤ c i)
    (ω : ℕ → ℝ) (hω : ∀ l < p, 0 ≤ ω l) :
    flagEnvelope (diagonal c) ω ≤ (∑ l ∈ range p, ω l) • diagonal c := by
  rw [flagEnvelope, Finset.sum_smul]
  apply Finset.sum_le_sum
  intro l hl
  exact smul_le_smul_of_nonneg_left (prefix_diagonal_le c hc l) (hω l (mem_range.mp hl))

/-- Every admissible conjugate window has canonical model error of spectral norm at most W.
Use: together with the actual opposite histories this proves the exact information radius.
Article: main_krylov, thm:window, the conjugate-window upper radius.
Proof: bound the physical envelope by WG, compress both signs by G⁻¹/², and
use the two shifted positive forms to recover the actual Euclidean spectral norm. -/
theorem conjugate_window_upper (S : Matrix (Fin n) (Fin p) ℝ)
    (hS : Function.Injective S.mulVec) (base : Matrix (Fin n) (Fin n) ℝ) (hbase : base.PosDef)
    (A : ℕ → Matrix (Fin n) (Fin n) ℝ) (hA : ∀ k, (A k).IsSymm)
    (ω : ℕ → ℝ) (hω : ∀ l < p, 0 ≤ ω l)
    (hlo : ∀ l < p, -(ω l • base) ≤ A (l + 1) - A l)
    (hhi : ∀ l < p, A (l + 1) - A l ≤ ω l • base)
    (c : Fin p → ℝ) (hc : Sᵀ * base * S = diagonal c) :
    chebyshev1.opNorm (canonicalWindowError S base A) ≤ ∑ l ∈ range p, ω l := by
  -- Full physical column rank supplies the positive-definite canonical Gram metric.
  let G := Sᵀ * base * S
  have hG : G.PosDef := by
    simpa only [G, conjTranspose_eq_transpose_of_trivial] using
      hbase.conjTranspose_mul_mul_same (B := S) hS
  have hcn : ∀ i, 0 ≤ c i := by
    have hd := hG.posSemidef
    rw [show G = diagonal c from hc, posSemidef_diagonal_iff] at hd
    exact hd
  have hen : flagEnvelope G ω ≤ (∑ l ∈ range p, ω l) • G := by
    rw [show G = diagonal c from hc]
    exact diagonal_envelope_le c hcn ω hω
  have hb := window_loewner_bound S A hA base ω hlo hhi
  have hu := relativeOperator_mono G (hb.2.trans hen)
  have hl := relativeOperator_mono G ((neg_le_neg hen).trans hb.1)
  simp only [relativeOperator_neg, relativeOperator_smul, relativeOperator_base G hG] at hu hl
  have hz : (canonicalWindowError S base A).IsSymm := by
    apply relativeOperator_isSymm
    have hs : (Sᵀ * A p * S).IsSymm := by
      simp only [Matrix.IsSymm, transpose_mul, transpose_transpose, (hA p).eq, Matrix.mul_assoc]
    exact hs.sub (latest_isSymm _)
  apply (krylov.LinearAlgebra.spectral_norm_iff_shifted_posSemidef _
    (Matrix.isHermitian_iff_isSymm.mpr hz) (sum_nonneg fun l hl => hω l (mem_range.mp hl))).mpr
  constructor
  · exact Matrix.le_iff.mp hu
  · have hh := Matrix.le_iff.mp hl
    simpa only [canonicalWindowError, G, sub_neg_eq_add, add_comm] using hh

end
end krylov.Secant
