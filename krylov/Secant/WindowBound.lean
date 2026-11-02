import krylov.Secant.Flag
import Mathlib.Analysis.Matrix.Order

/-!
Article: main_krylov, Theorem thm:window, the exact Loewner envelope.
Use: bound the hidden model error for arbitrary windows without requiring
independence of their columns; positivity is used only for the envelope.
Source: congruence preserves positive semidefiniteness, and the exact flag identity.
-/

namespace krylov.Secant
noncomputable section
open Matrix Finset
open scoped Matrix MatrixOrder BigOperators
variable {n p : ℕ}

/-- Compressing two ordered symmetric matrices preserves their Loewner order.
Use: every old flag inherits the physical increment budget.
Article: main_krylov, proof of thm:window.
Source: mathlib Matrix.PosSemidef.conjTranspose_mul_mul_same.
Proof: compress the positive semidefinite difference by the same rectangular matrix. -/
theorem congruence_mono {A B : Matrix (Fin n) (Fin n) ℝ} (h : A ≤ B)
    (C : Matrix (Fin n) (Fin p) ℝ) : Cᵀ * A * C ≤ Cᵀ * B * C := by
  simpa only [Matrix.le_iff, Matrix.mul_sub, Matrix.sub_mul, conjTranspose_eq_transpose_of_trivial]
    using (Matrix.le_iff.mp h).conjTranspose_mul_mul_same C

/-- The coordinate flag projectors are genuinely symmetric matrices.
Use: their old-flag compressions are rectangular congruences.
Article: main_krylov, Lemma lem:flag, the coordinate projectors.
Proof: a diagonal matrix equals its transpose. -/
theorem prefixProjection_isSymm (p l : ℕ) : (prefixProjection p l).IsSymm := by
  simp only [prefixProjection, Matrix.IsSymm, diagonal_transpose]

/-- The cumulative entrywise budget seen by a pair of old coordinates.
Use: the Hadamard form of the exact information envelope.
Article: main_krylov, thm:window, R_ij = ∑_(l≥max(i,j)) ω_l. -/
def budgetTail (p : ℕ) (ω : ℕ → ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  fun i j => ∑ l ∈ range p, if max i.val j.val ≤ l then ω l else 0

/-- The sum of budget-weighted flag compressions of a Gram matrix.
Use: provides a positive-semidefinite envelope and its exact Hadamard formula.
Article: main_krylov, thm:window, ∑_l ω_l I_≤l G I_≤l. -/
def flagEnvelope (G : Matrix (Fin p) (Fin p) ℝ) (ω : ℕ → ℝ) :
    Matrix (Fin p) (Fin p) ℝ :=
  ∑ l ∈ range p, ω l • (prefixProjection p l * G * prefixProjection p l)

/-- The flag envelope is precisely the printed Hadamard budget matrix.
Use: identifies the concrete algebraic bound with G ∘ R in the article.
Article: main_krylov, thm:window, entrywise envelope identity.
Proof: an entry survives exactly the tail selected by its newer coordinate. -/
theorem flagEnvelope_apply (G : Matrix (Fin p) (Fin p) ℝ) (ω : ℕ → ℝ) (i j : Fin p) :
    flagEnvelope G ω i j = G i j * budgetTail p ω i j := by
  simp only [flagEnvelope, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    prefix_compression_apply, budgetTail, Finset.mul_sum]
  apply sum_congr rfl
  intro l _
  split_ifs <;> simp [mul_comm]

/-- A nonnegative budget produces a positive-semidefinite flag envelope.
Use: the positivity assertion in the unresolved-curvature theorem.
Article: main_krylov, thm:window, G ∘ R ⪰ 0.
Proof: each summand is a nonnegative multiple of a Gram congruence. -/
theorem flagEnvelope_posSemidef (G : Matrix (Fin p) (Fin p) ℝ) (hG : G.PosSemidef)
    (ω : ℕ → ℝ) (hω : ∀ l < p, 0 ≤ ω l) : (flagEnvelope G ω).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro l hl
  have h := (hG.conjTranspose_mul_mul_same (prefixProjection p l)).smul (hω l (mem_range.mp hl))
  simpa only [conjTranspose_eq_transpose_of_trivial, (prefixProjection_isSymm p l).eq] using h

/-- Every admissible physical sequence obeys both sharp flag-envelope inequalities.
Use: the first assertion of thm:window, before constructing indistinguishable data.
Article: main_krylov, thm:window, −G∘R ⪯ Z ⪯ G∘R.
Proof: compress each signed Loewner budget by the old flag and sum; replace
the sum of true increments using the already proved exact physical flag identity. -/
theorem window_loewner_bound (S : Matrix (Fin n) (Fin p) ℝ)
    (A : ℕ → Matrix (Fin n) (Fin n) ℝ) (hA : ∀ k, (A k).IsSymm)
    (base : Matrix (Fin n) (Fin n) ℝ) (ω : ℕ → ℝ)
    (hlo : ∀ l < p, -(ω l • base) ≤ A (l + 1) - A l)
    (hhi : ∀ l < p, A (l + 1) - A l ≤ ω l • base) :
    let G := Sᵀ * base * S
    let Z := Sᵀ * A p * S - latest (Sᵀ * pairImages S A)
    (-flagEnvelope G ω ≤ Z) ∧ (Z ≤ flagEnvelope G ω) := by
  dsimp only
  rw [(flag_identities S A hA).1]
  -- Treat the lower bound as the sum of the negative compressed budgets.
  have hupper := Finset.sum_le_sum (s := range p) fun l hl =>
    congruence_mono (hhi l (mem_range.mp hl)) (S * prefixProjection p l)
  have hlower := Finset.sum_le_sum (s := range p) fun l hl =>
    congruence_mono (hlo l (mem_range.mp hl)) (S * prefixProjection p l)
  simp only [transpose_mul, (prefixProjection_isSymm p _).eq, Matrix.mul_assoc,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_neg, Matrix.neg_mul] at hupper hlower
  constructor
  · simpa only [flagEnvelope, Finset.sum_neg_distrib, Matrix.mul_assoc] using hlower
  · simpa only [flagEnvelope, Matrix.mul_assoc] using hupper

end
end krylov.Secant
