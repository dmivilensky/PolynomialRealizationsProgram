import krylov.Tensor.FlatDyadicBits
import krylov.Tensor.FlatPartitionBounds
import krylov.Functions.CubicSegment

/-!
Article: main_krylov, apG:flat, actual dyadic expansion of the flat prefix tensor.
Use: expand the real prefix vector and its compatible cubic contraction
using the genuine finite dyadic rectangles, with no decomposition premise.
Source: the actual unique binary-prefix partition proved in FlatDyadicBits.
-/

namespace krylov.Tensor
noncomputable section
open Finset krylov.Functions
open scoped BigOperators InnerProductSpace
section Linear
variable {N L : ℕ} {E : Type*} [NormedAddCommGroup E]

/-- The actual ordered prefix vector in the genuine coordinate family.
Article: main_krylov, apG:flat, the reversed flat CG tail. -/
def flatPrefixVector (e : Fin N → E) (b : Fin N) : E :=
  ∑ a : Fin N, if a < b then e a else 0

/-- The real vector of one actual dyadic left half-block.
Article: main_krylov, apG:flat, actual dyadic indicator vectors. -/
def dyadicLeftVector (e : Fin N → E) (p : DyadicPrefixIndex L) : E :=
  ∑ a ∈ dyadicHalf N p.1.val p.2.val false, e a

/-- The genuine flat prefix vector is exactly the sum of its actual dyadic left blocks selected by the actual right blocks.
Article: main_krylov, apG:flat, v_a=Σ_(I∈D(m_a))1_I.
Proof: expand both real finite sums. Each actual strict prefix coordinate
belongs to exactly one genuine rectangle, by the binary partition theorem. -/
theorem flatPrefixVector_dyadic (e : Fin N → E) (hN : N ≤ 2 ^ L) (b : Fin N) :
    flatPrefixVector e b = ∑ p : DyadicPrefixIndex L,
      if b ∈ dyadicHalf N p.1.val p.2.val true then dyadicLeftVector e p else 0 := by
  have hexpand (p : DyadicPrefixIndex L) : (if b ∈ dyadicHalf N p.1.val p.2.val true then dyadicLeftVector e p else 0) =
      ∑ a : Fin N, if a ∈ dyadicHalf N p.1.val p.2.val false ∧ b ∈ dyadicHalf N p.1.val p.2.val true then e a else 0 := by
    by_cases hb : b ∈ dyadicHalf N p.1.val p.2.val true
    · simp only [hb, ite_true, and_true, dyadicLeftVector]
      simpa only [Finset.filter_univ_mem] using
        (Finset.sum_filter (s := Finset.univ) (fun a => a ∈ dyadicHalf N p.1.val p.2.val false) e)
    · simp only [hb, ite_false, and_false, sum_const_zero]
  simp_rw [hexpand]
  rw [Finset.sum_comm]
  unfold flatPrefixVector
  apply Finset.sum_congr rfl
  intro a _
  by_cases hab : a < b
  · obtain ⟨p, hp, huniq⟩ := (dyadic_prefix_rectangle_unique N L hN a b).mp hab
    rw [Finset.sum_eq_single p]
    · simp only [hab, hp.1, hp.2, true_and, ite_true]
    · intro q _ hqp
      have hn : ¬ (a ∈ dyadicHalf N q.1.val q.2.val false ∧ b ∈ dyadicHalf N q.1.val q.2.val true) :=
        fun hq => hqp (huniq q hq)
      simp only [hn, ite_false]
    · intro hp'
      exact (hp' (Finset.mem_univ p)).elim
  · have hn (p : DyadicPrefixIndex L) : ¬ (a ∈ dyadicHalf N p.1.val p.2.val false ∧ b ∈ dyadicHalf N p.1.val p.2.val true) :=
      fun hp => hab (dyadic_rectangle_lt hp.1 hp.2)
    simp only [hab, ite_false]
    simp_rw [hn]
    simp only [ite_false, sum_const_zero]

end Linear

section Inner
variable {N L : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual compatible contraction with the squared prefix vector.
Article: main_krylov, apG:flat, the actual X₁ contraction. -/
def flatPrefixContraction (e : Fin N → E) (T : SymmetricCubic E) (u : E) : ℝ :=
  ∑ a : Fin N, inner ℝ (e a) u * T.form (e a) (flatPrefixVector e a) (flatPrefixVector e a)

/-- The original squared-prefix contraction equals the genuine double dyadic block contraction.
Article: main_krylov, apG:flat, X₁=Σ_(I,J)u_(A(I)∩A(J))⊗1_I⊗1_J.
Proof: insert the proved real prefix expansion in both tensor slots and
commute its finite sums. The original restricted first-slot vector is the
actual orthogonal coordinate restriction on the real right-block intersection. -/
theorem flatPrefixContraction_dyadic (e : Fin N → E) (T : SymmetricCubic E) (hN : N ≤ 2 ^ L) (u : E) :
    flatPrefixContraction e T u = ∑ p : DyadicPrefixIndex L, ∑ q : DyadicPrefixIndex L,
      T.form (flagComponent e (dyadicHalf N p.1.val p.2.val true ∩ dyadicHalf N q.1.val q.2.val true) u)
        (dyadicLeftVector e p) (dyadicLeftVector e q) := by
  unfold flatPrefixContraction
  simp_rw [flatPrefixVector_dyadic e hN]
  simp only [map_sum, _root_.sum_apply, mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  unfold flagComponent
  simp only [map_sum, _root_.sum_apply, map_smul, smul_apply, smul_eq_mul]
  rw [← Finset.filter_univ_mem (dyadicHalf N p.1.val p.2.val true ∩ dyadicHalf N q.1.val q.2.val true), Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hp : a ∈ dyadicHalf N p.1.val p.2.val true <;>
    by_cases hq : a ∈ dyadicHalf N q.1.val q.2.val true <;>
    simp only [hp, hq, ite_true, ite_false, map_zero, _root_.zero_apply, mul_zero,
      Finset.mem_inter, and_self, and_false, false_and, T.swap₂]

end Inner
end
end krylov.Tensor
