import krylov.Secant.Flag
import Mathlib.Tactic

/-!
Article: main_krylov, thm:centre, the exact reflection in direction coordinates.
Use: construct the twin operators and prove involutivity and probe preservation
before imposing metric budgets or replaying an adaptive method.
Source: the article's flag reflection; the existing secant flag identity supplies
the latest-information model, with the final zero-length tail handled explicitly.
-/

namespace krylov.Information
noncomputable section
open Matrix Finset krylov.Secant
open scoped BigOperators
variable {p : ℕ}

/-- The coordinate projection complementary to the explored prefix.
Use: the base displacement is the sum of its hidden-block compressions.
Article: main_krylov, apD:centre, Ī_l. -/
def complementProjection (p l : ℕ) : Matrix (Fin p) (Fin p) ℝ :=
  Matrix.diagonal fun i => if i.val ≤ l then 0 else 1

/-- The coordinate reflection that fixes the explored prefix and negates its complement.
Use: construct the reflected symmetric increments without choosing a metric.
Article: main_krylov, apD:centre, J_l=I_≤l−Ī_l. -/
def flagReflection (p l : ℕ) : Matrix (Fin p) (Fin p) ℝ :=
  Matrix.diagonal fun i => if i.val ≤ l then 1 else -1

/-- The reflected increment preserves cross blocks and reverses both diagonal blocks.
Use: a genuine transformation of operators, rather than assumed twin observations.
Article: main_krylov, thm:centre, E_l^♯=−J_l E_l J_l. -/
def reflectedIncrement (l : ℕ) (E : Matrix (Fin p) (Fin p) ℝ) :
    Matrix (Fin p) (Fin p) ℝ :=
  -(flagReflection p l * E * flagReflection p l)

/-- Complementary compression retains precisely the two unobserved coordinates.
Use: prove that future hidden-block base changes annihilate every current probe.
Article: main_krylov, apD:eq:Akdiff, Ī_l E_l Ī_l.
Proof: the two diagonal indicator factors select indices strictly after l. -/
theorem complement_compression_apply (l : ℕ) (E : Matrix (Fin p) (Fin p) ℝ)
    (i j : Fin p) :
    (complementProjection p l * E * complementProjection p l) i j =
      if l < min i.val j.val then E i j else 0 := by
  simp only [complementProjection,Matrix.mul_diagonal,Matrix.diagonal_mul]
  by_cases hi : i.val ≤ l <;> by_cases hj : j.val ≤ l <;> simp [hi,hj,← not_le]

/-- Each coordinate reflection is an involution on actual increments.
Use: the second transformation restores all increments, including zero ones.
Article: main_krylov, thm:centre, involutivity on E_l.
Proof: each diagonal sign occurs twice on each side of the entry. -/
theorem reflectedIncrement_involutive (l : ℕ) (E : Matrix (Fin p) (Fin p) ℝ) :
    reflectedIncrement l (reflectedIncrement l E)=E := by
  ext i j
  simp only [reflectedIncrement,flagReflection,Matrix.neg_apply,
    Matrix.mul_diagonal,Matrix.diagonal_mul]
  by_cases hi : i.val ≤ l <;> by_cases hj : j.val ≤ l <;> simp [hi,hj]

/-- Reflection reverses exactly the old and hidden diagonal compressions.
Use: the common algebraic identity behind the time-dependent twin operators.
Article: main_krylov, apD:eq:Akdiff, block expansion of E_l^♯.
Proof: check the four blocks selected by the two diagonal prefix indicators. -/
theorem reflectedIncrement_eq (l : ℕ) (E : Matrix (Fin p) (Fin p) ℝ) :
    reflectedIncrement l E = E-(2 : ℝ) •
      (prefixProjection p l * E * prefixProjection p l +
        complementProjection p l * E * complementProjection p l) := by
  ext i j
  simp only [reflectedIncrement,flagReflection,Matrix.neg_apply,Matrix.mul_diagonal,
    Matrix.diagonal_mul,prefix_compression_apply,complement_compression_apply,
    Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  by_cases hi : i.val ≤ l <;> by_cases hj : j.val ≤ l <;> simp [hi,hj,← not_le] <;> ring

/-- Old-block compression changes sign under the reflection.
Use: twice reflecting restores each actual intermediate correction operator.
Article: main_krylov, thm:centre, Π_lᵀ E_l^♯ Π_l=−Π_lᵀ E_l Π_l.
Proof: on the selected old block both reflection signs are positive. -/
theorem prefix_reflectedIncrement (l : ℕ) (E : Matrix (Fin p) (Fin p) ℝ) :
    prefixProjection p l * reflectedIncrement l E * prefixProjection p l =
      -(prefixProjection p l * E * prefixProjection p l) := by
  ext i j
  simp only [prefix_compression_apply,Matrix.neg_apply,reflectedIncrement,
    flagReflection,Matrix.mul_diagonal,Matrix.diagonal_mul]
  by_cases hi : i.val ≤ l <;> by_cases hj : j.val ≤ l <;> simp [hi,hj]

/-- Hidden-block compression also changes sign under the reflection.
Use: the second base displacement cancels the first one exactly.
Article: main_krylov, thm:centre, Ī_l E_l^♯ Ī_l=−Ī_l E_l Ī_l.
Proof: on the selected hidden block the two negative signs cancel. -/
theorem complement_reflectedIncrement (l : ℕ) (E : Matrix (Fin p) (Fin p) ℝ) :
    complementProjection p l * reflectedIncrement l E * complementProjection p l =
      -(complementProjection p l * E * complementProjection p l) := by
  ext i j
  simp only [complement_compression_apply,Matrix.neg_apply,reflectedIncrement,
    flagReflection,Matrix.mul_diagonal,Matrix.diagonal_mul]
  by_cases hi : i.val ≤ l <;> by_cases hj : j.val ≤ l <;> simp [hi,hj,← not_le]

/-- The actual operator data of a finite probed-correction scenario.
Use: record independent operators before imposing symmetry, positivity or budgets.
Article: main_krylov, s4:C, Ξ=(A₀;E_•;E′;F_•). -/
@[ext] structure Scenario (p : ℕ) where
  /-- The reference-independent base operator A₀ from which probe operators accumulate. -/
  base : Matrix (Fin p) (Fin p) ℝ
  /-- Consecutive probe increments E_l; a finite horizon uses only its finite prefix. -/
  increment : ℕ → Matrix (Fin p) (Fin p) ℝ
  /-- The additional operator E′ used at the terminal correction query. -/
  terminal : Matrix (Fin p) (Fin p) ℝ
  /-- Intermediate correction perturbations F_k relative to the current probe operator. -/
  correction : ℕ → Matrix (Fin p) (Fin p) ℝ

/-- The probe operator obtained by summing the actual preceding increments.
Use: the twin must preserve its action on the current direction at every time.
Article: main_krylov, s4:C, A_k=A₀+Σ_(l<k)E_l. -/
def Scenario.probe (S : Scenario p) (k : ℕ) : Matrix (Fin p) (Fin p) ℝ :=
  S.base + ∑ l ∈ range k, S.increment l

/-- The old-block curvature accumulated strictly before an iteration.
Use: compensate the reflection at every actual intermediate correction.
Article: main_krylov, apD:centre, 𝒴_k. -/
def Scenario.oldPart (S : Scenario p) (k : ℕ) : Matrix (Fin p) (Fin p) ℝ :=
  ∑ l ∈ range k, prefixProjection p l * S.increment l * prefixProjection p l

/-- The explicit flag-reflected scenario for a specified terminal time.
Use: prove exact preservation and involutivity before the admissibility estimates.
Article: main_krylov, thm:centre, σ_M(Ξ) in its fixed direction coordinates. -/
def Scenario.reflect (S : Scenario p) (N : ℕ) : Scenario p where
  base := S.base + (2 : ℝ) • ∑ l ∈ range N,
    complementProjection p l * S.increment l * complementProjection p l
  increment := fun l => reflectedIncrement l (S.increment l)
  terminal := -S.terminal
  correction := fun k => S.correction k + (2 : ℝ) • S.oldPart k

/-- Twice reflecting a scenario restores every operator exactly.
Use: the information symmetry is a true involution on data, including zero increments.
Article: main_krylov, thm:centre, σ_M²=id for a preserved flag.
Proof: both compressed blocks change sign, cancelling the second base and
correction changes; each increment and the terminal perturbation are involutive. -/
theorem Scenario.reflect_involutive (S : Scenario p) (N : ℕ) :
    (S.reflect N).reflect N=S := by
  -- The second base displacement and each second correction displacement have opposite signs.
  cases S with
  | mk A E T F =>
    apply Scenario.ext
    · simp only [Scenario.reflect,complement_reflectedIncrement,sum_neg_distrib]
      module
    · funext l
      exact reflectedIncrement_involutive l (E l)
    · exact neg_neg T
    · funext k
      simp only [Scenario.reflect,Scenario.oldPart,prefix_reflectedIncrement,sum_neg_distrib]
      module

/-- The exact twin probe displacement separates future hidden blocks from past old blocks.
Use: derive both current-probe preservation and intermediate correction preservation.
Article: main_krylov, apD:eq:Akdiff.
Proof: expand the reflected increments and split the finite hidden-block sum
at the current time; all common terms cancel by additive algebra. -/
theorem Scenario.reflect_probe_sub (S : Scenario p) {k N : ℕ} (hk : k ≤ N) :
    (S.reflect N).probe k-S.probe k =
      (2 : ℝ) • (∑ l ∈ Ico k N,
        complementProjection p l*S.increment l*complementProjection p l) -
      (2 : ℝ) • S.oldPart k := by
  -- Split the hidden-block sum at the actual current time before cancelling old terms.
  have hs := sum_range_add_sum_Ico
    (fun l => complementProjection p l*S.increment l*complementProjection p l) hk
  simp only [Scenario.probe,Scenario.reflect,reflectedIncrement_eq,
    sum_sub_distrib,sum_add_distrib,← smul_sum]
  rw [← hs]
  unfold Scenario.oldPart
  module

/-- Every current coordinate probe is exactly preserved by the constructed twin.
Use: this is an operator-action identity, not just preservation of scalar pairings.
Article: main_krylov, thm:centre, A_k^♯d_k=A_kd_k.
Proof: future complementary blocks and past prefix blocks both annihilate
the kth coordinate direction, as follows from their actual diagonal indicators. -/
theorem Scenario.reflect_probe_column (S : Scenario p) {k N : ℕ} (hk : k ≤ N)
    (j : Fin p) (hj : j.val=k) (i : Fin p) :
    (S.reflect N).probe k i j=S.probe k i j := by
  -- Both remaining block sums annihilate the current direction coordinate.
  have hf : (∑ l ∈ Ico k N,
      complementProjection p l*S.increment l*complementProjection p l) i j=0 := by
    simp only [Matrix.sum_apply]
    apply sum_eq_zero
    intro l hl
    rw [complement_compression_apply,ite_eq_right]
    have hkl := (mem_Ico.mp hl).1
    omega
  have hp : S.oldPart k i j=0 := by
    simp only [Scenario.oldPart,Matrix.sum_apply]
    apply sum_eq_zero
    intro l hl
    rw [prefix_compression_apply,ite_eq_right]
    have hlk := mem_range.mp hl
    omega
  have hd := congrFun (congrFun (S.reflect_probe_sub hk) i) j
  simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,hf,hp,mul_zero,sub_zero] at hd
  exact sub_eq_zero.mp hd

end
end krylov.Information
