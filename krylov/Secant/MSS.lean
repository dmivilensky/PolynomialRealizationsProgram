import krylov.Secant.Correction
import krylov.Secant.WindowBound
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
Article: main_krylov, Appendix A, prop:mss, the actual symmetric multipoint update.
Use: connect the latest-information model to concrete recursive matrix updates.
Source: Burdakov83, equations (2.7), (2.11), (3.8)–(3.9); BurdakovEtAl02.
-/

namespace krylov.Secant
noncomputable section
open Matrix
open scoped Matrix
variable {n : ℕ}

/-- Place an ordered sequence of physical vectors in the columns of its finite window.
Use: retain an explicit matrix type through inverse and rank statements.
Article: main_krylov, def:latest, the stored step and secant matrices. -/
def stepColumns (p : ℕ) (s : ℕ → Fin n → ℝ) : Matrix (Fin n) (Fin p) ℝ :=
  fun a i => s i.val a

/-- The original symmetric rank-two multipoint secant update.
Use: iteration with older-step annihilating c constructs the MSS matrix.
Article: main_krylov, prop:mss, displayed recurrence.
Source: Burdakov83, symmetric multipoint secant construction. -/
def mssUpdate (B : Matrix (Fin n) (Fin n) ℝ) (s y c : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  let r := y - B *ᵥ s
  B + (c ⬝ᵥ s)⁻¹ • (vecMulVec r c + vecMulVec c r) -
    ((r ⬝ᵥ s) / (c ⬝ᵥ s)^2) • vecMulVec c c

/-- Real rank-one matrix action is scalar pairing times its left vector.
Use: evaluate each actual MSS update on new and retained steps.
Article: main_krylov, proof of prop:mss.
Source: mathlib Matrix.vecMulVec_mulVec.
Proof: the opposite real scalar action agrees with ordinary scalar multiplication. -/
theorem outer_mulVec (u v w : Fin n → ℝ) :
    vecMulVec u v *ᵥ w = (v ⬝ᵥ w) • u := by
  simpa only [op_smul_eq_smul] using Matrix.vecMulVec_mulVec u v w

/-- A symmetric input gives a genuinely symmetric updated matrix.
Use: the recursive MSS matrix remains a valid symmetric curvature model.
Article: main_krylov, prop:mss, symmetry of every update.
Proof: transposition exchanges the two cross rank-one terms and fixes the diagonal term. -/
theorem mssUpdate_isSymm (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm)
    (s y c : Fin n → ℝ) : (mssUpdate B s y c).IsSymm := by
  simp only [mssUpdate, Matrix.IsSymm, transpose_sub, transpose_add, transpose_smul,
    transpose_vecMulVec, hB.eq, add_comm (vecMulVec c _) (vecMulVec _ c)]

/-- Every admissible MSS update satisfies the newest full secant equation.
Use: establishes the actual model action, independently of previous observations.
Article: main_krylov, prop:mss(a), B_(k+1)s_k = y_k.
Proof: expand the three rank-one actions and cancel their nonzero pivot. -/
theorem mssUpdate_secant (B : Matrix (Fin n) (Fin n) ℝ) (s y c : Fin n → ℝ)
    (hc : c ⬝ᵥ s ≠ 0) : mssUpdate B s y c *ᵥ s = y := by
  simp only [mssUpdate, sub_mulVec, add_mulVec, smul_mulVec, outer_mulVec, smul_add,
    smul_smul]
  ext i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- An old step only changes by a multiple of the new annihilating vector.
Use: proves both old Gram-block invariance and the projected-action formula.
Article: main_krylov, prop:mss, proof of parts (a) and (b).
Proof: its vanishing c-pairing kills the first and the diagonal rank-one terms. -/
theorem mssUpdate_old_action (B : Matrix (Fin n) (Fin n) ℝ) (s y c v : Fin n → ℝ)
    (hcv : c ⬝ᵥ v = 0) :
    mssUpdate B s y c *ᵥ v = B *ᵥ v +
      ((c ⬝ᵥ s)⁻¹ * ((y - B *ᵥ s) ⬝ᵥ v)) • c := by
  simp only [mssUpdate, sub_mulVec, add_mulVec, smul_mulVec, outer_mulVec, hcv,
    zero_smul, smul_zero, sub_zero, zero_add, smul_smul]

/-- Subsequent MSS updates preserve the whole older bilinear block.
Use: the latest observation fixes each projected model entry permanently.
Article: main_krylov, prop:mss(a), preservation of older projected entries.
Proof: pair the old-step action with another vector annihilated by c. -/
theorem mssUpdate_old_pairing (B : Matrix (Fin n) (Fin n) ℝ) (s y c u v : Fin n → ℝ)
    (hcu : c ⬝ᵥ u = 0) (hcv : c ⬝ᵥ v = 0) :
    u ⬝ᵥ (mssUpdate B s y c *ᵥ v) = u ⬝ᵥ (B *ᵥ v) := by
  rw [mssUpdate_old_action B s y c v hcv, dotProduct_add, dotProduct_smul,
    dotProduct_comm u c, hcu, smul_eq_mul, mul_zero, add_zero]

/-- The actual recursively updated MSS matrices, starting from an arbitrary B₀.
Use: instantiate the projected identity for the article's complete update sequence.
Article: main_krylov, prop:mss, the matrices B_k. -/
def mssSequence (B₀ : Matrix (Fin n) (Fin n) ℝ) (s y c : ℕ → Fin n → ℝ) :
    ℕ → Matrix (Fin n) (Fin n) ℝ
  | 0 => B₀
  | k + 1 => mssUpdate (mssSequence B₀ s y c k) (s k) (y k) (c k)

/-- Every upper-triangular model pairing equals its most recent secant observation.
Use: proves SᵀB_pS=T̄ for the concrete MSS sequence, for every admissible c.
Article: main_krylov, prop:mss(a), actual projected matrix identity.
Proof: induct on the number of inserted pairs; the newest column uses its full
secant equation, while the older block is preserved by the annihilation conditions. -/
theorem mssSequence_pairing (B₀ : Matrix (Fin n) (Fin n) ℝ) (s y c : ℕ → Fin n → ℝ)
    (k : ℕ) (hc : ∀ j < k, c j ⬝ᵥ s j ≠ 0)
    (hold : ∀ j < k, ∀ i < j, c j ⬝ᵥ s i = 0) : ∀ i j, i ≤ j → j < k →
      s i ⬝ᵥ (mssSequence B₀ s y c k *ᵥ s j) = s i ⬝ᵥ y j := by
  -- Separate the newest column from the older block, which later updates preserve.
  induction k with
  | zero => intro i j _ h; omega
  | succ k ih =>
    intro i j hij hjk
    by_cases hj : j = k
    · subst j
      rw [mssSequence, mssUpdate_secant _ _ _ _ (hc k (Nat.lt_succ_self k))]
    · have hjlt : j < k := by omega
      rw [mssSequence, mssUpdate_old_pairing _ _ _ _ _ _
        (hold k (Nat.lt_succ_self k) i (lt_of_le_of_lt hij hjlt))
        (hold k (Nat.lt_succ_self k) j hjlt)]
      exact ih (fun j hj => hc j (Nat.lt_succ_of_lt hj))
        (fun j hj i hi => hold j (Nat.lt_succ_of_lt hj) i hi) i j hij hjlt

/-- Every actual MSS iterate remains symmetric from a symmetric initialization.
Use: the lower-triangular projected identities follow from the proved upper ones.
Article: main_krylov, prop:mss(a).
Proof: induct through the actual symmetric rank-two update. -/
theorem mssSequence_isSymm (B₀ : Matrix (Fin n) (Fin n) ℝ) (hB₀ : B₀.IsSymm)
    (s y c : ℕ → Fin n → ℝ) (k : ℕ) : (mssSequence B₀ s y c k).IsSymm := by
  induction k with
  | zero => exact hB₀
  | succ k ih => exact mssUpdate_isSymm _ ih _ _ _

/-- Compression of a physical operator is the scalar pairing of its actual columns.
Use: translate the recursive observation identities into the article's matrix notation.
Article: main_krylov, prop:mss(a), SᵀB_pS.
Proof: associate the rectangular products and unfold the entry action. -/
theorem column_pairing {p : ℕ} (S : Matrix (Fin n) (Fin p) ℝ)
    (B : Matrix (Fin n) (Fin n) ℝ) (i j : Fin p) :
    (Sᵀ * B * S) i j = (fun a => S a i) ⬝ᵥ (B *ᵥ (fun a => S a j)) := by
  rw [Matrix.mul_assoc]
  rfl

/-- The actual recursively constructed MSS matrix projects to the latest-information model.
Use: finishes the main matrix assertion for every initialization and admissible c,
without assuming a projected-model certificate or even independent columns.
Article: main_krylov, prop:mss(a), SᵀB_pS = T̄.
Proof: the actual upper pairings are the newest observations; symmetry determines
the lower half. Every intermediate matrix is the explicit recursive update. -/
theorem mssSequence_projected {p : ℕ} (B₀ : Matrix (Fin n) (Fin n) ℝ) (hB₀ : B₀.IsSymm)
    (s y c : ℕ → Fin n → ℝ) (hc : ∀ k < p, c k ⬝ᵥ s k ≠ 0)
    (hold : ∀ k < p, ∀ i < k, c k ⬝ᵥ s i = 0) :
    let S : Matrix (Fin n) (Fin p) ℝ := fun a i => s i.val a
    let Y : Matrix (Fin n) (Fin p) ℝ := fun a i => y i.val a
    Sᵀ * mssSequence B₀ s y c p * S = latest (Sᵀ * Y) := by
  -- The actual upper-triangular observation identities and symmetry determine the whole matrix.
  dsimp only
  let S : Matrix (Fin n) (Fin p) ℝ := fun a i => s i.val a
  let Y : Matrix (Fin n) (Fin p) ℝ := fun a i => y i.val a
  change Sᵀ * mssSequence B₀ s y c p * S = latest (Sᵀ * Y)
  have hs : (Sᵀ * mssSequence B₀ s y c p * S).IsSymm := by
    simp only [Matrix.IsSymm, transpose_mul, transpose_transpose,
      (mssSequence_isSymm B₀ hB₀ s y c p).eq, Matrix.mul_assoc]
  have hup (i j : Fin p) (hij : i ≤ j) :
      (Sᵀ * mssSequence B₀ s y c p * S) i j = latest (Sᵀ * Y) i j := by
    rw [latest_apply_of_le _ hij, column_pairing]
    exact mssSequence_pairing B₀ s y c p hc hold i.val j.val hij j.isLt
  ext i j
  rcases le_total i j with hij | hji
  · exact hup i j hij
  · rw [← hs.apply i j, hup j i hji, (latest_isSymm (Sᵀ * Y)).apply i j]

/-- The projected secant mismatch of the actual MSS matrix is exactly the lower defect.
Use: the observed incompatibility is not lost when translating to the physical model.
Article: main_krylov, prop:mss(a), Sᵀ(Y−B_pS) = tril D.
Proof: subtract the proved projected model equation from the raw observations. -/
theorem mssSequence_projected_defect {p : ℕ} (B₀ : Matrix (Fin n) (Fin n) ℝ)
    (hB₀ : B₀.IsSymm) (s y c : ℕ → Fin n → ℝ)
    (hc : ∀ k < p, c k ⬝ᵥ s k ≠ 0)
    (hold : ∀ k < p, ∀ i < k, c k ⬝ᵥ s i = 0) :
    let S : Matrix (Fin n) (Fin p) ℝ := fun a i => s i.val a
    let Y : Matrix (Fin n) (Fin p) ℝ := fun a i => y i.val a
    Sᵀ * (Y - mssSequence B₀ s y c p * S) = strictLower (defect (Sᵀ * Y)) := by
  let S : Matrix (Fin n) (Fin p) ℝ := fun a i => s i.val a
  let Y : Matrix (Fin n) (Fin p) ℝ := fun a i => y i.val a
  change Sᵀ * (Y - mssSequence B₀ s y c p * S) = strictLower (defect (Sᵀ * Y))
  rw [Matrix.mul_sub, ← Matrix.mul_assoc,
    mssSequence_projected B₀ hB₀ s y c hc hold, sub_latest]

/-- The newest stored pair satisfies its full physical secant equation.
Use: the newest secant assertion is separate from the projected older equations.
Article: main_krylov, prop:mss(a), B_p s_(p−1) = y_(p−1), p>0.
Proof: the final actual update enforces its own full secant equation. -/
theorem mssSequence_newest (B₀ : Matrix (Fin n) (Fin n) ℝ)
    (s y c : ℕ → Fin n → ℝ) (p : ℕ) (hc : c p ⬝ᵥ s p ≠ 0) :
    mssSequence B₀ s y c (p + 1) *ᵥ s p = y p := by
  exact mssUpdate_secant _ _ _ _ hc

/-- An invertible full window has exactly the inverse-congruence physical model.
Use: the explicit physical MSS matrix, independent of all choices of admissible c.
Article: main_krylov, prop:mss(a), B_n = S^(−T) T̄ S⁻¹.
Proof: invert both sides of the already proved projected identity by congruence. -/
theorem mssSequence_full (B₀ : Matrix (Fin n) (Fin n) ℝ) (hB₀ : B₀.IsSymm)
    (s y c : ℕ → Fin n → ℝ) (hc : ∀ k < n, c k ⬝ᵥ s k ≠ 0)
    (hold : ∀ k < n, ∀ i < k, c k ⬝ᵥ s i = 0)
    (hS : IsUnit (stepColumns n s).det) :
    let S : Matrix (Fin n) (Fin n) ℝ := fun a i => s i.val a
    let Y : Matrix (Fin n) (Fin n) ℝ := fun a i => y i.val a
    mssSequence B₀ s y c n = Sᵀ⁻¹ * latest (Sᵀ * Y) * S⁻¹ := by
  -- Invert the two actual coordinate factors after identifying the projected MSS matrix.
  let S : Matrix (Fin n) (Fin n) ℝ := fun a i => s i.val a
  let Y : Matrix (Fin n) (Fin n) ℝ := fun a i => y i.val a
  have hS' : IsUnit S.det := hS
  have ht : IsUnit Sᵀ.det := by simpa only [det_transpose] using hS'
  have hp := mssSequence_projected (p := n) B₀ hB₀ s y c hc hold
  change Sᵀ * mssSequence B₀ s y c n * S = latest (Sᵀ * Y) at hp
  have h := congrArg (fun M => Sᵀ⁻¹ * M * S⁻¹) hp
  change mssSequence B₀ s y c n = Sᵀ⁻¹ * latest (Sᵀ * Y) * S⁻¹
  simp only [← Matrix.mul_assoc, nonsing_inv_mul _ ht, one_mul] at h
  simpa only [Matrix.mul_assoc, mul_nonsing_inv _ hS', mul_one] using h

/-- The mismatch on an older secant stays in any subspace containing later c-vectors.
Use: the span hypothesis in the MSS projected-action formula is discharged recursively.
Article: main_krylov, proof of prop:mss(b).
Proof: the newest mismatch is zero; each subsequent update adds only a scalar multiple
of c, as established by the exact old-step action formula. -/
theorem mssSequence_mismatch_mem (W : Submodule ℝ (Fin n → ℝ))
    (B₀ : Matrix (Fin n) (Fin n) ℝ) (s y c : ℕ → Fin n → ℝ)
    (k : ℕ) (hc : ∀ j < k, c j ⬝ᵥ s j ≠ 0)
    (hold : ∀ j < k, ∀ i < j, c j ⬝ᵥ s i = 0)
    (hcW : ∀ j < k, c j ∈ W) : ∀ i < k,
      mssSequence B₀ s y c k *ᵥ s i - y i ∈ W := by
  -- At insertion the mismatch is zero, and every later change stays in the specified subspace.
  induction k with
  | zero => intro i hi; omega
  | succ k ih =>
    intro i hik
    by_cases hi : i = k
    · subst i
      rw [mssSequence_newest B₀ s y c k (hc k (Nat.lt_succ_self k)), sub_self]
      exact W.zero_mem
    · have hik' : i < k := by omega
      rw [mssSequence, mssUpdate_old_action _ _ _ _ _ (hold k (Nat.lt_succ_self k) i hik')]
      have he : ∀ a b d : Fin n → ℝ, a + b - d = (a - d) + b := by intros; abel
      rw [he]
      exact W.add_mem (ih (fun j hj => hc j (Nat.lt_succ_of_lt hj))
        (fun j hj i hi => hold j (Nat.lt_succ_of_lt hj) i hi)
        (fun j hj => hcW j (Nat.lt_succ_of_lt hj)) i hik')
        (W.smul_mem _ (hcW k (Nat.lt_succ_self k)))

/-- A full-column-rank step matrix has a positive-definite ordinary Gram matrix.
Use: the projected MSS action uses an actual Gram inverse, including rectangular windows.
Article: main_krylov, prop:mss(b), nonsingularity of SᵀS.
Source: mathlib positive-definite congruence of the identity.
Proof: injectivity of the column map preserves strict positive definiteness. -/
theorem stepGram_posDef {p : ℕ} (S : Matrix (Fin n) (Fin p) ℝ)
    (hS : Function.Injective S.mulVec) : (Sᵀ * S).PosDef := by
  simpa only [conjTranspose_eq_transpose_of_trivial, Matrix.mul_one] using
    Matrix.PosDef.one.conjTranspose_mul_mul_same (B := S) hS

/-- The actual MSS projected action for every admissible c in the prefix step span.
Use: closes the rectangular-window statement, with an actual recursive MSS matrix.
Article: main_krylov, prop:mss(b), B_pS = Y − S(SᵀS)⁻¹ tril D.
Proof: all mismatch columns lie in the step range; solve their unique Gram-coordinate
system using the already proved projected-defect identity. -/
theorem mssSequence_action {p : ℕ} (B₀ : Matrix (Fin n) (Fin n) ℝ) (hB₀ : B₀.IsSymm)
    (s y c : ℕ → Fin n → ℝ) (hc : ∀ k < p, c k ⬝ᵥ s k ≠ 0)
    (hold : ∀ k < p, ∀ i < k, c k ⬝ᵥ s i = 0)
    (hspan : ∀ k < p, c k ∈ Submodule.span ℝ (Set.range (fun i : Fin (k + 1) => s i.val)))
    (hS : Function.Injective (stepColumns p s).mulVec) :
    let S : Matrix (Fin n) (Fin p) ℝ := fun a i => s i.val a
    let Y : Matrix (Fin n) (Fin p) ℝ := fun a i => y i.val a
    mssSequence B₀ s y c p * S = Y - S * (Sᵀ * S)⁻¹ * strictLower (defect (Sᵀ * Y)) := by
  let S : Matrix (Fin n) (Fin p) ℝ := fun a i => s i.val a
  let Y : Matrix (Fin n) (Fin p) ℝ := fun a i => y i.val a
  let B := mssSequence B₀ s y c p
  change B * S = Y - S * (Sᵀ * S)⁻¹ * strictLower (defect (Sᵀ * Y))
  have hcR (k : ℕ) (hk : k < p) : c k ∈ LinearMap.range S.mulVecLin := by
    apply (Submodule.span_le.mpr ?_) (hspan k hk)
    rintro v ⟨i, rfl⟩
    refine ⟨Pi.single (⟨i.val, by omega⟩ : Fin p) 1, ?_⟩
    simp only [mulVecLin_apply, Matrix.mulVec_single, op_smul_eq_smul, one_smul]
    rfl
  -- Choose actual step coordinates for every mismatch column in the proved range.
  have hm (j : Fin p) : ∃ z : Fin p → ℝ, S *ᵥ z = B *ᵥ s j.val - y j.val :=
    mssSequence_mismatch_mem (LinearMap.range S.mulVecLin) B₀ s y c p hc hold hcR j.val j.isLt
  choose z hz using hm
  let Z : Matrix (Fin p) (Fin p) ℝ := fun i j => z j i
  have hZ : B * S - Y = S * Z := by
    ext a j
    exact (congrFun (hz j) a).symm
  have hd : Sᵀ * (B * S - Y) = -strictLower (defect (Sᵀ * Y)) := by
    have hd := mssSequence_projected_defect (p := p) B₀ hB₀ s y c hc hold
    change Sᵀ * (Y - B * S) = _ at hd
    rw [← neg_sub (B * S) Y, Matrix.mul_neg] at hd
    exact neg_eq_iff_eq_neg.mp hd
  rw [hZ, ← Matrix.mul_assoc] at hd
  have hG : IsUnit (Sᵀ * S).det := isUnit_iff_ne_zero.mpr (stepGram_posDef S hS).det_pos.ne'
  have hz' := congrArg (fun M => (Sᵀ * S)⁻¹ * M) hd
  rw [← Matrix.mul_assoc, nonsing_inv_mul _ hG, one_mul, Matrix.mul_neg] at hz'
  rw [hz', Matrix.mul_neg, ← Matrix.mul_assoc] at hZ
  exact sub_eq_iff_eq_add.mp hZ |>.trans (by abel)

end
end krylov.Secant
