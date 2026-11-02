import krylov.Envelope.SelectionNuclearDual
import krylov.Envelope.SelectionSupportLaws

set_option autoImplicit false
/-!
Article: main_krylov, thm:select, selection value budget laws and singleton bounds.
Use: prove the printed convexity, positive homogeneity, monotonicity
and singleton budget comparisons for the actual minimax selection value.
Source: the attained actual nuclear support maximum and elementary
nonnegative finite-sum inequalities.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.LinearAlgebra Polynomial Matrix Finset
open scoped BigOperators Matrix.Norms.L2Operator NNReal
variable {n : ℕ}

/-- The actual minimax selection value is monotone in every nonnegative budget coordinate.
Use: The actual minimax selection value is monotone in every nonnegative budget coordinate.
Article: main_krylov, thm:select, selection value budget laws and singleton bounds.
Proof: Compare the true polynomial support at an actual maximizing direction with the larger-budget maximum. -/
theorem selectionValue_mono (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g)
    (ω η : Fin (N-1) → ℝ≥0) (h : ω≤η) : selectionValue base g N ω≤selectionValue base g N η := by
  obtain ⟨p,hp,hmax⟩ := (selection_nuclear_dual base hb g N hN hcount ω).1
  rw [← hmax]
  exact (selectionSupport_mono base g ω η h p).trans (selectionSupport_le_value base hb g N hN hcount η p hp)

/-- The actual minimax selection value is subadditive in its nonnegative budget profile.
Use: The actual minimax selection value is subadditive in its nonnegative budget profile.
Article: main_krylov, thm:select, selection value budget laws and singleton bounds.
Proof: At an actual maximizing unit polynomial for the sum profile, split its genuine additive support and bound both summands by their true maxima. -/
theorem selectionValue_subadd (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g)
    (ω η : Fin (N-1) → ℝ≥0) :
    selectionValue base g N (ω+η)≤selectionValue base g N ω+selectionValue base g N η := by
  obtain ⟨p,hp,hmax⟩ := (selection_nuclear_dual base hb g N hN hcount (ω+η)).1
  rw [← hmax,selectionSupport_add]
  exact add_le_add (selectionSupport_le_value base hb g N hN hcount ω p hp)
    (selectionSupport_le_value base hb g N hN hcount η p hp)

/-- The actual minimax selection value is positively homogeneous in every nonnegative budget profile, including zero scale.
Use: The actual minimax selection value is positively homogeneous in every nonnegative budget profile, including zero scale.
Article: main_krylov, thm:select, selection value budget laws and singleton bounds.
Proof: Use actual attained maximizers for the scaled and unscaled profiles and the true support homogeneity for both inequalities. -/
theorem selectionValue_smul (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g)
    (r : ℝ≥0) (ω : Fin (N-1) → ℝ≥0) :
    selectionValue base g N (r • ω)=(r : ℝ)*selectionValue base g N ω := by
  -- Actual attained maximizers in both profiles prove equality even when the genuine scaling factor is zero.
  apply le_antisymm
  · obtain ⟨p,hp,hmax⟩ := (selection_nuclear_dual base hb g N hN hcount (r • ω)).1
    rw [← hmax,selectionSupport_smul]
    exact mul_le_mul_of_nonneg_left (selectionSupport_le_value base hb g N hN hcount ω p hp) r.coe_nonneg
  · obtain ⟨p,hp,hmax⟩ := (selection_nuclear_dual base hb g N hN hcount ω).1
    rw [← hmax,← selectionSupport_smul]
    exact selectionSupport_le_value base hb g N hN hcount (r • ω) p hp

/-- Every nonnegative weighted pair of budget profiles satisfies the convex selection inequality; convex combinations are included.
Use: Every nonnegative weighted pair of budget profiles satisfies the convex selection inequality; convex combinations are included.
Article: main_krylov, thm:select, selection value budget laws and singleton bounds.
Proof: Combine the actual profile subadditivity and positive homogeneity. -/
theorem selectionValue_convex (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g)
    (r s : ℝ≥0) (ω η : Fin (N-1) → ℝ≥0) :
    selectionValue base g N (r • ω+s • η)≤(r : ℝ)*selectionValue base g N ω+(s : ℝ)*selectionValue base g N η := by
  simpa only [selectionValue_smul base hb g N hN hcount] using
    selectionValue_subadd base hb g N hN hcount (r • ω) (s • η)

/-- The actual selection value of the zero profile is zero.
Use: The actual selection value of the zero profile is zero.
Article: main_krylov, thm:select, selection value budget laws and singleton bounds.
Proof: Evaluate the zero support at an actual nuclear-dual maximizing polynomial. -/
theorem selectionValue_zero (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g) :
    selectionValue base g N 0=0 := by
  obtain ⟨p,_,hmax⟩ := (selection_nuclear_dual base hb g N hN hcount 0).1
  rw [← hmax,selectionSupport_zero]

/-- The actual selection value is at most the sum of the budgets times their actual unit singleton selection values.
Use: The actual selection value is at most the sum of the budgets times their actual unit singleton selection values.
Article: main_krylov, thm:select, selection value budget laws and singleton bounds.
Proof: Evaluate the genuine nuclear sum at its actual maximizing polynomial and bound each nuclear coefficient by the true corresponding singleton maximum. -/
theorem selectionValue_single_upper (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g)
    (ω : Fin (N-1) → ℝ≥0) :
    selectionValue base g N ω≤∑ l : Fin (N-1), (ω l : ℝ)*selectionValue base g N (Pi.single l 1) := by
  obtain ⟨p,hp,hmax⟩ := (selection_nuclear_dual base hb g N hN hcount ω).1
  rw [← hmax]
  apply sum_le_sum
  intro l _
  apply mul_le_mul_of_nonneg_left _ (ω l).coe_nonneg
  rw [← selectionSupport_single base g l p]
  exact selectionSupport_le_value base hb g N hN hcount (Pi.single l 1) p hp

/-- Every budget times its actual unit singleton selection value is a lower bound for the genuine full-profile selection value.
Use: Every budget times its actual unit singleton selection value is a lower bound for the genuine full-profile selection value.
Article: main_krylov, thm:select, selection value budget laws and singleton bounds.
Proof: The scaled singleton profile is coordinatewise at most the actual profile; use true monotonicity and positive homogeneity. -/
theorem selectionValue_single_lower (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g)
    (ω : Fin (N-1) → ℝ≥0) (l : Fin (N-1)) :
    (ω l : ℝ)*selectionValue base g N (Pi.single l 1)≤selectionValue base g N ω := by
  -- The actual scaled singleton is coordinatewise below the genuine profile, with all absent coordinates exactly zero.
  classical
  rw [← selectionValue_smul base hb g N hN hcount]
  apply selectionValue_mono base hb g N hN hcount
  intro i
  by_cases hi : i=l
  · subst i
    simp
  · simp [hi]
end
end krylov.Envelope
