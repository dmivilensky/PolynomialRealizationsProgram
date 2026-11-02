import krylov.Envelope.SelectionNuclearDual
import krylov.Envelope.SelectionSupportLaws

set_option autoImplicit false
/-!
Article: main_krylov, thm:select, exact final-budget and exhaustion boundaries.
Use: prove actual selection independence of the last source budget and
true zero values at two steps and at genuine active-spectrum exhaustion.
Source: the proved actual zero final compressed sensitivity block,
true attained common-tilt maxima and real finite CG stopping.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Variation krylov.LinearAlgebra Polynomial Matrix Finset
open scoped BigOperators Matrix.Norms.L2Operator NNReal
variable {n : ℕ}

/-- Changing only the actual final budget leaves every genuine degree-admissible polynomial selection support unchanged.
Use: Changing only the actual final budget leaves every genuine degree-admissible polynomial selection support unchanged.
Article: main_krylov, thm:select, exact final-budget and exhaustion boundaries.
Proof: The true final compressed sensitivity is zero; every earlier actual weighted coefficient has unchanged budget. -/
theorem selectionSupport_congr_early (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g)
    (ω η : Fin (N-1) → ℝ≥0) (h : ∀ l : Fin (N-1), l.val<N-2 → ω l=η l)
    (p : ℝ[X]) (hdegree : p.natDegree<N) :
    selectionSupport base g N ω p=selectionSupport base g N η p := by
  -- The actual final sensitivity block vanishes exactly; every earlier term has its genuine unchanged budget.
  apply sum_congr rfl
  intro l _
  by_cases hl : l.val=N-2
  · have hz : selectionKernel base g N p l.val=0 := by
      rw [selectionKernel,hl]
      exact daleckiiKrein_last_compression_zero base hb g N hN hcount p hdegree
    rw [hz,matrixNuclearNorm_zero,mul_zero,mul_zero]
  · rw [h l (by have := l.isLt;omega)]

/-- The genuine actual minimax selection value is independent of the last increment budget.
Use: The genuine actual minimax selection value is independent of the last increment budget.
Article: main_krylov, thm:select, exact final-budget and exhaustion boundaries.
Proof: Evaluate the unchanged true polynomial supports at actual maximizing directions for both profiles. -/
theorem selectionValue_congr_early (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g)
    (ω η : Fin (N-1) → ℝ≥0) (h : ∀ l : Fin (N-1), l.val<N-2 → ω l=η l) :
    selectionValue base g N ω=selectionValue base g N η := by
  -- Compare the two actual attained nuclear maxima using equality of every genuine polynomial support.
  apply le_antisymm
  · obtain ⟨p,hp,hmax⟩ := (selection_nuclear_dual base hb g N hN hcount ω).1
    rw [← hmax,selectionSupport_congr_early base hb g N hN hcount ω η h p hp.1]
    exact selectionSupport_le_value base hb g N hN hcount η p hp
  · obtain ⟨p,hp,hmax⟩ := (selection_nuclear_dual base hb g N hN hcount η).1
    rw [← hmax,← selectionSupport_congr_early base hb g N hN hcount ω η h p hp.1]
    exact selectionSupport_le_value base hb g N hN hcount ω p hp

/-- The actual two-step selection value is zero on every genuine budget profile.
Use: The actual two-step selection value is zero on every genuine budget profile.
Article: main_krylov, thm:select, exact final-budget and exhaustion boundaries.
Proof: The true common tilt is identically zero at two steps, so its actual attained maximum is zero. -/
theorem selectionValue_two (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hcount : 2≤referenceAtomCount base hb g)
    (ω : Fin (2-1) → ℝ≥0) : selectionValue base g 2 ω=0 := by
  obtain ⟨E,_,hmax⟩ := (selectionValue_attained base g 2 ω).1
  dsimp only at hmax
  rw [canonicalTiltLinear_apply base hb g 2 le_rfl hcount E,commonTilt_two,_root_.norm_zero] at hmax
  exact hmax.symm

/-- The actual selection value vanishes at genuine active-spectrum exhaustion.
Use: The actual selection value vanishes at genuine active-spectrum exhaustion.
Article: main_krylov, thm:select, exact final-budget and exhaustion boundaries.
Proof: Every true common tilt is zero when the actual CG reference gradient has stopped; evaluate the real attained maximum. -/
theorem selectionValue_exhausted (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hN : 2≤N) (hcount : N=referenceAtomCount base hb g)
    (ω : Fin (N-1) → ℝ≥0) : selectionValue base g N ω=0 := by
  obtain ⟨E,_,hmax⟩ := (selectionValue_attained base g N ω).1
  dsimp only at hmax
  rw [canonicalTiltLinear_apply base hb g N hN hcount.le E,
    commonTilt_exhausted base hb g (canonicalFCPath base (matrixSequenceExtension (N-1) E)) N hcount.ge,_root_.norm_zero] at hmax
  exact hmax.symm
end
end krylov.Envelope
