import krylov.Envelope.DaleckiiKreinPairing

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:DK and thm:select, actual zero final compressed sensitivity block.
Use: prove the genuine last canonical budget contributes exactly zero
to the printed real Daleckii--Krein nuclear dual, from the true actual
common-tilt last-increment identity rather than a presumed cancellation.
Source: actual derived common-tilt polynomial pairing, genuine final
budget irrelevance and positivity of the true Frobenius squared norm.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Stability krylov.Variation krylov.LinearAlgebra Polynomial Matrix Finset
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The genuine printed last complementary-flag compression of the actual Daleckii--Krein matrix is exactly zero on every true degree-admissible active reference prefix.
Use: The genuine printed last complementary-flag compression of the actual Daleckii--Krein matrix is exactly zero on every true degree-admissible active reference prefix.
Article: main_krylov, apB:lem:DK and thm:select, actual zero final compressed sensitivity block.
Proof: The actual compressed matrix is symmetric. Use it as the sole genuine final increment: the true common tilt vanishes by proved last-budget irrelevance. The actual Daleckii--Krein identity then gives its genuine Frobenius squared norm equal to zero, so the real matrix vanishes. -/
theorem daleckiiKrein_last_compression_zero (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g)
    (p : ℝ[X]) (hdegree : p.natDegree<N) :
    canonicalComplementMatrix base g (N-2)*daleckiiKreinMatrix base g N p*canonicalComplementMatrix base g (N-2)=0 := by
  -- Test the genuine final compressed sensitivity block against itself as an actual symmetric last-only increment.
  let Z := daleckiiKreinMatrix base g N p
  let P := canonicalComplementMatrix base g (N-2)
  let K := P*Z*P
  have hK : K.IsSymm := by
    change (P*Z*P)ᵀ=P*Z*P
    dsimp only [P,Z]
    simp only [transpose_mul,(canonicalComplementMatrix_symm base g (N-2)).eq,(daleckiiKreinMatrix_symm base g N p).eq,mul_assoc]
  let E := fun l : ℕ => if l=N-2 then K else 0
  have hE (l : ℕ) : (E l).IsSymm := by
    dsimp only [E]
    split
    · exact hK
    · exact Matrix.isSymm_zero
  have hzero : commonTilt base g (canonicalFCPath base E) N=0 := by
    rw [commonTilt_eq_of_early_increments base g N E (fun _ => 0) (by
      intro l hl
      exact ite_eq_right (by omega)),commonTilt_zero_increments]
  -- The true common-tilt functional is zero on the actual last-only scenario; its genuine Frobenius self-pairing forces the real block to vanish.
  have hpair := actual_tilt_daleckiiKrein_pairing base hb g N hN hcount E (fun l _ => hE l) p hdegree
  rw [hzero,inner_zero_right] at hpair
  have hsum : (∑ l∈range (N-1), inner ℝ (frobeniusVector (E l))
      (frobeniusVector (canonicalComplementMatrix base g l*daleckiiKreinMatrix base g N p*canonicalComplementMatrix base g l)))=
      inner ℝ (frobeniusVector K) (frobeniusVector K) := by
    rw [sum_eq_single (N-2)]
    · simp only [E,ite_true]
      rfl
    · intro l _ hl
      have hf0 : frobeniusVector (0 : Matrix (Fin n) (Fin n) ℝ)=0 := (frobeniusVector_eq_zero_iff _).mpr rfl
      simp only [E,ite_eq_right hl,hf0,inner_zero_left]
    · intro hnot
      exact (hnot (mem_range.mpr (by omega))).elim
  rw [hsum] at hpair
  have hz : frobeniusVector K=0 := inner_self_eq_zero.mp hpair.symm
  exact (frobeniusVector_eq_zero_iff K).mp hz
end
end krylov.Envelope
