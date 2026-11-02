import krylov.Envelope.TiltFormula
import krylov.Envelope.FinalErrorImage

set_option autoImplicit false
/-!
Article: main_krylov, thm:select, genuine last-nontrivial singleton tilt.
Use: compute the actual frozen common tilt when only the real last
meaningful source increment is present.
Source: proved printed genuine direction-polynomial tilt double sum,
actual finite source prefix sums and the true zero-length direction response.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Stability krylov.Variation Polynomial Matrix Finset
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The actual common tilt from a genuine last-nontrivial singleton increment has exactly its true single scalar pairing and final CG unit-step direction.
Use: The actual common tilt from a genuine last-nontrivial singleton increment has exactly its true single scalar pairing and final CG unit-step direction.
Article: main_krylov, thm:select, genuine last-nontrivial singleton tilt.
Proof: In the real printed double sum, every true cumulative increment before the singleton vanishes. Only the genuine last earlier/later index pair remains, and its actual zero-length direction polynomial is minus one. -/
theorem commonTilt_singleton_increment (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (D : Matrix (Fin n) (Fin n) ℝ) :
    commonTilt base g (canonicalFCPath base (Pi.single k D)) (k+3)=
      -(CG.length (cgOperator base) g (k+2)*Real.sqrt (cgEnergy base g (k+1))/Real.sqrt (cgEnergy base g (k+2))*
        inner ℝ (cgOperator base (cgCanonicalError base g (k+3))) (cgOperator D (canonicalCGUnitStep base g (k+1)))) •
          canonicalCGUnitStep base g (k+2) := by
  -- Evaluate the genuine singleton cumulative drift before reducing the actual finite chronological triangle.
  have hsum (p : ℕ) : (∑ l∈range p,(Pi.single k D : ℕ → Matrix (Fin n) (Fin n) ℝ) l)=
      if k<p then D else 0 := by
    classical
    simp [Pi.single_apply]
  -- Only the true last nontrivial earlier index and the actual final direction contribute to the genuine tilt.
  rw [commonTilt_canonical_formula base hb]
  unfold canonicalTiltSum
  rw [sum_eq_single (k+1)]
  · rw [sum_eq_single (k+2)]
    · rw [hsum,ite_eq_left (by omega)]
      have hv : directionTiltVector base g (k+3) (k+2) (k+1)=
          -cgOperator base (cgCanonicalError base g (k+3)) := by
        simp only [directionTiltVector,show k+2-(k+1+1)=0 by omega,psi_zero,map_neg,map_one,LinearMap.neg_apply,Module.End.one_apply]
      rw [hv,inner_neg_left]
      congr 1
      ring
    · intro i hi hne
      have := mem_Ico.mp hi
      omega
    · intro hnot
      exact (hnot (mem_Ico.mpr (by omega))).elim
  · intro p hp hne
    have hp' := mem_Ico.mp hp
    have hpk : ¬ k<p := by omega
    rw [hsum,ite_eq_right hpk]
    simp only [cgOperator,map_zero,_root_.zero_apply,inner_zero_right,mul_zero,zero_smul,sum_const_zero]
  · intro hnot
    exact (hnot (mem_Ico.mpr (by omega))).elim
end
end krylov.Envelope
