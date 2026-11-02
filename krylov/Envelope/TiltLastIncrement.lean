import krylov.Envelope.DirectionResponse
import krylov.Envelope.TiltSplitting
import krylov.Variation.FCResponse

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:mu(b), thm:select and thm:E, genuine tilt boundary identities.
Use: prove the actual common tilt ignores the true final canonical budget,
vanishes for genuine two-step prefixes and is exactly zero at or after
actual active-spectrum exhaustion.
Source: true measured frozen direction impulse formula, actual canonical
segment derivatives and proved genuine finite CG stopping.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Variation Matrix
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- Every true injection on the genuine canonical source path is exactly its actual cumulative physical drift on the real reference CG step.
Use: Every true injection on the genuine canonical source path is exactly its actual cumulative physical drift on the real reference CG step.
Article: main_krylov, apB:lem:mu(b), thm:select and thm:E, genuine tilt boundary identities.
Proof: Differentiate the actual affine canonical segment before evaluating its genuine reference step. -/
theorem referenceInjection_canonical (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (i : ℕ) :
    referenceInjection (cgOperator base) g (canonicalFCPath base E) (i+1)=
      cumulativeDrift base E i (referenceStep (cgOperator base) g i) := by
  rw [referenceInjection,(canonicalFCPath_calculus base E i).2.deriv]

/-- The actual common tilt depends only on genuine canonical increments strictly before the final horizon budget.
Use: The actual common tilt depends only on genuine canonical increments strictly before the final horizon budget.
Article: main_krylov, apB:lem:mu(b), thm:select and thm:E, genuine tilt boundary identities.
Proof: Use the true frozen displacement-step and direction impulse formulas; every actual contributing segment contains only earlier genuine canonical increments. -/
theorem commonTilt_eq_of_early_increments (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (N : ℕ) (E F : ℕ → Matrix (Fin n) (Fin n) ℝ) (hEF : ∀ l<N-2, E l=F l) :
    commonTilt base g (canonicalFCPath base E) N=commonTilt base g (canonicalFCPath base F) N := by
  -- Inspect actual measured frozen direction impulses to retain the genuine finite source-increment dependence.
  unfold commonTilt
  apply Finset.sum_congr rfl
  intro i _
  rw [frozen_displacement_step,frozen_displacement_step,frozen_direction_formula,frozen_direction_formula]
  congr 4
  apply Finset.sum_congr rfl
  intro j hj
  have hi := i.isLt
  have hj' := Finset.mem_range.mp hj
  have he : cumulativeDrift base E j=cumulativeDrift base F j := by
    have hprefix : (∑ l∈Finset.range j,E l)=∑ l∈Finset.range j,F l :=
      Finset.sum_congr rfl (fun l hl => hEF l (by have := Finset.mem_range.mp hl;omega))
    unfold cumulativeDrift
    rw [hprefix]
  rw [referenceInjection_canonical,referenceInjection_canonical,he]

/-- The genuine common tilt vanishes identically on the actual zero-increment canonical scenario.
Use: The genuine common tilt vanishes identically on the actual zero-increment canonical scenario.
Article: main_krylov, apB:lem:mu(b), thm:select and thm:E, genuine tilt boundary identities.
Proof: All true physical injections are zero, so every genuine frozen direction contribution vanishes. -/
theorem commonTilt_zero_increments (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) :
    commonTilt base g (canonicalFCPath base (fun _ => 0)) N=0 := by
  -- Every true affine zero-increment segment has actual zero derivative injection.
  have hz (j : ℕ) : referenceInjection (cgOperator base) g (canonicalFCPath base (fun _ => 0)) (j+1)=0 := by
    rw [referenceInjection_canonical]
    simp only [cumulativeDrift,Finset.sum_const_zero,Matrix.mul_zero,Matrix.zero_mul,map_zero,_root_.zero_apply]
  unfold commonTilt
  apply Finset.sum_eq_zero
  intro i _
  rw [frozen_displacement_step,frozen_direction_formula]
  simp only [hz,map_zero,Finset.sum_const_zero,smul_zero,inner_zero_right,zero_div,zero_smul]

/-- Every actual genuine two-step common tilt is exactly zero.
Use: Every actual genuine two-step common tilt is exactly zero.
Article: main_krylov, apB:lem:mu(b), thm:select and thm:E, genuine tilt boundary identities.
Proof: Its true earlier-increment dependence range is empty, and the actual zero-increment tilt vanishes. -/
theorem commonTilt_two (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) : commonTilt base g (canonicalFCPath base E) 2=0 := by
  rw [commonTilt_eq_of_early_increments base g 2 E (fun _ => 0) (by intro l hl;omega),commonTilt_zero_increments]
/-- The true common frozen tilt vanishes whenever the actual final reference gradient is zero.
Use: The true common frozen tilt vanishes whenever the actual final reference gradient is zero.
Article: main_krylov, apB:lem:mu(b), thm:select and thm:E, genuine tilt boundary identities.
Proof: Every genuine tilt coordinate pairs its actual displacement variation with that true zero gradient. -/
theorem commonTilt_of_gradient_zero (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (A : ℝ → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (N : ℕ)
    (hz : CG.gradient (cgOperator base) g N=0) : commonTilt base g A N=0 := by
  simp only [commonTilt,hz,inner_zero_left,zero_div,zero_smul,Finset.sum_const_zero]

/-- The genuine common tilt vanishes at and after the actual reference active-spectrum exhaustion, for every true line-operator path.
Use: The genuine common tilt vanishes at and after the actual reference active-spectrum exhaustion, for every true line-operator path.
Article: main_krylov, apB:lem:mu(b), thm:select and thm:E, genuine tilt boundary identities.
Proof: Use proved actual finite CG stopping and the genuine zero-gradient tilt identity. -/
theorem commonTilt_exhausted (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (A : ℝ → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (N : ℕ) (hstop : referenceAtomCount base hb g≤N) : commonTilt base g A N=0 :=
  commonTilt_of_gradient_zero base g A N ((cg_stopping_iff base hb g N).mpr hstop)

end
end krylov.Envelope
