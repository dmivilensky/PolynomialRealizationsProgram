import krylov.Envelope.FiniteSingletonTilt
import krylov.Envelope.FinalErrorImageNorm
import krylov.Envelope.RFCSelectionValue
import krylov.Envelope.CanonicalPolynomialFlags
import krylov.LinearAlgebra.OrthogonalPairSupport

set_option autoImplicit false
/-!
Article: main_krylov, thm:select, true sharp last-nontrivial singleton selection value.
Use: prove the genuine minimax singleton coefficient equals the actual
CG scalar times the true final-error base-image norm.
Source: actual singleton common-tilt formula, genuine attained source
budget maxima and the proved real symmetric two-plane spectral attainer.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Stability krylov.Variation krylov.LinearAlgebra Polynomial Matrix Set
open scoped Matrix.Norms.L2Operator NNReal
variable {n : ℕ}

/-- The genuine last-nontrivial singleton selection value is exactly its actual positive-CG scalar times the true final-error base-image norm.
Use: The genuine last-nontrivial singleton selection value is exactly its actual positive-CG scalar times the true final-error base-image norm.
Article: main_krylov, thm:select, true sharp last-nontrivial singleton selection value.
Proof: Every real feasible increment is bounded by true Cauchy--Schwarz. Actual polynomial flag orthogonality places the genuine final-error image orthogonal to the real tested CG unit step, and a concrete symmetric unit-budget cross-plane matrix attains the true product. The actual attained common-tilt maximum gives both genuine inequalities. -/
theorem selectionValue_last_singleton_product (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (hk : k+3<referenceAtomCount base hb g) :
    selectionValue base g (k+3) (Pi.single ⟨k,by omega⟩ 1)=
      (CG.length (cgOperator base) g (k+2)*Real.sqrt (cgEnergy base g (k+1))/Real.sqrt (cgEnergy base g (k+2)))*
        ‖cgOperator base (cgCanonicalError base g (k+3))‖ := by
  -- Work with the genuine tested CG unit step, actual final tilt direction and true final-error base image.
  classical
  let l : Fin (k+2) := ⟨k,by omega⟩
  let a := CG.length (cgOperator base) g (k+2)*Real.sqrt (cgEnergy base g (k+1))/Real.sqrt (cgEnergy base g (k+2))
  let v := cgOperator base (cgCanonicalError base g (k+3))
  let b := canonicalCGUnitStep base g (k+1)
  let h := canonicalCGUnitStep base g (k+2)
  have ha : 0≤a := by
    have hα := cgLength_pos base hb g (k+2) (by omega)
    dsimp only [a]
    positivity
  have hb' : ‖b‖=1 := NormedSpace.norm_normalize
    (canonicalCGStep_ne_zero base hb g (k+1) (fun i hi => cg_nonstagnation base hb g i (by omega)))
  have hh' : ‖h‖=1 := NormedSpace.norm_normalize
    (canonicalCGStep_ne_zero base hb g (k+2) (fun i hi => cg_nonstagnation base hb g i (by omega)))
  have hform (E : Fin (k+2) → Matrix (Fin n) (Fin n) ℝ) (hE : E∈incrementBudget (k+3) (Pi.single l 1)) :
      commonTilt base g (canonicalFCPath base (matrixSequenceExtension (k+2) E)) (k+3)=
        -(a*inner ℝ v (cgOperator (E l) b)) • h := commonTilt_finite_singleton base hb g k E hE
  -- Bound the genuine attained maximum using the real singleton scenario formula and actual unit spectral budget.
  have hmax := selectionValue_commonTilt base hb g (k+3) (by omega) (by omega) (Pi.single l 1)
  change IsGreatest ((fun E : Fin (k+2) → Matrix (Fin n) (Fin n) ℝ =>
    ‖commonTilt base g (canonicalFCPath base (matrixSequenceExtension (k+2) E)) (k+3)‖) ''
      incrementBudget (k+3) (Pi.single l 1)) (selectionValue base g (k+3) (Pi.single l 1)) at hmax
  change selectionValue base g (k+3) (Pi.single l 1)=a*‖v‖
  apply le_antisymm
  · obtain ⟨E,hE,hval⟩ := hmax.1
    rw [← hval]
    change ‖commonTilt base g (canonicalFCPath base (matrixSequenceExtension (k+2) E)) (k+3)‖≤a*‖v‖
    rw [hform E hE,norm_smul,Real.norm_eq_abs,hh',mul_one,abs_neg,abs_mul,abs_of_nonneg ha]
    have hD : ‖E l‖≤1 := by simpa only [Pi.single_eq_same,NNReal.coe_one] using (hE l).2
    exact mul_le_mul_of_nonneg_left (symmetric_pairing_unit_bound v b hb' (E l) hD) ha
  -- Genuine polynomial flag geometry supplies the actual orthogonal plane on which the real symmetric rank-two witness attains equality.
  · have hv : v≠0 := canonical_final_error_image_ne_zero base hb g (k+3) hk
    have horth : v∈(exploredFlag base g (k+2))ᗮ := by
      have ht := canonical_polynomial_error_orthogonal base hb g (k+3) (k+2) (by omega) (X : ℝ[X]) (by simp)
      rw [aeval_X] at ht
      change cgOperator base (cgCanonicalError base g (k+3))∈(exploredFlag base g (k+2))ᗮ at ht
      exact ht
    have hvm : inner ℝ v b=0 := by
      rw [real_inner_comm]
      exact horth _ (Submodule.subset_span ⟨(⟨k+1,by omega⟩ : Fin (k+2)),rfl⟩)
    obtain ⟨D,hD,hDn,hval⟩ := orthogonal_symmetric_pairing_attained v b hv hb' hvm
    let E : Fin (k+2) → Matrix (Fin n) (Fin n) ℝ := Pi.single l D
    -- Insert the concrete genuine matrix into the actual singleton budget, keeping every other real increment exactly zero.
    have hE : E∈incrementBudget (k+3) (Pi.single l 1) := by
      intro j
      by_cases hj : j=l
      · subst j
        simpa only [E,Pi.single_eq_same,symmetricMatrixBall,Set.mem_ofPred_eq,NNReal.coe_one] using And.intro hD hDn
      · simp only [E,Pi.single_eq_of_ne hj]
        exact ⟨Matrix.isSymm_zero,by simp⟩
    have he : ‖commonTilt base g (canonicalFCPath base (matrixSequenceExtension (k+2) E)) (k+3)‖=a*‖v‖ := by
      have hED : E l=D := by simp only [E,Pi.single_eq_same]
      have hp : inner ℝ v (cgOperator D b)=‖v‖ := hval
      rw [hform E hE,hED,hp,norm_smul,Real.norm_eq_abs,hh',mul_one,abs_neg,
        abs_of_nonneg (mul_nonneg ha (norm_nonneg v))]
    exact hmax.2 ⟨E,hE,he⟩
end
end krylov.Envelope
