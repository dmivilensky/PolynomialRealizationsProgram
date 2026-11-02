import krylov.Envelope.SingletonTilt
import krylov.Envelope.ScenarioBudgets
import krylov.Envelope.TiltLastIncrement

set_option autoImplicit false
/-!
Article: main_krylov, thm:select, actual finite singleton selection scenarios.
Use: identify genuine singleton increment arrays and the true scalar
last-nontrivial common tilt on their actual finite source budgets.
Source: true finite source coordinate extension, genuine spectral zero
budgets and the proved actual singleton common-tilt formula.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Stability krylov.Variation Matrix Finset
open scoped BigOperators Matrix.Norms.L2Operator NNReal
variable {n : ℕ}

/-- The genuine zero extension of a true finite singleton matrix array is exactly the actual chronological singleton sequence.
Use: The genuine zero extension of a true finite singleton matrix array is exactly the actual chronological singleton sequence.
Article: main_krylov, thm:select, actual finite singleton selection scenarios.
Proof: Compare the real valid finite coordinate and zero default using genuine finite-index value equality. -/
theorem matrixSequenceExtension_single {p : ℕ} (l : Fin p) (D : Matrix (Fin n) (Fin n) ℝ) :
    matrixSequenceExtension p (Pi.single l D)=Pi.single l.val D := by
  -- Match true finite coordinate equality with the actual chronological singleton index before comparing zero defaults.
  classical
  funext j
  by_cases hj : j<p
  · change (if hj : j<p then (Pi.single l D : Fin p → Matrix (Fin n) (Fin n) ℝ) ⟨j,hj⟩ else 0)=_
    rw [dite_eq_left hj]
    simp only [Pi.single_apply,Fin.ext_iff]
  · have he : j≠l.val := by have := l.isLt;omega
    simp only [matrixSequenceExtension,dite_eq_right hj,Pi.single_apply,he,ite_false]

/-- Every genuine increment outside the actual nonzero singleton source budget is the real zero matrix.
Use: Every genuine increment outside the actual nonzero singleton source budget is the real zero matrix.
Article: main_krylov, thm:select, actual finite singleton selection scenarios.
Proof: Its true spectral norm is bounded by the actual zero budget, hence vanishes. -/
theorem incrementBudget_single_zero {N : ℕ} (l j : Fin (N-1)) (D : Fin (N-1) → Matrix (Fin n) (Fin n) ℝ)
    (hD : D∈incrementBudget N (Pi.single l 1)) (hj : j≠l) : D j=0 := by
  have hn := (hD j).2
  rw [Pi.single_eq_of_ne hj,NNReal.coe_zero] at hn
  exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))

/-- Every actual finite last-nontrivial singleton budget scenario has exactly the genuine one-pair scalar common-tilt response.
Use: Every actual finite last-nontrivial singleton budget scenario has exactly the genuine one-pair scalar common-tilt response.
Article: main_krylov, thm:select, actual finite singleton selection scenarios.
Proof: Real zero budgets annihilate every other genuine early increment. The actual common tilt is independent of later increments, so its true singleton formula applies. -/
theorem commonTilt_finite_singleton (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (E : Fin (k+2) → Matrix (Fin n) (Fin n) ℝ)
    (hE : E∈incrementBudget (k+3) (Pi.single ⟨k,by omega⟩ 1)) :
    commonTilt base g (canonicalFCPath base (matrixSequenceExtension (k+2) E)) (k+3)=
      -(CG.length (cgOperator base) g (k+2)*Real.sqrt (cgEnergy base g (k+1))/Real.sqrt (cgEnergy base g (k+2))*
        inner ℝ (cgOperator base (cgCanonicalError base g (k+3)))
          (cgOperator (E ⟨k,by omega⟩) (canonicalCGUnitStep base g (k+1)))) • canonicalCGUnitStep base g (k+2) := by
  -- The genuine singleton budget fixes every contributing true early increment; later coordinates cannot affect the actual common tilt.
  have heq : commonTilt base g (canonicalFCPath base (matrixSequenceExtension (k+2) E)) (k+3)=
      commonTilt base g (canonicalFCPath base (Pi.single k (E ⟨k,by omega⟩))) (k+3) := by
    apply commonTilt_eq_of_early_increments
    intro l hl
    have hl' : l<k+2 := by omega
    rw [show matrixSequenceExtension (k+2) E l=E ⟨l,hl'⟩ from dite_eq_left hl']
    by_cases he : l=k
    · subst l
      rw [Pi.single_eq_same]
    · have hf : (⟨l,hl'⟩ : Fin (k+2))≠⟨k,by omega⟩ := by intro h;exact he (congrArg Fin.val h)
      rw [incrementBudget_single_zero (N := k+3) ⟨k,by omega⟩ ⟨l,hl'⟩ E hE hf,Pi.single_eq_of_ne he]
  rw [heq,commonTilt_singleton_increment base hb]
end
end krylov.Envelope
