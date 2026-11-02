import krylov.Stability.UniformFCScaling
import krylov.Correction.ReferenceOperator

/-!
Article: main_krylov, thm:UCq, true reference coefficient homogeneity.
Use: Restore the arbitrary initial-error factor in the whole spectral-class
ordinary-RFC expansion without changing any source operator or uniform constant.
Source: exact CG homogeneity, mathlib's positive normalization identity and
the existing original old-flag, staircase and fresh-defect definitions.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Reference krylov.Secant krylov.Stability krylov.Variation krylov.Envelope
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- A nonzero rescaling of the actual initial gradient preserves its genuine active spectral atom count.
Use: Normalize the original source initial error while retaining the full-atom premise.
Article: main_krylov, thm:UCq.
Proof: In the true Hermitian eigenbasis each canonical initial coordinate is multiplied by the same nonzero scalar; the actual finite set of present eigenvalues is unchanged.
-/
theorem referenceAtomCount_scalar (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (c : ℝ) (hc : c≠0) :
    referenceAtomCount base hb (c • g)=referenceAtomCount base hb g := by
  unfold referenceAtomCount activeSpectralValues
  apply congrArg Finset.card
  apply congrArg (Finset.image hb.1.eigenvalues)
  apply Finset.filter_congr
  intro i _
  simp only [map_smul,real_inner_smul_right,mul_ne_zero_iff]
  exact ⟨And.right,fun h => ⟨hc,h⟩⟩

/-- Every actual canonical CG unit step is unchanged by positive initial-gradient scaling, including zero steps after termination.
Use: Transfer the original reference geometry through error normalization.
Article: main_krylov, thm:UCq.
Proof: True CG step homogeneity and mathlib's zero-safe positive normalization identity cancel the common positive factor.
-/
theorem canonicalCGUnitStep_positive_scalar (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) {c : ℝ} (hc : 0<c) (i : ℕ) :
    canonicalCGUnitStep base (c • g) i=canonicalCGUnitStep base g i := by
  rw [canonicalCGUnitStep,canonicalCGStep_scalar base hb g c hc.ne' i,
    NormedSpace.normalize_smul_of_pos hc]
  rfl

/-- Positive initial-gradient scaling preserves the entire true old reference flag.
Use: Transfer the original staircase operator without an artificial frame premise.
Article: main_krylov, thm:UCq.
Proof: The actual old span has the same normalized CG generators.
-/
theorem oldFlag_positive_scalar (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) {c : ℝ} (hc : 0<c) (l : ℕ) :
    oldFlag base (c • g) l=oldFlag base g l := by
  unfold oldFlag
  congr 2
  funext i
  exact canonicalCGUnitStep_positive_scalar base hb g hc i

/-- The original staircase operator is invariant under every positive initial-gradient rescaling.
Use: Restore the leading operator in the genuine uniform terminal expansion.
Article: main_krylov, thm:UCq.
Proof: Every actual old flag, and hence every true orthogonal compression in the original finite staircase, is unchanged.
-/
theorem staircaseOperator_positive_scalar (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) {c : ℝ} (hc : 0<c)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (F : Matrix (Fin n) (Fin n) ℝ) (N : ℕ) :
    staircaseOperator base (c • g) E F N=staircaseOperator base g E F N := by
  simp only [staircaseOperator,oldFlag_positive_scalar base hb g hc]

/-- The original fresh defect is invariant under every positive initial-gradient rescaling.
Use: Restore the actual reference leading vector with precisely the initial-error factor of the source theorem.
Article: main_krylov, thm:UCq.
Proof: Both the real last normalized CG step and every real old orthogonal projection are unchanged.
-/
theorem freshDefect_positive_scalar (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) {c : ℝ} (hc : 0<c)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (N : ℕ) :
    freshDefect base (c • g) E N=freshDefect base g E N := by
  simp only [freshDefect,oldFlag_positive_scalar base hb g hc,
    canonicalCGUnitStep_positive_scalar base hb g hc]

end
end krylov.Correction
