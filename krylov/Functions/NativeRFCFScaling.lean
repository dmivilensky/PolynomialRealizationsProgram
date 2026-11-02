import krylov.Functions.RFCLineCoordinates
import krylov.Functions.NativeRFCFValueJets

/-!
Article: main_krylov, prop:Fcycle, exact actual modified-source normalization.
Use: scale the genuine old RFC history and true changed last solve together;
the observed value correction has coefficient-space degree two. The real
scalar observations remain actual ones throughout the normalization.
Source: previously proved genuine RFC history homogeneity and true inverse
coefficient congruence, including totalized singular models.
-/
namespace krylov.Functions
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Correction
open scoped InnerProductSpace Matrix Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {k : ℕ}

/-- The genuine raw full RFC basis has degree one in its actual initial gradient.
Article: main_krylov, prop:Fcycle, no scaled-basis hypothesis. -/
theorem rfc_probedStepBasis_scalar (A B : ℕ → E →L[ℝ] E) (g : E) (c : ℝ) (hc : c≠0) :
    probedStepBasis (rfcMethod fullMemory 1) A B (c • g) k=
      fun i=>c • probedStepBasis (rfcMethod fullMemory 1) A B g k i := by
  have h := rfc_scalar fullMemory 1 A B g c hc (k+1)
  funext i
  refine Fin.cases ?_ (fun j=>?_) i
  · exact (h.2 k (by omega)).1
  · exact (h.2 (k-1-j.val) (by omega)).2.1

/-- Actual full RFC probe/secant images have exactly the same true source scale.
Article: main_krylov, prop:Fcycle, genuine model homogeneity. -/
theorem rfc_probedImageBasis_scalar (A B : ℕ → E →L[ℝ] E) (g : E) (c : ℝ) (hc : c≠0) :
    probedImageBasis (rfcMethod fullMemory 1) A B (c • g) k=
      fun i=>c • probedImageBasis (rfcMethod fullMemory 1) A B g k i := by
  have h := rfc_scalar fullMemory 1 A B g c hc (k+1)
  funext i
  refine Fin.cases ?_ (fun j=>?_) i
  · change A k ((rfcMethod fullMemory 1).direction (methodRun _ _ _ (c • g) k))=_
    rw [(h.2 k (by omega)).1,map_smul]
    rfl
  · exact (h.2 (k-1-j.val) (by omega)).2.2

/-- The actually searched incoming gradient before the changed final solve
has true degree one in its real initial observation.
Article: main_krylov, prop:Fcycle. -/
theorem rfc_fullPostSearch_scalar (A B : ℕ → E →L[ℝ] E) (g : E) (c : ℝ) (hc : c≠0) :
    fullPostSearch 1 A B (c • g) k=c • fullPostSearch 1 A B g k := by
  have hg := (rfc_scalar fullMemory 1 A B g c hc k).1
  have hd := (rfc_scalar fullMemory 1 A B g c hc (k+1)).2 k (by omega)
  change searchedGradient (probedGradient _ _ _ (c • g) k) _ _=_
  rw [hg,hd.1,map_smul,searchedGradient_scalar _ _ _ c hc]
  rfl

/-- The genuine changed last query scales by degree one when its real model change scales by degree two.
Article: main_krylov, prop:Fcycle, actual physical/source normalization. -/
theorem rfcModifiedCorrection_scalar (A B : ℕ → E →L[ℝ] E) (g : E)
    (D : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (c : ℝ) (hc : c≠0) :
    rfcModifiedCorrection A B (c • g) (c^2 • D)=c • rfcModifiedCorrection A B g D := by
  rw [rfcModifiedCorrection,rfcModifiedCorrection,rfc_probedStepBasis_scalar A B g c hc,
    rfc_probedImageBasis_scalar A B g c hc,pairModel_scalar,rfc_fullPostSearch_scalar A B g c hc]
  rw [pow_two,←smul_add,modelCoefficients_scalar _ _ _ c hc,combine_scalar]

/-- The true normalized observed value change in raw newest-first coordinates.
Article: main_krylov, prop:Fcycle. Its entries use the actual scalar defects
and actual split, with their actual current-line squared coordinate scale. -/
def rfcFNormalizedRawValueChange (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (r : ℝ) (x₀ : E) (k : ℕ) (ε : ℝ) (c : Fin (k+1) → ℝ) : Matrix (Fin (k+1)) (Fin (k+1)) ℝ :=
  Matrix.diagonal (fun i=>rfcFNormalizedValueDiagonal T f G r x₀ k ε i.rev/c i^2)

/-- Scaling the actual normalized raw value change back gives exactly its genuine observed physical model change.
Article: main_krylov, prop:Fcycle, exact diagonal normalization. -/
theorem rfcFNormalizedRawValueChange_scale (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (r : ℝ) (x₀ : E) (k : ℕ) (ε : ℝ) (hε : ε≠0) (c : Fin (k+1) → ℝ) :
    ε^2 • rfcFNormalizedRawValueChange T f G r x₀ k ε c=rfcFRawValueChange T f G r x₀ k c := by
  ext i j
  by_cases hij : i=j
  · subst j
    simp only [rfcFNormalizedRawValueChange,rfcFRawValueChange,Matrix.smul_apply,smul_eq_mul,
      diagonal_apply_eq,rfcFNormalizedValueDiagonal,rfcFValueDiagonal]
    rw [←mul_div_assoc,mul_div_cancel₀ _ (pow_ne_zero 2 hε)]
    ring
  · simp only [rfcFNormalizedRawValueChange,rfcFRawValueChange,Matrix.smul_apply,smul_eq_mul,
      diagonal_apply_ne _ hij,mul_zero]

/-- The actual accepted RFC-F query is its genuine normalized changed-model
query multiplied by the real initial source scale.
Article: main_krylov, prop:Fcycle, before enclosing the new correction endpoint. -/
theorem rfcFCorrectionStep_normalized_operator (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (r : ℝ) (x₀ : E) (A B : ℕ → E →L[ℝ] E) (k : ℕ)
    (hp : ∀ j≤k,rfcFunctionRun T f G fullMemory r x₀ j=methodRun (rfcMethod fullMemory 1) A B (G x₀) j)
    (α : ℝ) (hα : α≠0)
    (hs : rfcFunctionLineStep T f fullMemory r x₀ (rfcFunctionRun T f G fullMemory r x₀ k)=
      α • rfcFunctionDirection fullMemory (rfcFunctionRun T f G fullMemory r x₀ k))
    (hy : G (rfcFAnchor T f G r x₀ k)-G (rfcFunctionPoint T f G fullMemory r x₀ k)=
      α • A k (rfcFunctionDirection fullMemory (rfcFunctionRun T f G fullMemory r x₀ k)))
    (hpost : G (rfcFAnchor T f G r x₀ k)=fullPostSearch 1 A B (G x₀) k)
    (hgate : rfcFunctionGate fullMemory (rfcFunctionRun T f G fullMemory r x₀ k))
    (ε : ℝ) (hε : ε≠0) :
    rfcFCorrectionStep T f G r x₀ k=ε •
      rfcModifiedCorrection A B (ε⁻¹ • G x₀)
        (rfcFNormalizedRawValueChange T f G r x₀ k ε (Fin.cons α (fun _=>1))) := by
  rw [rfcFCorrectionStep_modified_operator T f G r x₀ A B k hp α hα hs hy hpost hgate,
    ←rfcFNormalizedRawValueChange_scale T f G r x₀ k ε hε]
  have he : G x₀=ε • (ε⁻¹ • G x₀) := by rw [smul_smul,mul_inv_cancel₀ hε,one_smul]
  conv_lhs => arg 3; rw [he]
  exact rfcModifiedCorrection_scalar A B (ε⁻¹ • G x₀) _ ε hε

/-- Genuine nonzero initial-observation scaling preserves the actual old-pair RFC gate.
Article: main_krylov, prop:Fcycle, transfer of its true normalized branch domain. -/
theorem rfcFunctionGate_scalar (A B : ℕ → E →L[ℝ] E) (g : E)
    (c : ℝ) (hc : c≠0) (k : ℕ) (hk : 0<k) :
    rfcFunctionGate fullMemory (methodRun (rfcMethod fullMemory 1) A B (c • g) k) ↔
      rfcFunctionGate fullMemory (methodRun (rfcMethod fullMemory 1) A B g k) := by
  rw [rfcFunctionGate_operator_iff A B (c • g) k hk,rfcFunctionGate_operator_iff A B g k hk]
  have h := rfc_scalar fullMemory 1 A B g c hc k
  have hS : (fun i : Fin k=>probedStep (rfcMethod fullMemory 1) A B (c • g) (k-1-i.val))=
      fun i : Fin k=>c • probedStep (rfcMethod fullMemory 1) A B g (k-1-i.val) :=
    funext fun i=>(h.2 (k-1-i.val) (by omega)).2.1
  have hY : (fun i : Fin k=>probedSecant (rfcMethod fullMemory 1) A B (c • g) (k-1-i.val))=
      fun i : Fin k=>c • probedSecant (rfcMethod fullMemory 1) A B g (k-1-i.val) :=
    funext fun i=>(h.2 (k-1-i.val) (by omega)).2.2
  rw [hS,hY,pairDefect_scalar _ _ c hc]

/-- The actual modified returned gradient scales with its true changed correction query.
Article: main_krylov, prop:Fcycle, physical gradient normalization. -/
theorem rfcModifiedTerminalGradient_scalar (A B : ℕ → E →L[ℝ] E) (g : E)
    (D : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (c : ℝ) (hc : c≠0) :
    modifiedTerminalGradient A B (c • g) k (c^2 • D)=c • modifiedTerminalGradient A B g k D := by
  change fullPostSearch 1 A B (c • g) k+B k (rfcModifiedCorrection A B (c • g) (c^2 • D))=_
  rw [rfc_fullPostSearch_scalar A B g c hc,rfcModifiedCorrection_scalar A B g D c hc,map_smul,←smul_add]
  rfl

/-- The actual physical current line quotient is unchanged by genuine nonzero initial-observation scaling.
Article: main_krylov, prop:Fcycle, true raw-column normalization. -/
theorem rfcPhysicalLineScale_scalar {j : ℕ} (base : Matrix (Fin (j+1)) (Fin (j+1)) ℝ)
    (g : EuclideanSpace ℝ (Fin (j+1))) (Θ : RFCPhysicalData j) (c : ℝ) (hc : c≠0) :
    rfcPhysicalLineScale base (c • g,Θ)=rfcPhysicalLineScale base (g,Θ) := by
  let A := rfcPhysicalSearch base Θ
  let B := rfcPhysicalCorrection base Θ
  have hg := (rfc_scalar fullMemory 1 A B g c hc j).1
  have hd := (rfc_scalar fullMemory 1 A B g c hc (j+1)).2 j (by omega)
  change lineLength (probedGradient (rfcMethod fullMemory 1) A B (c • g) j)
    ((rfcMethod fullMemory 1).direction (methodRun _ _ _ (c • g) j)) _=_
  rw [hg,hd.1,map_smul,lineLength_scalar _ _ _ c hc]
  rfl

end
end krylov.Functions
