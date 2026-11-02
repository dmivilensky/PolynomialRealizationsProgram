import krylov.Correction.FlagCoordinates
import krylov.Correction.CycleData

/-!
Article: main_krylov, thm:C, the actual stored reference basis in canonical coordinates.
Use: relate newest-first RFC storage to the existing chronological CG steps,
including the unscaled searched direction in the head position.
Source: actual RFC quadratic consistency, genuine recorded CG steps and the
proved inverse line-length identity for the positive metric-root image.
-/

namespace krylov.Correction
noncomputable section
open Matrix Finset krylov.Reference krylov.Variation krylov.Envelope krylov.Methods krylov.Secant
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The actual augmented full-memory RFC basis on the genuine static quadratic reference.
Use: retain exactly the head direction and newest-first old total steps used by the real solve.
Article: main_krylov, thm:C, the true reference U₀. -/
def referenceModelBasis (base : Matrix (Fin n) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) : Fin (k+1) → EuclideanSpace ℝ (Fin n) :=
  probedStepBasis (rfcMethod fullMemory 1) (fun _ => cgOperator base) (fun _ => cgOperator base) g k

/-- The actual head reference column is the true CG direction.
Use: the terminal direction needs its actual line-length rescaling.
Article: main_krylov, thm:C, d⁰ in the augmented reference window.
Proof: the real retained RFC direction on its quadratic transcript is the true CG direction. -/
theorem referenceModelBasis_zero (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    referenceModelBasis base g k 0=CG.direction (cgOperator base) g k :=
  rfc_reference_direction fullMemory 1 _ (cgOperator_positive base hb).1
    (cgOperator_positive base hb).2 g (fun _ _ ha => ha) k

/-- Every actual older reference column is precisely its genuine chronological CG step.
Use: the storage reversal changes only the finite age index.
Article: main_krylov, thm:C, the old columns s⁰_i.
Proof: genuine RFC quadratic consistency identifies each actual recorded total step with CG. -/
theorem referenceModelBasis_succ (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (j : Fin k) :
    referenceModelBasis base g k j.succ=cgStep base g (k-1-j.val) :=
  quadratic_probedStep_eq_cg _ (rfcMethod_consistent fullMemory (fun _ ha => ha) 1)
    _ (cgOperator_positive base hb).1 (cgOperator_positive base hb).2 g _

/-- The genuine quadratic full reference family is independent of the number of RFC corrections.
Use: every repeated-model expansion uses the same actual CG frame as the one-correction expansion.
Article: main_krylov, thm:C2(b), common quadratic reference U₀.
Proof: the actual head is the true CG direction for every count; all actual
older recorded total steps equal the same genuine CG steps. -/
theorem referenceModelBasis_count (count : ℕ) (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    probedStepBasis (rfcMethod fullMemory count) (fun _ => cgOperator base)
      (fun _ => cgOperator base) g k=referenceModelBasis base g k := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [referenceModelBasis_zero base hb]
    exact rfc_reference_direction fullMemory count _ (cgOperator_positive base hb).1
      (cgOperator_positive base hb).2 g (fun _ _ ha => ha) k
  · rw [referenceModelBasis_succ base hb]
    exact quadratic_probedStep_eq_cg _ (rfcMethod_consistent fullMemory (fun _ ha => ha) count)
      _ (cgOperator_positive base hb).1 (cgOperator_positive base hb).2 g _

/-- The exact scalar conversion from the true chronological step to its actual stored reference column.
Use: only the head direction differs from a true reference step by its inverse line length.
Article: main_krylov, thm:C, current-direction energy normalization. -/
def referenceBasisScale (base : Matrix (Fin n) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) : Fin (k+1) → ℝ :=
  Fin.cons (cgLine base g k)⁻¹ (fun _ => 1)

/-- The positive-root image of every actual reference model column is its genuine CG step with its exact stored scale.
Use: pass the real newest-first model entries to the existing chronological flag identities.
Article: main_krylov, thm:C, A¹ᐟ²U₀=Q C¹ᐟ² in actual storage order.
Proof: the real head direction uses the proved nonzero true CG line length;
every genuine older recorded step is already its actual physical CG step. -/
theorem referenceModelBasis_canonical (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (hN : k+1≤referenceAtomCount base hb g) (i : Fin (k+1)) :
    cgOperator (metricRoot base) (referenceModelBasis base g k i)=
      referenceBasisScale base g k i • canonicalCGStep base g (k-i.val) := by
  -- The actual head is a direction; all genuine older entries are already true total steps.
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [referenceModelBasis_zero base hb]
    exact canonicalCG_direction base g k (canonicalCGStep_ne_zero base hb g k
      (fun a ha => cg_nonstagnation base hb g a (by omega)))
  · rw [referenceModelBasis_succ base hb]
    simp only [referenceBasisScale,Fin.cons_succ,one_smul,Fin.val_succ,
      show k-(j.val+1)=k-1-j.val by omega]
    rfl

/-- Pairing through the actual symmetric metric root moves it to the true reference column.
Use: compare physical incoming coordinates with canonical fresh-defect coordinates.
Article: main_krylov, thm:C, U₀ᵀA¹ᐟ²v=(A¹ᐟ²U₀)ᵀv.
Proof: the genuine metric root is symmetric as a real Euclidean operator. -/
theorem root_pairing (base : Matrix (Fin n) (Fin n) ℝ)
    (u v : EuclideanSpace ℝ (Fin n)) :
    inner ℝ u (cgOperator (metricRoot base) v)=inner ℝ (cgOperator (metricRoot base) u) v :=
  (Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (Matrix.isHermitian_iff_isSymm.mpr (metricRoot_isSymm base)) u v).symm

/-- The real native frozen incoming vector is the true last-step norm times the actual reference projection of the geometric fresh defect.
Use: identify the complete computed leading right-hand side, including its exactly zero searched-direction entry.
Article: main_krylov, thm:C, C^(−1/2)U₀ᵀg′=√c_last Qᵀf̂+O(ω²).
Proof: the true last fresh-defect coordinate vanishes. Each genuine older
coordinate is the proved scaled fresh suffix, and actual physical root
congruence converts its summed canonical increments to the real operator difference. -/
theorem frozenIncoming_reference_fresh (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (hN : k+1≤referenceAtomCount base hb g) (E : ℕ → Matrix (Fin n) (Fin n) ℝ) :
    frozenIncoming (cgOperator base) g (canonicalFCPath base E 1) k=
      projectedResidual (referenceModelBasis base g k)
        (cgOperator (metricRoot base) (‖canonicalCGStep base g k‖ • freshDefect base g E (k+1))) := by
  -- Compare the genuine newest-first coordinates, using the already proved chronological fresh suffix.
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change (0 : ℝ)=inner ℝ (referenceModelBasis base g k 0) _
    rw [root_pairing,referenceModelBasis_canonical base hb g k hN 0]
    simp only [referenceBasisScale,Fin.cons_zero,Fin.val_zero,Nat.sub_zero,
      real_inner_smul_left,real_inner_smul_right]
    have hz := freshDefect_last_coordinate_zero base hb g hN (by omega : 0<k+1) E
    simp only [Nat.add_sub_cancel] at hz
    rw [hz,mul_zero,mul_zero]
  · change inner ℝ (referenceStep (cgOperator base) g (k-1-j.val))
      ((canonicalFCPath base E 1 k-canonicalFCPath base E 1 (k-1-j.val))
        (referenceStep (cgOperator base) g k))=inner ℝ (referenceModelBasis base g k j.succ) _
    rw [root_pairing,referenceModelBasis_succ base hb]
    change _=inner ℝ (canonicalCGStep base g (k-1-j.val))
      (‖canonicalCGStep base g k‖ • freshDefect base g E (k+1))
    have hf := freshDefect_scaled_step_pairing base hb g hN E (i := k-1-j.val) (by omega)
    simp only [Nat.add_sub_cancel] at hf
    rw [hf]
    have hd : canonicalFCPath base E 1 k-canonicalFCPath base E 1 (k-1-j.val)=
        cgOperator (metricRoot base*(∑ l∈Ico (k-1-j.val) k, E l)*metricRoot base) := by
      simp only [canonicalFCPath,one_smul]
      rw [add_sub_add_left_eq_sub,cumulativeDrift_sub base E (by omega)]
      rfl
    rw [hd]
    exact metric_drift_pairing base _ _ _

end
end krylov.Correction
