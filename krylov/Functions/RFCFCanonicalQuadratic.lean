import krylov.Functions.RFCFCanonicalDiagonal

/-!
Article: main_krylov, prop:Fcycle(i), exact corrected canonical coefficient.
Use: cancel the genuine full raw reference coordinates after identifying
both the actual latest model and its actual value diagonal as compressions.
Source: genuine physical/canonical reconstruction, true reference incoming
coordinates and exact nonsingular full-reference matrix cancellation.
-/
namespace krylov.Functions
noncomputable section
open Matrix Finset krylov.Methods krylov.Reference krylov.Correction krylov.Secant krylov.Nonlinear
  krylov.Envelope krylov.Variation krylov.Stability
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {k : ℕ}

/-- A real common first-secant drift cancels from every frozen incoming coordinate.
Article: main_krylov, prop:Fcycle(i), genuine drifting first secant. -/
theorem frozenIncoming_common_shift {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Q : E →L[ℝ] E) (g : E) (A : ℕ → E →L[ℝ] E) (C : E →L[ℝ] E) (k : ℕ) :
    frozenIncoming Q g (fun i=>A i+C) k=frozenIncoming Q g A k := by
  simp only [frozenIncoming,add_sub_add_right_eq_sub]

/-- The true modified physical coefficient is its canonical staircase with the genuine compressed model change subtracted.
Article: main_krylov, prop:Fcycle(i), the exact L-Delta_L coefficient.
The compression premise is a finite matrix coordinate identity; the native
value diagonal satisfies it by the preceding actual raw-coordinate theorem. -/
theorem rfcModifiedQuadratic_eq_canonical
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (k+1))) (hN : k+1≤referenceAtomCount base hb g)
    (A B : ℕ → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (D : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (F : EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (hD : D=correctionCompression
      (fun i=>cgOperator (metricRoot base) (referenceModelBasis base g k i)) F) :
    cgOperator (metricRoot base)⁻¹ (rfcModifiedQuadratic base g A B D)=
      ‖canonicalCGStep base g k‖ •
        (staircaseOperator base g (fun l=>physicalCanonicalMatrix base hb (A (l+1)-A l))
          (physicalCanonicalMatrix base hb (B k-A k)) (k+1)-F)
        (freshDefect base g (fun l=>physicalCanonicalMatrix base hb (A (l+1)-A l)) (k+1)) := by
  let E := fun l=>physicalCanonicalMatrix base hb (A (l+1)-A l)
  let P := physicalCanonicalMatrix base hb (B k-A k)
  let C := cgOperator base-A 0
  let U := referenceModelBasis base g k
  let R := fullBasisMatrix U
  let S := physicalOperatorMatrix (staircaseOperator base g E P (k+1)-F)
  have hS : cgOperator S=staircaseOperator base g E P (k+1)-F := physicalOperatorMatrix_operator _
  have hA (i : ℕ) : canonicalFCPath base E 1 i=A i+C := by
    rw [canonical_path_of_physical_differences]
    dsimp only [C]
    abel
  have hB : canonicalCorrectionOperator base E P k=B k+C := by
    rw [canonical_correction_of_physical_differences]
    dsimp only [C]
    abel
  have hpre (i : ℕ) (hi : i≤k) : CG.gradient (cgOperator base) g i≠0 :=
    cg_nonstagnation base hb g i (by omega)
  have hU : LinearIndependent ℝ U := probedStepBasis_independent _
    (rfcMethod_consistent fullMemory (fun _ ha=>ha) 1) _ (cgOperator_positive base hb).1
    (cgOperator_positive base hb).2 g k hpre
  have hL : (Matrix.of fun i j : Fin (k+1)=>inner ℝ (U i)
      ((B k-A (k-(min i j).val)) (U j)))-D=Rᵀ*metricRoot base*S*metricRoot base*R := by
    have hh := reference_model_staircase base hb g k hN E P
    simp only [hA,hB,add_sub_add_right_eq_sub] at hh
    rw [hh,hD]
    have he : correctionCompression (fun i=>cgOperator (metricRoot base) (U i))
        (staircaseOperator base g E P (k+1))-
      correctionCompression (fun i=>cgOperator (metricRoot base) (U i)) F=
      correctionCompression (fun i=>cgOperator (metricRoot base) (U i)) (cgOperator S) := by
      rw [hS]
      ext i j
      simp only [correctionCompression,crossGram,_root_.sub_apply,inner_sub_right,Matrix.sub_apply]
    change _=Rᵀ*metricRoot base*S*metricRoot base*R
    rw [he,fullBasisMatrix_compression,fullBasisMatrix_map]
    simp only [R,transpose_mul,(metricRoot_isSymm base).eq,Matrix.mul_assoc]
  have hH : pairModel U (fun i=>cgOperator base (U i))=Rᵀ*base*R := by
    rw [pairModel_quadratic _ _ (cgOperator_positive base hb).1,fullBasisMatrix_compression]
  have hr : frozenIncoming (cgOperator base) g A k=
      cgOperator (Rᵀ*metricRoot base)
        (‖canonicalCGStep base g k‖ • freshDefect base g E (k+1)) := by
    have hh := frozenIncoming_reference_fresh base hb g k hN E
    rw [show canonicalFCPath base E 1=(fun i=>A i+C) from funext hA,
      frozenIncoming_common_shift] at hh
    rw [hh,projectedResidual_fullBasisMatrix]
    simp only [R,U,map_mul,mul_apply_eq_comp,cgOperator]
  change cgOperator (metricRoot base)⁻¹ (cgOperator (Rᵀ⁻¹*((_-D)*_⁻¹)) _)=_
  rw [hL,hH,hr]
  have hc := full_reference_coefficient base R S hb (fullBasisMatrix_unit _ hU)
    (‖canonicalCGStep base g k‖ • freshDefect base g E (k+1))
  rw [←hS]
  simpa only [map_mul,mul_apply_eq_comp,cgOperator,map_smul] using hc

/-- The printed canonical RFC-F cubic coefficient, with its genuine half-step diagonal replacement.
Article: main_krylov, prop:Fcycle(i), Lambda_F in the actual minimizer metric. -/
def rfcFTensorCanonicalCoefficient
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (D : EuclideanSpace ℝ (Fin (k+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (u : EuclideanSpace ℝ (Fin (k+1))) : EuclideanSpace ℝ (Fin (k+1)) :=
  ‖canonicalCGStep base (cgOperator base u) k‖ •
    (staircaseOperator base (cgOperator base u) (rfcCompatibleIncrements base hb D u)
      (rfcCompatibleCorrection base hb D u k) (k+1)-rfcFReferenceDiagonal base D (cgOperator base u))
      (freshDefect base (cgOperator base u) (rfcCompatibleIncrements base hb D u) (k+1))

/-- The actual physical tensor coefficient is exactly the source's corrected canonical staircase/fresh-defect product.
Article: main_krylov, prop:Fcycle(i), the full native-to-Lambda_F dictionary. -/
theorem rfcFTensorPhysicalCoefficient_eq_canonical
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (D : EuclideanSpace ℝ (Fin (k+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (u : EuclideanSpace ℝ (Fin (k+1)))
    (hN : k+1≤referenceAtomCount base hb (cgOperator base u)) :
    cgOperator (metricRoot base)⁻¹ (rfcFTensorPhysicalCoefficient base D u)=
      rfcFTensorCanonicalCoefficient base hb D u := by
  unfold rfcFTensorPhysicalCoefficient
  rw [rfcModifiedQuadratic_eq_canonical base hb _ hN _ _ _ _
    (rfcFReferenceRawValueChange_eq_compression base hb D u hN)]
  have hA l : rfcTensorSearch (cgOperator base) D u (l+1)-rfcTensorSearch (cgOperator base) D u l=
      D ((1/2:ℝ) • (referenceStep (cgOperator base) (cgOperator base u) l+
        referenceStep (cgOperator base) (cgOperator base u) (l+1))) := by
    simp only [rfcTensorSearch,add_sub_add_left_eq_sub,←map_sub,rfcReferenceSearchMidpoint_sub]
  have hB : rfcTensorCorrection (cgOperator base) D u k-rfcTensorSearch (cgOperator base) D u k=
      D ((1/2:ℝ) • referenceStep (cgOperator base) (cgOperator base u) k) := by
    simp only [rfcTensorCorrection,rfcTensorSearch,add_sub_add_left_eq_sub,←map_sub,rfcReferenceCorrectionMidpoint_sub]
  simp only [hA,hB]
  rfl

end
end krylov.Functions
