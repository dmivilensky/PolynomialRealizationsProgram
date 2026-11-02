import krylov.Tensor.ValueReferenceNorm
import krylov.Functions.RFCFOwnCanonical

/-!
Article: main_krylov, prop:Fcycle(i), complete original tensor Lambda_F formula.
Use: connect the genuine derivative-based native coefficient, including an
independently measured own-A0 reference gradient, to the actual printed
corrected tensor model and its genuine 4 n^(3/2) bound.
Source: the true scalar third tensor coordinate pairing, original unit CG
geometry and the proved exact corrected model/fresh coordinate isometry.
-/
namespace krylov.Functions
noncomputable section
open Matrix Finset krylov.Methods krylov.Reference krylov.Correction krylov.Secant krylov.Nonlinear
  krylov.Tensor krylov.Envelope krylov.Variation
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n k : ℕ}

/-- Every genuine physical third-derivative slice is exactly its actual canonical scalar tensor slice.
Article: main_krylov, prop:Fcycle(i), no independent tensor response is assumed. -/
theorem physicalCanonicalMatrix_third_tensor
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (D : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (T : SymmetricCubic (EuclideanSpace ℝ (Fin n)))
    (hT : ∀ a b c,T.form (cgOperator (metricRoot base) a) (cgOperator (metricRoot base) b)
      (cgOperator (metricRoot base) c)=inner ℝ (D a b) c)
    (v : EuclideanSpace ℝ (Fin n)) :
    physicalCanonicalMatrix base hb (D v)=cubicSliceMatrix T (cgOperator (metricRoot base) v) := by
  apply (Matrix.toEuclideanCLM (n:=Fin n) (𝕜:=ℝ)).injective
  change cgOperator _=cgOperator _
  rw [cubicSliceMatrix_operator]
  apply ContinuousLinearMap.ext
  intro b
  apply ext_inner_left ℝ
  intro a
  rw [canonicalVariation_pair]
  let S := metricCoordinates base hb
  have hp := physicalCanonicalMatrix_pairing base hb (D v) (S.symm a) (S.symm b)
  change inner ℝ (S (S.symm a)) (cgOperator (physicalCanonicalMatrix base hb (D v)) (S (S.symm b)))=_ at hp
  rw [S.apply_symm_apply,S.apply_symm_apply] at hp
  rw [hp,real_inner_comm]
  have hh := hT v (S.symm b) (S.symm a)
  change T.form (cgOperator (metricRoot base) v) (S (S.symm b)) (S (S.symm a))=_ at hh
  rw [S.apply_symm_apply,S.apply_symm_apply] at hh
  exact hh.symm.trans (T.swap₂ _ _ _)

/-- The original independently measured reference increments are the genuine scalar tensor's adjacent-midpoint slices.
Article: main_krylov, prop:Fcycle(i), own-A0 compatible tensor dictionary. -/
theorem ownFCCompatibleIncrements_third_tensor
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (D : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (T : SymmetricCubic (EuclideanSpace ℝ (Fin n)))
    (hT : ∀ a b c,T.form (cgOperator (metricRoot base) a) (cgOperator (metricRoot base) b)
      (cgOperator (metricRoot base) c)=inner ℝ (D a b) c)
    (g : EuclideanSpace ℝ (Fin n)) (i : ℕ) :
    ownFCCompatibleIncrements base hb D g i=cubicSliceMatrix T (referenceMidpointDrift base g i) := by
  rw [ownFCCompatibleIncrements,physicalCanonicalMatrix_third_tensor base hb D T hT]
  simp only [map_smul,map_add]
  rfl

/-- The true current half-step correction slice is exactly the scalar tensor's canonical half-step slice.
Article: main_krylov, prop:Fcycle(i), actual last source slice. -/
theorem rfcOwnCompatibleCorrection_third_tensor
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (D : EuclideanSpace ℝ (Fin (k+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (T : SymmetricCubic (EuclideanSpace ℝ (Fin (k+1))))
    (hT : ∀ a b c,T.form (cgOperator (metricRoot base) a) (cgOperator (metricRoot base) b)
      (cgOperator (metricRoot base) c)=inner ℝ (D a b) c)
    (g : EuclideanSpace ℝ (Fin (k+1))) :
    rfcOwnCompatibleCorrection base hb D g=cubicSliceMatrix T ((1/2 : ℝ) • canonicalCGStep base g k) := by
  rw [rfcOwnCompatibleCorrection,physicalCanonicalMatrix_third_tensor base hb D T hT,map_smul]
  rfl

/-- The actually observed diagonal is exactly the printed half-step tensor diagonal, for an independent full-active original reference gradient.
Article: main_krylov, prop:Fcycle(i), true scalar/model diagonal equality. -/
theorem rfcFReferenceDiagonal_third_tensor
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (D : EuclideanSpace ℝ (Fin (k+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (T : SymmetricCubic (EuclideanSpace ℝ (Fin (k+1))))
    (hT : ∀ a b c,T.form (cgOperator (metricRoot base) a) (cgOperator (metricRoot base) b)
      (cgOperator (metricRoot base) c)=inner ℝ (D a b) c)
    (g : EuclideanSpace ℝ (Fin (k+1)))
    (hcount : referenceAtomCount base hb g=k+1) :
    rfcFReferenceDiagonal base D g=tensorReferenceDiagonal base hb g T := by
  unfold rfcFReferenceDiagonal tensorReferenceDiagonal
  have hh : rfcFReferenceDiagonalCoefficient base D g=
      fun i : Fin (k+1)=>T.form ((1/2 : ℝ) • canonicalCGStep base g i.val)
        (canonicalCGUnitStep base g i.val) (canonicalCGUnitStep base g i.val) := by
    funext i
    exact rfcFReferenceDiagonalCoefficient_eq_tensor base hb D T hT g hcount.ge i
  rw [hh]
  let F := fun j : ℕ=>T.form ((1/2 : ℝ) • canonicalCGStep base g j)
    (canonicalCGUnitStep base g j) (canonicalCGUnitStep base g j) •
      InnerProductSpace.rankOne ℝ (canonicalCGUnitStep base g j) (canonicalCGUnitStep base g j)
  change (∑ i : Fin (k+1),F i.val)=∑ i : Fin (referenceAtomCount base hb g),F i.val
  rw [Fin.sum_univ_eq_sum_range,Fin.sum_univ_eq_sum_range,hcount]

/-- The full true derivative-based own-A0 canonical coefficient has exactly the printed Lambda_F coordinates, with the actual last-step factor retained.
Article: main_krylov, prop:Fcycle(i), complete actual coefficient dictionary. -/
theorem rfcFOwnTensorCanonicalCoefficient_coordinates
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (D : EuclideanSpace ℝ (Fin (k+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (T : SymmetricCubic (EuclideanSpace ℝ (Fin (k+1))))
    (hT : ∀ a b c,T.form (cgOperator (metricRoot base) a) (cgOperator (metricRoot base) b)
      (cgOperator (metricRoot base) c)=inner ℝ (D a b) c)
    (g : EuclideanSpace ℝ (Fin (k+1)))
    (hcount : referenceAtomCount base hb g=k+1) :
    (valueReferenceBasis base hb g (by omega) hcount).repr
      (rfcFOwnTensorCanonicalCoefficient base hb D g)=
        ‖canonicalCGStep base g k‖ • valueReferenceCoefficient base hb g T := by
  have hE : ownFCCompatibleIncrements base hb D g=
      fun i=>cubicSliceMatrix T (referenceMidpointDrift base g i) :=
    funext (ownFCCompatibleIncrements_third_tensor base hb D T hT g)
  have hF := rfcOwnCompatibleCorrection_third_tensor base hb D T hT g
  have hD := rfcFReferenceDiagonal_third_tensor base hb D T hT g hcount
  unfold rfcFOwnTensorCanonicalCoefficient
  rw [hE,hF,hD,map_smul]
  have hh := valueReferenceCoefficient_coordinates base hb g (by omega) hcount T
  simp only [tensorReferenceStaircase,hcount,Nat.add_sub_cancel] at hh
  rw [hh]

/-- The genuine original-reference RFC-F cubic coefficient obeys the exact source 4 n^(3/2) two-error bound.
Article: main_krylov, prop:Fcycle(i), true independent-g tensor norm estimate.
The actual scalar third tensor is coupled only through its literal physical
coordinate pairing; genuine derivatives supply it by metricThirdCubic_pair. -/
theorem rfcFOwnTensorCanonicalCoefficient_bound
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (D : EuclideanSpace ℝ (Fin (k+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (T : SymmetricCubic (EuclideanSpace ℝ (Fin (k+1))))
    (hT : ∀ a b c,T.form (cgOperator (metricRoot base) a) (cgOperator (metricRoot base) b)
      (cgOperator (metricRoot base) c)=inner ℝ (D a b) c)
    (g : EuclideanSpace ℝ (Fin (k+1)))
    (hcount : referenceAtomCount base hb g=k+1)
    (hball : ∀ x,‖x‖=1 → |T.form x x x|≤2) :
    ‖rfcFOwnTensorCanonicalCoefficient base hb D g‖≤
      ‖canonicalCGStep base g k‖ *
        (4*(k+1)*Real.sqrt (k+1)*‖cgCanonicalError base g 0‖*‖cgCanonicalError base g 1‖) := by
  have hh := congrArg norm (rfcFOwnTensorCanonicalCoefficient_coordinates base hb D T hT g hcount)
  rw [LinearIsometryEquiv.norm_map,norm_smul,Real.norm_of_nonneg (norm_nonneg _)] at hh
  rw [hh]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  simpa only [hcount,Nat.cast_add,Nat.cast_one] using
    valueReferenceCoefficient_bound base hb g (by omega) T hball

end
end krylov.Functions
