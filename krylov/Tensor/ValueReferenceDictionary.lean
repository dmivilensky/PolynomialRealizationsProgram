import krylov.Functions.RFCFCanonicalTensor
import krylov.Functions.MetricCubicCompatible

/-!
Article: main_krylov, prop:Fcycle(i), exact source tensor coordinate dictionary.
Use: identify the genuine corrected staircase and fresh vector with the
printed valueReferenceModel and referenceTensorFresh in the actual CG frame.
Source: true midpoint telescoping, actual unit-step pairing and the genuine
orthonormal coordinate isometry; no response formula is assumed.
-/
namespace krylov.Tensor
noncomputable section
open Matrix Finset krylov.Functions krylov.Reference krylov.Correction krylov.Secant krylov.Variation krylov.Envelope
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- Actual midpoint-to-anchor vectors lose exactly one genuine adjacent midpoint increment.
Article: main_krylov, prop:Fcycle(i), zeta_i-zeta_(i+1)=xi_i. -/
theorem referenceAnchorDrift_sub_succ (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (i : ℕ) :
    referenceAnchorDrift A g i-referenceAnchorDrift A g (i+1)=referenceMidpointDrift A g i := by
  simp only [referenceAnchorDrift,remainingTail,referenceMidpointDrift,
    cgCanonicalError_succ A hA g (i+1)]
  module

/-- The genuine adjacent midpoint increments telescope to the actual anchor difference.
Article: main_krylov, prop:Fcycle(i), actual compatible suffix. -/
theorem referenceMidpointDrift_sum (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) {i k : ℕ} (hik : i≤k) :
    (∑ l∈Ico i k,referenceMidpointDrift A g l)=referenceAnchorDrift A g i-referenceAnchorDrift A g k := by
  simp_rw [←referenceAnchorDrift_sub_succ A hA g]
  have hh := sum_Ico_sub (fun l=>-referenceAnchorDrift A g l) hik
  simpa only [neg_sub_neg] using hh

/-- Actual tensor slice matrices depend linearly on the genuine slice vector.
Article: main_krylov, prop:Fcycle(i), finite tensor suffix algebra. -/
theorem cubicSliceMatrix_add (T : SymmetricCubic (EuclideanSpace ℝ (Fin n)))
    (x y : EuclideanSpace ℝ (Fin n)) : cubicSliceMatrix T (x+y)=cubicSliceMatrix T x+cubicSliceMatrix T y := by
  simp only [cubicSliceMatrix,map_add]

/-- Actual tensor slice matrices depend linearly on scalar slice multiples.
Article: main_krylov, prop:Fcycle(i), genuine tensor diagonal scale. -/
theorem cubicSliceMatrix_smul (T : SymmetricCubic (EuclideanSpace ℝ (Fin n)))
    (a : ℝ) (x : EuclideanSpace ℝ (Fin n)) : cubicSliceMatrix T (a • x)=a • cubicSliceMatrix T x := by
  simp only [cubicSliceMatrix,map_smul]

/-- The genuine tensor slice matrix of a finite sum is the sum of its actual slice matrices.
Article: main_krylov, prop:Fcycle(i), real finite compatible suffix. -/
theorem cubicSliceMatrix_sum {ι : Type*} (T : SymmetricCubic (EuclideanSpace ℝ (Fin n)))
    (s : Finset ι) (x : ι → EuclideanSpace ℝ (Fin n)) :
    cubicSliceMatrix T (∑ i∈s,x i)=∑ i∈s,cubicSliceMatrix T (x i) := by
  simp only [cubicSliceMatrix,map_sum]

/-- The source's true terminal half-step slice and midpoint suffix give exactly its midpoint-to-final-anchor tensor slice.
Article: main_krylov, prop:Fcycle(i), the actual latest-model tensor argument. -/
theorem reference_tensor_suffix (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 0<referenceAtomCount A hA g)
    (T : SymmetricCubic (EuclideanSpace ℝ (Fin n)))
    {i : ℕ} (hi : i<referenceAtomCount A hA g) :
    cubicSliceMatrix T ((1/2 : ℝ) • canonicalCGStep A g (referenceAtomCount A hA g-1))+
      ∑ l∈Ico i (referenceAtomCount A hA g-1),cubicSliceMatrix T (referenceMidpointDrift A g l)=
        cubicSliceMatrix T (referenceAnchorDrift A g i) := by
  rw [←cubicSliceMatrix_sum,←cubicSliceMatrix_add,referenceMidpointDrift_sum A hA g (by omega)]
  have hh : referenceAnchorDrift A g (referenceAtomCount A hA g-1)=
      (1/2 : ℝ) • canonicalCGStep A g (referenceAtomCount A hA g-1) := by
    rw [referenceAnchorDrift,reference_last_tail_zero A hA g hN,add_zero]
  rw [hh]
  congr 1
  abel

/-- The actual tensor latest-information staircase before its observed value diagonal is removed.
Article: main_krylov, prop:Fcycle(i), original tensor staircase. -/
def tensorReferenceStaircase (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (T : SymmetricCubic (EuclideanSpace ℝ (Fin n))) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  staircaseOperator A g (fun l=>cubicSliceMatrix T (referenceMidpointDrift A g l))
    (cubicSliceMatrix T ((1/2 : ℝ) • canonicalCGStep A g (referenceAtomCount A hA g-1)))
    (referenceAtomCount A hA g)

/-- The true tensor half-step diagonal in the actual active CG unit frame.
Article: main_krylov, prop:Fcycle(i), diagonal replaced by the remaining tail. -/
def tensorReferenceDiagonal (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (T : SymmetricCubic (EuclideanSpace ℝ (Fin n))) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  frameDiagonal (fun i : Fin (referenceAtomCount A hA g)=>canonicalCGUnitStep A g i.val)
    (fun i=>T.form ((1/2 : ℝ) • canonicalCGStep A g i.val)
      (canonicalCGUnitStep A g i.val) (canonicalCGUnitStep A g i.val))

/-- The genuine latest-information tensor staircase has exactly its printed midpoint-anchor unit-frame entries.
Article: main_krylov, prop:Fcycle(i), literal off-diagonal tensor entries. -/
theorem tensorReferenceStaircase_unit_pair
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (T : SymmetricCubic (EuclideanSpace ℝ (Fin n)))
    (i j : Fin (referenceAtomCount A hA g)) :
    inner ℝ (canonicalCGUnitStep A g i.val)
      (tensorReferenceStaircase A hA g T (canonicalCGUnitStep A g j.val))=
      T.form (referenceAnchorDrift A g (max i.val j.val))
        (canonicalCGUnitStep A g i.val) (canonicalCGUnitStep A g j.val) := by
  have hp := staircase_step_pairing A hA g le_rfl
    (fun l=>cubicSliceMatrix T (referenceMidpointDrift A g l))
    (cubicSliceMatrix T ((1/2 : ℝ) • canonicalCGStep A g (referenceAtomCount A hA g-1))) i.isLt j.isLt
  rw [reference_tensor_suffix A hA g (Nat.zero_lt_of_lt i.isLt) T (max_lt_iff.mpr ⟨i.isLt,j.isLt⟩),cubicSliceMatrix_operator,
    canonicalVariation_pair] at hp
  have hsi : canonicalCGStep A g i.val=‖canonicalCGStep A g i.val‖ • canonicalCGUnitStep A g i.val :=
    (NormedSpace.norm_smul_normalize _).symm
  have hsj : canonicalCGStep A g j.val=‖canonicalCGStep A g j.val‖ • canonicalCGUnitStep A g j.val :=
    (NormedSpace.norm_smul_normalize _).symm
  rw [hsi,hsj] at hp
  simp only [map_smul,real_inner_smul_left,real_inner_smul_right,_root_.smul_apply,smul_eq_mul] at hp
  have hni : ‖canonicalCGStep A g i.val‖≠0 := norm_ne_zero_iff.mpr
    (canonicalCGStep_ne_zero A hA g i.val (fun a ha=>cg_nonstagnation A hA g a (by omega)))
  have hnj : ‖canonicalCGStep A g j.val‖≠0 := norm_ne_zero_iff.mpr
    (canonicalCGStep_ne_zero A hA g j.val (fun a ha=>cg_nonstagnation A hA g a (by omega)))
  apply (mul_left_cancel₀ (mul_ne_zero hni hnj))
  simpa only [tensorReferenceStaircase,mul_assoc,mul_left_comm,mul_comm] using hp

/-- The actual corrected tensor staircase has exactly the genuine printed value-reference model entries.
Article: main_krylov, prop:Fcycle(i), full corrected model dictionary. -/
theorem tensorReferenceCorrected_unit_pair
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (T : SymmetricCubic (EuclideanSpace ℝ (Fin n)))
    (i j : Fin (referenceAtomCount A hA g)) :
    inner ℝ (canonicalCGUnitStep A g i.val)
      ((tensorReferenceStaircase A hA g T-tensorReferenceDiagonal A hA g T)
        (canonicalCGUnitStep A g j.val))=valueReferenceModel A hA g T i j := by
  rw [_root_.sub_apply,inner_sub_right,tensorReferenceStaircase_unit_pair]
  have hd := frameDiagonal_apply (fun i : Fin (referenceAtomCount A hA g)=>canonicalCGUnitStep A g i.val)
    (canonicalCG_frame A hA g)
    (fun i=>T.form ((1/2 : ℝ) • canonicalCGStep A g i.val)
      (canonicalCGUnitStep A g i.val) (canonicalCGUnitStep A g i.val)) j
  change tensorReferenceDiagonal A hA g T (canonicalCGUnitStep A g j.val)=_ at hd
  rw [hd,real_inner_smul_right,orthonormal_iff_ite.mp (canonicalCG_frame A hA g) i j]
  by_cases hij : i=j
  · subst j
    simp only [↓reduceIte,mul_one,valueReferenceModel,max_self]
    simp only [referenceAnchorDrift,map_add,_root_.add_apply]
    ring
  · simp only [ite_eq_right hij,mul_zero,sub_zero,valueReferenceModel]

/-- The genuine tensor fresh defect has exactly the printed reference tensor coordinates.
Article: main_krylov, prop:Fcycle(i), actual fresh-vector dictionary. -/
theorem tensorReferenceFresh_unit_pair
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 0<referenceAtomCount A hA g)
    (T : SymmetricCubic (EuclideanSpace ℝ (Fin n)))
    (i : Fin (referenceAtomCount A hA g)) :
    inner ℝ (canonicalCGUnitStep A g i.val)
      (freshDefect A g (fun l=>cubicSliceMatrix T (referenceMidpointDrift A g l))
        (referenceAtomCount A hA g))=referenceTensorFresh A hA g T i := by
  have hp := freshDefect_scaled_step_pairing A hA g le_rfl
    (fun l=>cubicSliceMatrix T (referenceMidpointDrift A g l)) i.isLt
  rw [←cubicSliceMatrix_sum,referenceMidpointDrift_sum A hA g (by omega),
    cubicSliceMatrix_operator,canonicalVariation_pair] at hp
  have hsi : canonicalCGStep A g i.val=‖canonicalCGStep A g i.val‖ • canonicalCGUnitStep A g i.val :=
    (NormedSpace.norm_smul_normalize _).symm
  have hsl : canonicalCGStep A g (referenceAtomCount A hA g-1)=
      ‖canonicalCGStep A g (referenceAtomCount A hA g-1)‖ •
        canonicalCGUnitStep A g (referenceAtomCount A hA g-1) :=
    (NormedSpace.norm_smul_normalize _).symm
  conv at hp => rhs; rw [hsi,hsl]
  conv at hp => lhs; rw [hsi]
  simp only [map_smul,real_inner_smul_left,real_inner_smul_right,_root_.smul_apply,smul_eq_mul] at hp
  have hni : ‖canonicalCGStep A g i.val‖≠0 := norm_ne_zero_iff.mpr
    (canonicalCGStep_ne_zero A hA g i.val (fun a ha=>cg_nonstagnation A hA g a (by omega)))
  have hnl : ‖canonicalCGStep A g (referenceAtomCount A hA g-1)‖≠0 := norm_ne_zero_iff.mpr
    (canonicalCGStep_ne_zero A hA g _ (fun a ha=>cg_nonstagnation A hA g a (by omega)))
  apply (mul_left_cancel₀ (mul_ne_zero hni hnl))
  change (_*_)*inner ℝ _ _=(_*_)*T.form _ _ _
  convert hp using 1 <;> ring

end
end krylov.Tensor
