import krylov.Functions.NativeRFCFTensorTransfer
import krylov.Functions.NativeRFCSpatialResponse
import krylov.Tensor.ValueResponseBound

/-!
Article: main_krylov, prop:Fcycle(i), the true canonical diagonal replacement.
Use: remove the actual raw column scales from the observed model jet and
identify its genuine half-step diagonal in the true CG unit frame.
Source: actual stored-reference basis scales, genuine CG orthonormality and
the real observed scalar third-derivative coefficient.
-/
namespace krylov.Functions
noncomputable section
open Matrix Finset krylov.Methods krylov.Reference krylov.Correction krylov.Secant krylov.Nonlinear krylov.Tensor
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {k n : ℕ}

/-- A genuine diagonal operator in an actual finite orthonormal frame.
Article: main_krylov, prop:Fcycle(i), canonical diagonal model change. -/
def frameDiagonal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι] (h : ι → E) (d : ι → ℝ) : E →L[ℝ] E :=
  ∑ i, d i • InnerProductSpace.rankOne ℝ (h i) (h i)

/-- The actual diagonal operator has its exact unit-frame action.
Article: main_krylov, prop:Fcycle(i), finite orthonormal coordinate algebra. -/
theorem frameDiagonal_apply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (h : ι → E) (hh : Orthonormal ℝ h)
    (d : ι → ℝ) (j : ι) : frameDiagonal h d (h j)=d j • h j := by
  simp only [frameDiagonal, _root_.sum_apply, _root_.smul_apply, InnerProductSpace.rankOne_apply]
  rw [sum_eq_single j]
  · rw [orthonormal_iff_ite.mp hh j j,ite_eq_left rfl,one_smul]
  · intro i _ hij
    rw [orthonormal_iff_ite.mp hh i j,ite_eq_right hij,zero_smul,smul_zero]
  · intro hj
    exact (hj (mem_univ _)).elim

/-- The raw reference value-model change has exactly the canonical half-step scalar coefficients.
Article: main_krylov, prop:Fcycle(i), the actual reference diagonal in chronological unit coordinates. -/
def rfcFReferenceDiagonalCoefficient
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (D : EuclideanSpace ℝ (Fin (k+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (g : EuclideanSpace ℝ (Fin (k+1))) (i : Fin (k+1)) : ℝ :=
  inner ℝ (D (referenceStep (cgOperator base) g i.val) (referenceStep (cgOperator base) g i.val))
    (referenceStep (cgOperator base) g i.val)/(2*‖canonicalCGStep base g i.val‖^2)

/-- The genuine source half-step diagonal operator in the actual chronological CG frame.
Article: main_krylov, prop:Fcycle(i), Delta_L,aa=T[σ_a/2,h_a,h_a]. -/
def rfcFReferenceDiagonal
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (D : EuclideanSpace ℝ (Fin (k+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (g : EuclideanSpace ℝ (Fin (k+1))) : EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)) :=
  frameDiagonal (fun i : Fin (k+1)=>canonicalCGUnitStep base g i.val)
    (rfcFReferenceDiagonalCoefficient base D g)

/-- The genuine diagonal correction acts diagonally on true canonical CG steps.
Article: main_krylov, prop:Fcycle(i), no raw-direction normalization is assumed. -/
theorem rfcFReferenceDiagonal_step_pair
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (D : EuclideanSpace ℝ (Fin (k+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (g : EuclideanSpace ℝ (Fin (k+1)))
    (hN : k+1≤referenceAtomCount base hb g) (i j : Fin (k+1)) :
    inner ℝ (canonicalCGStep base g i.val) (rfcFReferenceDiagonal base D g (canonicalCGStep base g j.val))=
      if i=j then (1/2 : ℝ)*inner ℝ
        (D (referenceStep (cgOperator base) g j.val) (referenceStep (cgOperator base) g j.val))
        (referenceStep (cgOperator base) g j.val) else 0 := by
  let h := fun i : Fin (k+1)=>canonicalCGUnitStep base g i.val
  have hh : Orthonormal ℝ h := by
    rw [orthonormal_iff_ite]
    intro i j
    have hz := orthonormal_iff_ite.mp (canonicalCG_frame base hb g)
      (⟨i.val,i.isLt.trans_le hN⟩ : Fin (referenceAtomCount base hb g))
      (⟨j.val,j.isLt.trans_le hN⟩ : Fin (referenceAtomCount base hb g))
    simpa only [Fin.mk.injEq,Fin.ext_iff] using hz
  have hj : canonicalCGStep base g j.val=‖canonicalCGStep base g j.val‖ • h j :=
    (NormedSpace.norm_smul_normalize _).symm
  have hi : canonicalCGStep base g i.val=‖canonicalCGStep base g i.val‖ • h i :=
    (NormedSpace.norm_smul_normalize _).symm
  have hact := frameDiagonal_apply h hh (rfcFReferenceDiagonalCoefficient base D g) j
  change rfcFReferenceDiagonal base D g (h j)=_ at hact
  rw [hj,map_smul,hact,hi,real_inner_smul_left,real_inner_smul_right,real_inner_smul_right,
    orthonormal_iff_ite.mp hh i j]
  by_cases hij : i=j
  · subst j
    simp only [↓reduceIte,mul_one]
    have hn : ‖canonicalCGStep base g i.val‖≠0 := norm_ne_zero_iff.mpr
      (canonicalCGStep_ne_zero base hb g i.val (fun a ha=>cg_nonstagnation base hb g a (by omega)))
    dsimp only [rfcFReferenceDiagonalCoefficient]
    field_simp
  · simp only [ite_eq_right hij,mul_zero]

/-- The original raw observed diagonal is exactly the compression of the genuine canonical half-step diagonal operator.
Article: main_krylov, prop:Fcycle(i), exact reversal and current-line scale cancellation. -/
theorem rfcFReferenceRawValueChange_eq_compression
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (D : EuclideanSpace ℝ (Fin (k+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (u : EuclideanSpace ℝ (Fin (k+1)))
    (hN : k+1≤referenceAtomCount base hb (cgOperator base u)) :
    rfcFReferenceRawValueChange base D u=
      correctionCompression
        (fun i=>cgOperator (metricRoot base) (referenceModelBasis base (cgOperator base u) k i))
        (rfcFReferenceDiagonal base D (cgOperator base u)) := by
  ext i j
  change _=inner ℝ _ (rfcFReferenceDiagonal base D (cgOperator base u) _)
  dsimp only
  rw [referenceModelBasis_canonical base hb _ k hN i,referenceModelBasis_canonical base hb _ k hN j]
  simp only [map_smul,real_inner_smul_left,real_inner_smul_right]
  have hi : k-i.val=i.rev.val := by simp only [Fin.val_rev]; omega
  have hj : k-j.val=j.rev.val := by simp only [Fin.val_rev]; omega
  rw [hi,hj,rfcFReferenceDiagonal_step_pair base hb D _ hN i.rev j.rev]
  by_cases hij : i=j
  · subst j
    simp only [rfcFReferenceRawValueChange,diagonal_apply_eq,↓reduceIte]
    have hscale : referenceBasisScale base (cgOperator base u) k i=
      ((Fin.cons (CG.length (cgOperator base) (cgOperator base u) k) (fun _ : Fin k=>(1:ℝ)) : Fin (k+1) → ℝ) i)⁻¹ := by
      refine Fin.cases rfl (fun j=>?_) i
      simp only [referenceBasisScale,Fin.cons_succ,inv_one]
    rw [hscale]
    ring
  · have hr : i.rev≠j.rev := fun he=>hij (Fin.rev_injective he)
    simp only [rfcFReferenceRawValueChange,diagonal_apply_ne _ hij,ite_eq_right hr,mul_zero]

end
end krylov.Functions
