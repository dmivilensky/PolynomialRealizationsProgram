import krylov.Functions.MetricCubicCompatible

/-!
Article: main_krylov, thm:H, exact genuine harmonic increment matrices.
Use: evaluate the real midpoint slices in the original computed CG plane,
before multiplying the actual fresh defect and staircase factors.
Source: the actual harmonic whole-space slice and true CG coordinate pairs.
-/

namespace krylov.Tensor
noncomputable section
open Matrix Finset krylov.Functions krylov.Reference krylov.Variation krylov.LinearAlgebra
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The true newest-step coordinate of each actual compatible midpoint drift.
Article: main_krylov, thm:H. -/
theorem reference_midpoint_last_coordinate (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 2 ≤ referenceAtomCount A hA g)
    (l : Fin (referenceAtomCount A hA g-1)) :
    inner ℝ (canonicalCGUnitStep A g (referenceAtomCount A hA g-1))
      (referenceMidpointDrift A g l.val) =
        if l.val+2=referenceAtomCount A hA g then
          ‖canonicalCGStep A g (referenceAtomCount A hA g-1)‖/2 else 0 := by
  let N := referenceAtomCount A hA g
  let il : Fin N := ⟨N-1,by omega⟩
  have hp := reference_midpoint_unit_pair A hA g il l
  dsimp only [il] at hp
  have hn : ¬N-1=l.val := by have := l.isLt; omega
  simp only [hn,ite_false,zero_add] at hp
  by_cases hl : l.val+2=referenceAtomCount A hA g
  · have heq : N-1=l.val+1 := by omega
    rw [ite_eq_left hl]
    change inner ℝ (canonicalCGUnitStep A g (N-1)) (referenceMidpointDrift A g l.val) =
      ‖canonicalCGStep A g (N-1)‖/2
    simpa only [heq,ite_true,div_eq_mul_inv,mul_comm,one_mul] using hp
  · have heq : ¬N-1=l.val+1 := by omega
    rw [ite_eq_right hl]
    simpa only [heq,ite_false,mul_zero] using hp

/-- The actual harmonic slice matrix in its true first/last CG plane.
Article: main_krylov, thm:H. -/
theorem cubicSliceMatrix_referenceHarmonic (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (a : ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    cubicSliceMatrix (referenceHarmonicTensor A hA g a) v =
      planarMatrix (canonicalCGUnitStep A g 0) (canonicalCGUnitStep A g (referenceAtomCount A hA g-1))
        ((2*a/Real.sqrt 2)*(inner ℝ (canonicalCGUnitStep A g 0) v+
          inner ℝ (canonicalCGUnitStep A g (referenceAtomCount A hA g-1)) v))
        ((2*a/Real.sqrt 2)*(inner ℝ (canonicalCGUnitStep A g 0) v-
          inner ℝ (canonicalCGUnitStep A g (referenceAtomCount A hA g-1)) v))
        (-((2*a/Real.sqrt 2)*(inner ℝ (canonicalCGUnitStep A g 0) v+
          inner ℝ (canonicalCGUnitStep A g (referenceAtomCount A hA g-1)) v))) := by
  apply (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).injective
  change cgOperator (cubicSliceMatrix (referenceHarmonicTensor A hA g a) v) = _
  rw [cubicSliceMatrix_operator]
  exact canonicalHarmonic_slice _ _ _ _

/-- The true first harmonic midpoint slice as a whole-space planar matrix.
Article: main_krylov, thm:H. -/
def referenceHarmonicFirstMatrix (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (a : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  let p := a*‖canonicalCGStep A g 0‖/Real.sqrt 2
  planarMatrix (canonicalCGUnitStep A g 0) (canonicalCGUnitStep A g (referenceAtomCount A hA g-1)) p p (-p)

/-- The true last harmonic midpoint/correction slice as a whole-space planar matrix.
Article: main_krylov, thm:H. -/
def referenceHarmonicLastMatrix (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (a : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  let q := a*‖canonicalCGStep A g (referenceAtomCount A hA g-1)‖/Real.sqrt 2
  planarMatrix (canonicalCGUnitStep A g 0) (canonicalCGUnitStep A g (referenceAtomCount A hA g-1)) q (-q) (-q)

/-- Every genuine harmonic midpoint matrix is exactly one of the two printed
endpoint slices or zero. Article: main_krylov, thm:H. -/
theorem reference_harmonic_increment_matrix (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 3 ≤ referenceAtomCount A hA g)
    (a : ℝ) (l : Fin (referenceAtomCount A hA g-1)) :
    cubicSliceMatrix (referenceHarmonicTensor A hA g a) (referenceMidpointDrift A g l.val) =
      (if l.val=0 then referenceHarmonicFirstMatrix A hA g a else 0) +
        (if l.val+2=referenceAtomCount A hA g then referenceHarmonicLastMatrix A hA g a else 0) := by
  rw [cubicSliceMatrix_referenceHarmonic,
    reference_midpoint_first_coordinate A hA g (by omega) l,
    reference_midpoint_last_coordinate A hA g (by omega) l]
  by_cases h0 : l.val=0
  · have hL : ¬2=referenceAtomCount A hA g := by omega
    simp only [h0,hL,ite_true,ite_false,zero_add,add_zero,sub_zero,
      referenceHarmonicFirstMatrix]
    congr 1 <;> ring
  · by_cases hL : l.val+2=referenceAtomCount A hA g
    · simp only [h0,hL,ite_true,ite_false,zero_add,zero_sub,referenceHarmonicLastMatrix]
      congr 1 <;> ring
    · simp only [h0,hL,ite_false,add_zero,sub_zero,mul_zero,neg_zero,
        planarMatrix,zero_smul,add_zero]

/-- The genuine final correction half-step slice is the very same newest
harmonic endpoint matrix. Article: main_krylov, thm:H. -/
theorem reference_harmonic_correction_matrix (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 2 ≤ referenceAtomCount A hA g) (a : ℝ) :
    cubicSliceMatrix (referenceHarmonicTensor A hA g a)
      ((1/2 : ℝ) • canonicalCGStep A g (referenceAtomCount A hA g-1)) =
        referenceHarmonicLastMatrix A hA g a := by
  let N := referenceAtomCount A hA g
  let i0 : Fin N := ⟨0,by omega⟩
  let il : Fin N := ⟨N-1,by omega⟩
  have hp0 := canonical_step_unit_pair A hA g i0 il
  have hpL := canonical_step_unit_pair A hA g il il
  have hi0L : i0 ≠ il := by
    intro hz
    have hv := congrArg Fin.val hz
    dsimp only [i0,il] at hv
    omega
  rw [ite_eq_right hi0L] at hp0
  rw [ite_eq_left rfl] at hpL
  change inner ℝ (canonicalCGUnitStep A g 0) (canonicalCGStep A g (referenceAtomCount A hA g-1))=0 at hp0
  change inner ℝ (canonicalCGUnitStep A g (referenceAtomCount A hA g-1))
    (canonicalCGStep A g (referenceAtomCount A hA g-1))=‖canonicalCGStep A g (referenceAtomCount A hA g-1)‖ at hpL
  rw [cubicSliceMatrix_referenceHarmonic,inner_smul_right,inner_smul_right,hp0,hpL]
  simp only [mul_zero,zero_add,zero_sub,referenceHarmonicLastMatrix]
  congr 1 <;> ring

end
end krylov.Tensor
