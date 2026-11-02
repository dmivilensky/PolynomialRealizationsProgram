import krylov.Correction.ModifiedCanonical

/-!
Article: Lemma B.21 [apD:lem-model] of krylov.tex.
Use: identify a true energy-scaled diagonal coefficient change with the
diagonal operator in the genuine normalized CG frame, in actual storage order.
Source: true reference column scaling, computed CG orthonormality and exact
inverse-congruence cancellation; physical stored columns remain unnormalized.
-/

namespace krylov.Correction
noncomputable section
open Matrix Finset krylov.Reference krylov.Methods krylov.Secant
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {p : ℕ}

/-- Actual model changes and full basis columns may be rescaled together without changing their canonical physical form.
Use: eliminate the genuine reference column energies in diagonal model replacements.
Article: main_krylov, apD:lem-model, invariance of V^(−T)Δ_H V^(−1).
Proof: reverse both actual product inverses and cancel the two nonsingular
diagonal column factors on their respective sides of the form. -/
theorem inverseCongruence_right_rescale (V H : Matrix (Fin p) (Fin p) ℝ)
    (s : Fin p → ℝ) (hs : IsUnit (diagonal s).det) :
    inverseCongruence (V*diagonal s) (rescaleModel H s)=inverseCongruence V H := by
  -- Only the real diagonal change is cancelled; the full form H need not be nonsingular.
  simp only [inverseCongruence,rescaleModel,transpose_mul,diagonal_transpose,Matrix.mul_inv_rev]
  calc
    _ = Vᵀ⁻¹*((diagonal s)⁻¹*diagonal s)*H*(diagonal s*(diagonal s)⁻¹)*V⁻¹ := by
      noncomm_ring
    _ = _ := by simp only [nonsing_inv_mul _ hs,mul_nonsing_inv _ hs,Matrix.mul_one]

/-- The actual normalized CG frame in the newest-first order of the true full reference model.
Use: the head is the terminal CG unit direction and older columns retain their actual reverse ages.
Article: main_krylov, apD:lem-model, Q in the actual native storage order. -/
def referenceUnitColumns {k : ℕ} (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (g : EuclideanSpace ℝ (Fin (k+1))) : Fin (k+1) → EuclideanSpace ℝ (Fin (k+1)) :=
  fun i => canonicalCGUnitStep base g (k-i.val)

/-- The real energy-scaled diagonal change of the actual full reference coefficient model.
Use: each entry is the given normalized diagonal change times its true physical reference-column energy.
Article: main_krylov, apD:lem-model, (Δ_H)_ii=q_i c_i. -/
def referenceDiagonalChange {k : ℕ} (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (g : EuclideanSpace ℝ (Fin (k+1))) (q : Fin (k+1) → ℝ) :
    Matrix (Fin (k+1)) (Fin (k+1)) ℝ :=
  diagonal fun i => q i*inner ℝ (referenceModelBasis base g k i)
    (cgOperator base (referenceModelBasis base g k i))

/-- An actual energy-scaled diagonal model change is exactly its diagonal operator in the genuine normalized CG frame.
Use: specialize the proved full modified canonical expansion to the source's informed old-entry changes, with every true reference energy cancelled.
Article: main_krylov, apD:lem-model, Δ̂=Q diag(q)Qᵀ.
Proof: actual CG orthonormality gives the orthogonal unit-column matrix.
The actual native reference columns equal these unit columns times their
proved stored scales and true CG step norms. Their true physical energies
are the squares of those same scales, so the exact diagonal inverse
congruence cancellation leaves precisely Q diag(q)Qᵀ. -/
theorem referenceDiagonalChange_canonical {k : ℕ}
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (k+1))) (hN : k+1≤referenceAtomCount base hb g)
    (q : Fin (k+1) → ℝ) :
    let V := metricRoot base*fullBasisMatrix (referenceModelBasis base g k)
    let Q := fullBasisMatrix (referenceUnitColumns base g)
    inverseCongruence V (referenceDiagonalChange base g q)=Q*diagonal q*Qᵀ := by
  -- The actual native head scale and every old step norm are retained until the final cancellation.
  let U := referenceModelBasis base g k
  let u := referenceUnitColumns base g
  let Q := fullBasisMatrix u
  let V := metricRoot base*fullBasisMatrix U
  let s := fun i : Fin (k+1) => referenceBasisScale base g k i*‖canonicalCGStep base g (k-i.val)‖
  have ho : Orthonormal ℝ u := by
    have hf := canonicalCGUnitStep_orthonormal base hb g (k+1)
      (fun i hi => cg_nonstagnation base hb g i (by omega))
    change Orthonormal ℝ (fun i : Fin (k+1) => canonicalCGUnitStep base g (k-i.val))
    simpa only [Function.comp_def,Fin.val_rev,Nat.add_sub_add_right] using
      hf.comp Fin.rev Fin.rev_injective
  have hcol (i : Fin (k+1)) : cgOperator (metricRoot base) (U i)=s i • u i := by
    calc
      _ = referenceBasisScale base g k i • canonicalCGStep base g (k-i.val) :=
        referenceModelBasis_canonical base hb g k hN i
      _ = s i • u i := by
        simpa only [s,u,referenceUnitColumns,canonicalCGUnitStep,smul_smul] using
          congrArg (fun v => referenceBasisScale base g k i • v)
            (NormedSpace.norm_smul_normalize (canonicalCGStep base g (k-i.val))).symm
  have hV : V=Q*diagonal s := by
    rw [show V=fullBasisMatrix (fun i => cgOperator (metricRoot base) (U i)) from
      (fullBasisMatrix_map U (metricRoot base)).symm]
    ext a i
    simpa only [Q,fullBasisMatrix,Matrix.of_apply,Matrix.mul_diagonal,PiLp.smul_apply,smul_eq_mul,
      mul_comm] using congrArg (fun v : EuclideanSpace ℝ (Fin (k+1)) => v a) (hcol i)
  have hQQ : Qᵀ*Q=1 := by
    have hc := fullBasisMatrix_compression u (1 : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    rw [Matrix.mul_one] at hc
    rw [← hc]
    ext i j
    simpa only [correctionCompression,crossGram,cgOperator,map_one,one_apply_eq_self,Matrix.one_apply]
      using (orthonormal_iff_ite.mp ho i j)
  have hQi : Q⁻¹=Qᵀ := Matrix.inv_eq_left_inv hQQ
  have hpre (i : ℕ) (hi : i≤k) : CG.gradient (cgOperator base) g i≠0 :=
    cg_nonstagnation base hb g i (by omega)
  have hU : LinearIndependent ℝ U := probedStepBasis_independent _
    (rfcMethod_consistent fullMemory (fun _ ha => ha) 1) _ (cgOperator_positive base hb).1
    (cgOperator_positive base hb).2 g k hpre
  have hvunit : IsUnit V.det := by
    change IsUnit (metricRoot base*fullBasisMatrix U).det
    rw [det_mul]
    exact (metricRoot_det_unit base hb).mul (fullBasisMatrix_unit U hU)
  have hs : IsUnit (diagonal s).det := by
    apply isUnit_iff_ne_zero.mpr
    intro hz
    have hd : V.det=0 := by rw [hV,det_mul,hz,mul_zero]
    exact isUnit_iff_ne_zero.mp hvunit hd
  have henergy (i : Fin (k+1)) : inner ℝ (U i) (cgOperator base (U i))=s i*s i := by
    have ha : cgOperator (metricRoot base) (cgOperator (metricRoot base) (U i))=cgOperator base (U i) := by
      simp only [cgOperator,← mul_apply_eq_comp,← map_mul,metricRoot_square base hb]
    rw [← ha,root_pairing,hcol,real_inner_smul_left,real_inner_smul_right]
    rw [real_inner_self_eq_norm_sq,ho.norm_eq_one i,one_pow,mul_one]
  have hD : referenceDiagonalChange base g q=rescaleModel (diagonal q) s := by
    change (diagonal fun i => q i*inner ℝ (U i) (cgOperator base (U i)))=rescaleModel (diagonal q) s
    simp only [rescaleModel,diagonal_mul_diagonal]
    congr 1
    funext i
    rw [henergy]
    ring
  change inverseCongruence V (referenceDiagonalChange base g q)=Q*diagonal q*Qᵀ
  rw [hV,hD,inverseCongruence_right_rescale Q (diagonal q) s hs]
  simp only [inverseCongruence,← transpose_nonsing_inv,hQi,transpose_transpose]

end
end krylov.Correction
