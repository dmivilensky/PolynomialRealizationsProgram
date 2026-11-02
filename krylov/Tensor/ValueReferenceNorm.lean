import krylov.Tensor.ValueReferenceDictionary

/-!
Article: main_krylov, prop:Fcycle(i), the genuine corrected response bound.
Use: pass the actually computed canonical corrected staircase to its true
orthonormal CG coordinates, and apply the source's proved sharp dimension
factor. Source: genuine full reference activity, the exact model/fresh
coordinate dictionary and the true coordinate linear isometry.
-/
namespace krylov.Tensor
noncomputable section
open Matrix Finset krylov.Functions krylov.Reference krylov.Correction krylov.Secant krylov.Variation krylov.Envelope
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The genuine full-active canonical CG frame as its actual orthonormal coordinate basis.
Article: main_krylov, prop:Fcycle(i), true Q coordinate isometry. -/
def valueReferenceBasis (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 0<referenceAtomCount A hA g)
    (hcount : referenceAtomCount A hA g=n) :
    OrthonormalBasis (Fin (referenceAtomCount A hA g)) ℝ (EuclideanSpace ℝ (Fin n)) := by
  letI : Nonempty (Fin (referenceAtomCount A hA g)) := ⟨⟨0,hN⟩⟩
  let B := basisOfOrthonormalOfCardEqFinrank (canonicalCG_frame A hA g)
    (by simpa only [Fintype.card_fin,finrank_euclideanSpace] using hcount)
  exact B.toOrthonormalBasis (by
    simpa only [B,coe_basisOfOrthonormalOfCardEqFinrank] using canonicalCG_frame A hA g)

/-- The true coordinate basis contains precisely the computed canonical unit CG steps.
Article: main_krylov, prop:Fcycle(i), genuine basis dictionary. -/
theorem valueReferenceBasis_apply (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 0<referenceAtomCount A hA g)
    (hcount : referenceAtomCount A hA g=n) (i : Fin (referenceAtomCount A hA g)) :
    valueReferenceBasis A hA g hN hcount i=canonicalCGUnitStep A g i.val := by
  simp only [valueReferenceBasis,Module.Basis.coe_toOrthonormalBasis,coe_basisOfOrthonormalOfCardEqFinrank]

/-- The true corrected staircase/fresh product has exactly the printed source Lambda_F coordinates.
Article: main_krylov, prop:Fcycle(i), complete genuine coefficient dictionary. -/
theorem valueReferenceCoefficient_coordinates
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 0<referenceAtomCount A hA g)
    (hcount : referenceAtomCount A hA g=n)
    (T : SymmetricCubic (EuclideanSpace ℝ (Fin n))) :
    (valueReferenceBasis A hA g hN hcount).repr
      ((tensorReferenceStaircase A hA g T-tensorReferenceDiagonal A hA g T)
        (freshDefect A g (fun l=>cubicSliceMatrix T (referenceMidpointDrift A g l))
          (referenceAtomCount A hA g)))=valueReferenceCoefficient A hA g T := by
  let b := valueReferenceBasis A hA g hN hcount
  let S := tensorReferenceStaircase A hA g T-tensorReferenceDiagonal A hA g T
  let f := freshDefect A g (fun l=>cubicSliceMatrix T (referenceMidpointDrift A g l)) (referenceAtomCount A hA g)
  have hf j : b.repr f j=referenceTensorFresh A hA g T j := by
    rw [b.repr_apply_apply,valueReferenceBasis_apply]
    exact tensorReferenceFresh_unit_pair A hA g hN T j
  have hM i j : inner ℝ (b i) (S (b j))=valueReferenceModel A hA g T i j := by
    rw [valueReferenceBasis_apply,valueReferenceBasis_apply]
    exact tensorReferenceCorrected_unit_pair A hA g T i j
  ext i
  change b.repr (S f) i=cgOperator (valueReferenceModel A hA g T) (referenceTensorFresh A hA g T) i
  calc
    _ = inner ℝ (b i) (S f) := b.repr_apply_apply _ _
    _ = inner ℝ (b i) (S (∑ j,b.repr f j • b j)) := by rw [b.sum_repr]
    _ = ∑ j,b.repr f j*inner ℝ (b i) (S (b j)) := by
      simp only [map_sum,inner_sum,map_smul,real_inner_smul_right]
    _ = ∑ j,valueReferenceModel A hA g T i j*referenceTensorFresh A hA g T j := by
      apply sum_congr rfl
      intro j _
      rw [hf,hM,mul_comm]
    _ = _ := rfl

/-- The actual physical canonical product and its true Lambda_F coordinate vector have exactly the same norm.
Article: main_krylov, prop:Fcycle(i), genuine orthonormal invariance. -/
theorem valueReferenceCoefficient_norm_eq
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 0<referenceAtomCount A hA g)
    (hcount : referenceAtomCount A hA g=n)
    (T : SymmetricCubic (EuclideanSpace ℝ (Fin n))) :
    ‖(tensorReferenceStaircase A hA g T-tensorReferenceDiagonal A hA g T)
      (freshDefect A g (fun l=>cubicSliceMatrix T (referenceMidpointDrift A g l))
        (referenceAtomCount A hA g))‖=‖valueReferenceCoefficient A hA g T‖ := by
  have hh := congrArg norm (valueReferenceCoefficient_coordinates A hA g hN hcount T)
  simpa only [LinearIsometryEquiv.norm_map] using hh

/-- The genuine corrected staircase/fresh response has the source's exact 4 n^(3/2) two-error upper bound.
Article: main_krylov, prop:Fcycle(i), no abstract response field is assumed.
Both the actual independent reference gradient and its genuine initial and
first post-search energy errors appear in this literal computed coefficient. -/
theorem tensorReferenceCorrected_response_bound
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 0<referenceAtomCount A hA g)
    (hcount : referenceAtomCount A hA g=n)
    (T : SymmetricCubic (EuclideanSpace ℝ (Fin n)))
    (hT : ∀ x,‖x‖=1 → |T.form x x x|≤2) :
    ‖(tensorReferenceStaircase A hA g T-tensorReferenceDiagonal A hA g T)
      (freshDefect A g (fun l=>cubicSliceMatrix T (referenceMidpointDrift A g l))
        (referenceAtomCount A hA g))‖≤
      4*referenceAtomCount A hA g*Real.sqrt (referenceAtomCount A hA g)*
        ‖cgCanonicalError A g 0‖*‖cgCanonicalError A g 1‖ := by
  rw [valueReferenceCoefficient_norm_eq A hA g hN hcount T]
  exact valueReferenceCoefficient_bound A hA g hN T hT

end
end krylov.Tensor
