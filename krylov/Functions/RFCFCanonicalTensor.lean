import krylov.Functions.RFCFCanonicalQuadratic
import krylov.Functions.GenuineThirdTensor

/-!
Article: main_krylov, prop:Fcycle(i), actual third tensors in the canonical metric.
Use: construct the true inverse-root pullback of the original scalar third
form and identify the observed canonical value diagonal with its literal
half-step tensor contraction. Source: continuous multilinear composition,
genuine scalar Schwarz symmetry and true reference step normalization.
-/
namespace krylov.Functions
noncomputable section
open Matrix Finset krylov.Methods krylov.Reference krylov.Correction krylov.Secant krylov.Nonlinear
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {k : ℕ}

/-- Pull back every slot of a genuine symmetric cubic by one actual linear coordinate map.
Article: main_krylov, prop:Fcycle(i), tensor transport to the minimizer metric. -/
def SymmetricCubic.pullback (T : SymmetricCubic E) (S : E →L[ℝ] E) : SymmetricCubic E where
  form :=
    let P := (ContinuousLinearMap.compL ℝ E E ℝ).flip S
    let Q := (ContinuousLinearMap.compL ℝ E E (E →L[ℝ] ℝ)).flip S
    (Q.comp ((P.postcomp E).comp T.form)).comp S
  swap₁ := fun a b c=>T.swap₁ (S a) (S b) (S c)
  swap₂ := fun a b c=>T.swap₂ (S a) (S b) (S c)

/-- The actual pullback form evaluates at precisely the three true transported vectors.
Article: main_krylov, prop:Fcycle(i), exact original tensor coordinate dictionary. -/
theorem SymmetricCubic.pullback_apply (T : SymmetricCubic E) (S : E →L[ℝ] E) (a b c : E) :
    (T.pullback S).form a b c=T.form (S a) (S b) (S c) := rfl

/-- A genuine scalar third derivative, expressed in the true minimizer metric.
Article: main_krylov, prop:Fcycle(i), the actual canonical T tensor. -/
def metricThirdCubic
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (T : EuclideanSpace ℝ (Fin (k+1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (f : EuclideanSpace ℝ (Fin (k+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)))
    (H : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (D : EuclideanSpace ℝ (Fin (k+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (hD : HasFDerivAt H D 0) {r : ℝ} (hr : 0<r)
    (hF : ∀ z, ‖T z‖≤r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z, ‖T z‖≤r → HasFDerivAt G (H z) z) : SymmetricCubic (EuclideanSpace ℝ (Fin (k+1))) :=
  (genuineThirdCubic T f G H D hD hr hF hG).pullback
    (metricCoordinates base hb).symm.toContinuousLinearMap

/-- The genuine canonical tensor contracts at root-images exactly as the original physical Hessian derivative.
Article: main_krylov, prop:Fcycle(i), actual scalar tensor compatibility. -/
theorem metricThirdCubic_pair
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (T : EuclideanSpace ℝ (Fin (k+1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (f : EuclideanSpace ℝ (Fin (k+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)))
    (H : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (D : EuclideanSpace ℝ (Fin (k+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (hD : HasFDerivAt H D 0) {r : ℝ} (hr : 0<r)
    (hF : ∀ z, ‖T z‖≤r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z, ‖T z‖≤r → HasFDerivAt G (H z) z)
    (a b c : EuclideanSpace ℝ (Fin (k+1))) :
    (metricThirdCubic base hb T f G H D hD hr hF hG).form
      (cgOperator (metricRoot base) a) (cgOperator (metricRoot base) b)
      (cgOperator (metricRoot base) c)=inner ℝ (D a b) c := by
  change (genuineThirdCubic T f G H D hD hr hF hG).form
    ((metricCoordinates base hb).symm ((metricCoordinates base hb) a))
    ((metricCoordinates base hb).symm ((metricCoordinates base hb) b))
    ((metricCoordinates base hb).symm ((metricCoordinates base hb) c))=_
  rw [ContinuousLinearEquiv.symm_apply_apply,ContinuousLinearEquiv.symm_apply_apply,
    ContinuousLinearEquiv.symm_apply_apply,genuineThirdCubic_apply,real_inner_comm]

/-- Every actual raw-model diagonal coefficient is the literal canonical tensor half-step contraction T[σ/2,h,h].
Article: main_krylov, prop:Fcycle(i), the source's precise diagonal replacement. -/
theorem rfcFReferenceDiagonalCoefficient_eq_tensor
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (D : EuclideanSpace ℝ (Fin (k+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (T : SymmetricCubic (EuclideanSpace ℝ (Fin (k+1))))
    (hT : ∀ a b c,T.form (cgOperator (metricRoot base) a) (cgOperator (metricRoot base) b)
      (cgOperator (metricRoot base) c)=inner ℝ (D a b) c)
    (g : EuclideanSpace ℝ (Fin (k+1)))
    (hN : k+1≤referenceAtomCount base hb g) (i : Fin (k+1)) :
    rfcFReferenceDiagonalCoefficient base D g i=
      T.form ((1/2 : ℝ) • canonicalCGStep base g i.val)
        (canonicalCGUnitStep base g i.val) (canonicalCGUnitStep base g i.val) := by
  have hn : ‖canonicalCGStep base g i.val‖≠0 := norm_ne_zero_iff.mpr
    (canonicalCGStep_ne_zero base hb g i.val (fun a ha=>cg_nonstagnation base hb g a (by omega)))
  have ht := hT (referenceStep (cgOperator base) g i.val)
    (referenceStep (cgOperator base) g i.val) (referenceStep (cgOperator base) g i.val)
  change T.form (canonicalCGStep base g i.val) (canonicalCGStep base g i.val)
    (canonicalCGStep base g i.val)=_ at ht
  have hs : canonicalCGStep base g i.val=‖canonicalCGStep base g i.val‖ • canonicalCGUnitStep base g i.val :=
    (NormedSpace.norm_smul_normalize _).symm
  rw [hs] at ht
  simp only [map_smul,_root_.smul_apply,smul_eq_mul] at ht
  have ht₁ : T.form (canonicalCGStep base g i.val) (canonicalCGUnitStep base g i.val)
      (canonicalCGUnitStep base g i.val)=‖canonicalCGStep base g i.val‖*
        T.form (canonicalCGUnitStep base g i.val) (canonicalCGUnitStep base g i.val)
          (canonicalCGUnitStep base g i.val) := by
    conv_lhs => rw [hs]
    simp only [map_smul,_root_.smul_apply,smul_eq_mul]
  simp only [map_smul,_root_.smul_apply,smul_eq_mul,ht₁]
  dsimp only [rfcFReferenceDiagonalCoefficient]
  rw [←ht]
  field_simp

end
end krylov.Functions
