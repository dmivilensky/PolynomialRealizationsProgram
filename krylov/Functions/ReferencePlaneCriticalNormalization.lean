import krylov.Functions.ReferencePlaneHessian
import krylov.Functions.ReferencePlaneCoefficient

/-!
Article: main_krylov, prop:Fcycle(iii), true initial-error normalization.
Use: translate the proved actual planar critical-point localization into the
literal full original source and its true physical displacement. Source:
orthogonal embedding, genuine positive-root coordinates and exact scaling.
-/
namespace krylov.Functions
noncomputable section
open Matrix krylov.Reference krylov.Nonlinear krylov.Tensor.BinaryCubic
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The limiting normalized initial error of the literal original source.
Article: main_krylov, prop:Fcycle(iii). -/
def referencePlaneInitialError (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  -(metricCoordinates A hA).symm (referencePlaneNode A g (referenceAtomCount A hA g))

/-- The limiting displacement is exactly the physical quadratic initial
error, rather than a supplied source normalization. Article: prop:Fcycle(iii). -/
theorem referencePlaneInitialError_eq (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) :
    referencePlaneInitialError A hA g=(metricCoordinates A hA).symm (cgCanonicalError A g 0) := by
  rw [referencePlaneInitialError,referencePlaneNode_terminal,map_neg,neg_neg]

/-- Every genuine nonzero reference has a nonzero limiting physical error.
Article: main_krylov, prop:Fcycle(iii). -/
theorem referencePlaneInitialError_ne_zero (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hg : g≠0) : referencePlaneInitialError A hA g≠0 := by
  rw [referencePlaneInitialError_eq]
  simpa only [map_zero] using
    (metricCoordinates A hA).symm.injective.ne (cgCanonicalError_initial_ne_zero A hA g hg)

/-- The genuine full critical point is within the proved quadratic error of
the actual full CG terminal node. Article: main_krylov, prop:Fcycle(iii). -/
theorem referencePlane_full_critical_localization
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 2≤referenceAtomCount A hA g)
    {ε M : ℝ} (_hε : 0<ε) (z : Plane)
    (hz : ‖z-planeOfPair (ε*‖canonicalCGStep A g 0‖,referencePlaneRatio A hA g*(ε*‖canonicalCGStep A g 0‖))‖≤
      M*(ε*‖canonicalCGStep A g 0‖)^2) :
    ‖hilbertPlaneEmbed (referencePlaneFirst A g) (referencePlaneLast A hA g) z+
      ε • referencePlaneComplement A hA g-ε • referencePlaneNode A g (referenceAtomCount A hA g)‖≤
      M*‖canonicalCGStep A g 0‖^2*ε^2 := by
  obtain ⟨_,_,he,hh,heh,_,_⟩ := referencePlane_sample_lines A hA g hN
  let e := referencePlaneFirst A g
  let h := referencePlaneLast A hA g
  let p := ‖canonicalCGStep A g 0‖
  let r := referencePlaneRatio A hA g
  have hpair : planeOfPair (ε*p,r*(ε*p))=ε • planeOfPair (p,r*p) := by
    rw [←planeOfPair_smul]
    congr 1
    apply Prod.ext <;> simp only [Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
    all_goals ring
  have hv : hilbertPlaneEmbed e h z+ε • referencePlaneComplement A hA g-
      ε • referencePlaneNode A g (referenceAtomCount A hA g)=
      hilbertPlaneEmbed e h (z-planeOfPair (ε*p,r*(ε*p))) := by
    rw [hpair,map_sub,map_smul]
    dsimp only [referencePlaneComplement,e,h,p,r]
    rw [smul_sub]
    abel
  rw [hv,hilbertPlaneEmbed_norm e h he hh heh]
  exact hz.trans_eq (by ring)

/-- True full minimizer localization gives a first-order bound on the
normalized physical initial error for the actual original ε g source.
Article: main_krylov, prop:Fcycle(iii). -/
theorem referencePlane_normalized_initial_error
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 2≤referenceAtomCount A hA g)
    {ε M : ℝ} (hε : 0<ε) (z : Plane)
    (hz : ‖z-planeOfPair (ε*‖canonicalCGStep A g 0‖,referencePlaneRatio A hA g*(ε*‖canonicalCGStep A g 0‖))‖≤
      M*(ε*‖canonicalCGStep A g 0‖)^2) :
    ‖(-ε⁻¹) • (metricCoordinates A hA).symm
        (hilbertPlaneEmbed (referencePlaneFirst A g) (referencePlaneLast A hA g) z+
          ε • referencePlaneComplement A hA g)-referencePlaneInitialError A hA g‖≤
      ‖(metricCoordinates A hA).symm.toContinuousLinearMap‖*M*‖canonicalCGStep A g 0‖^2*ε := by
  let S := metricCoordinates A hA
  let zf := hilbertPlaneEmbed (referencePlaneFirst A g) (referencePlaneLast A hA g) z+
    ε • referencePlaneComplement A hA g
  let v := referencePlaneNode A g (referenceAtomCount A hA g)
  have he : (-ε⁻¹) • S.symm zf-referencePlaneInitialError A hA g=
      (-ε⁻¹) • S.symm (zf-ε • v) := by
    rw [map_sub,map_smul,smul_sub,smul_smul,neg_mul,inv_mul_cancel₀ hε.ne',neg_one_smul]
    change (-ε⁻¹) • S.symm zf-(-S.symm v)=(-ε⁻¹) • S.symm zf-(-S.symm v)
    rfl
  rw [he,norm_smul,Real.norm_eq_abs,abs_neg,abs_inv,abs_of_pos hε]
  have hb := referencePlane_full_critical_localization A hA g hN hε z hz
  calc
    _ ≤ ε⁻¹*(‖S.symm.toContinuousLinearMap‖*‖zf-ε • v‖) :=
      mul_le_mul_of_nonneg_left (S.symm.toContinuousLinearMap.le_opNorm _) (inv_nonneg.mpr hε.le)
    _ ≤ ε⁻¹*(‖S.symm.toContinuousLinearMap‖*(M*‖canonicalCGStep A g 0‖^2*ε^2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb (norm_nonneg _)) (inv_nonneg.mpr hε.le)
    _ = _ := by dsimp only [S]; field_simp

end
end krylov.Functions
