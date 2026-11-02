import krylov.Functions.ReferencePlaneSource
import krylov.Correction.ResponseHomogeneity

/-!
Article: main_krylov, prop:Fcycle(iii), exact actual source scaling.
Use: write the original full reference-plane scalar family at initial gradient
ε g in its fixed genuine first/last CG frame, with actual step scale ε p and
actual orthogonal centre ε m. Source: true CG homogeneity and exact finite sums.
-/
namespace krylov.Functions
noncomputable section
open Matrix Finset krylov.Reference krylov.Correction krylov.Stability krylov.Nonlinear
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- Positive original-gradient scaling preserves the true first reference unit step.
Article: main_krylov, prop:Fcycle(iii). -/
theorem referencePlaneFirst_positive_scalar (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) {ε : ℝ} (hε : 0<ε) :
    referencePlaneFirst A (ε • g)=referencePlaneFirst A g :=
  canonicalCGUnitStep_positive_scalar A hA g hε 0

/-- Positive original-gradient scaling preserves the true final active reference unit step.
Article: main_krylov, prop:Fcycle(iii). -/
theorem referencePlaneLast_positive_scalar (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) {ε : ℝ} (hε : 0<ε) :
    referencePlaneLast A hA (ε • g)=referencePlaneLast A hA g := by
  rw [referencePlaneLast,referenceAtomCount_scalar A hA g ε hε.ne',
    canonicalCGUnitStep_positive_scalar A hA g hε]
  rfl

/-- The actual first/last reference ratio is unchanged by positive initial-gradient scaling.
Article: main_krylov, prop:Fcycle(iii). -/
theorem referencePlaneRatio_positive_scalar (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) {ε : ℝ} (hε : 0<ε) :
    referencePlaneRatio A hA (ε • g)=referencePlaneRatio A hA g := by
  simp only [referencePlaneRatio,referenceAtomCount_scalar A hA g ε hε.ne',
    canonicalCGStep_scalar A hA g ε hε.ne',norm_smul,Real.norm_of_nonneg hε.le]
  rw [mul_div_mul_left _ _ hε.ne']

/-- Every actual canonical reference node scales by exactly the original initial-gradient factor.
Article: main_krylov, prop:Fcycle(iii). -/
theorem referencePlaneNode_positive_scalar (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) {ε : ℝ} (hε : 0<ε) (i : ℕ) :
    referencePlaneNode A (ε • g) i=ε • referencePlaneNode A g i := by
  simp only [referencePlaneNode,canonicalCGStep_scalar A hA g ε hε.ne',Finset.smul_sum]

/-- The actual common orthogonal quadratic centre scales by precisely the original initial-gradient factor.
Article: main_krylov, prop:Fcycle(iii). -/
theorem referencePlaneComplement_positive_scalar (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) {ε : ℝ} (hε : 0<ε) :
    referencePlaneComplement A hA (ε • g)=ε • referencePlaneComplement A hA g := by
  rw [referencePlaneComplement,referenceAtomCount_scalar A hA g ε hε.ne',referencePlaneNode_positive_scalar A hA g hε,
    referencePlaneFirst_positive_scalar A hA g hε,referencePlaneLast_positive_scalar A hA g hε,
    referencePlaneRatio_positive_scalar A hA g hε,canonicalCGStep_scalar A hA g ε hε.ne',norm_smul,
    Real.norm_of_nonneg hε.le]
  have hp : planeOfPair (ε*‖canonicalCGStep A g 0‖,referencePlaneRatio A hA g*(ε*‖canonicalCGStep A g 0‖))=
      ε • planeOfPair (‖canonicalCGStep A g 0‖,referencePlaneRatio A hA g*‖canonicalCGStep A g 0‖) := by
    rw [←planeOfPair_smul]
    congr 1
    apply Prod.ext <;> simp only [Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
    all_goals ring
  rw [hp,map_smul,←smul_sub]
  rfl

/-- The literal original scalar cubic at ε g has fixed actual reference directions and precisely scaled real parameters.
Article: main_krylov, prop:Fcycle(iii), original family scaling dictionary. -/
theorem referencePlaneCubicObjective_positive_scalar
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) {ε : ℝ} (hε : 0<ε) (t : krylov.Tensor.BinaryCubic) :
    referencePlaneCubicObjective A hA (ε • g) t=
      metricHilbertPlaneObjective (metricCoordinates A hA) (referencePlaneFirst A g) (referencePlaneLast A hA g)
        (ε • referencePlaneComplement A hA g) (ε*‖canonicalCGStep A g 0‖) (referencePlaneRatio A hA g) t := by
  rw [referencePlaneCubicObjective,referencePlaneFirst_positive_scalar A hA g hε,
    referencePlaneLast_positive_scalar A hA g hε,referencePlaneComplement_positive_scalar A hA g hε,
    referencePlaneRatio_positive_scalar A hA g hε,canonicalCGStep_scalar A hA g ε hε.ne',norm_smul,
    Real.norm_of_nonneg hε.le]

/-- The actual initial gradient of the literal full scalar source is precisely its original ε-scaled reference gradient.
Article: main_krylov, prop:Fcycle(iii), true normalized initial observation. -/
theorem referencePlaneCubicObjective_initial_gradient
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 2≤referenceAtomCount A hA g)
    {ε : ℝ} (hε : 0<ε) (t : krylov.Tensor.BinaryCubic) :
    gradient (referencePlaneCubicObjective A hA (ε • g) t) 0=ε • g := by
  have hcount : 2≤referenceAtomCount A hA (ε • g) := by rw [referenceAtomCount_scalar A hA g ε hε.ne']; exact hN
  simpa only [CG.displacement,range_zero,sum_empty,CG.gradient,krylov.Reference.cgRun] using
    referencePlaneCubicGradient_prefix A hA (ε • g) hcount t 0 (by omega)

end
end krylov.Functions
