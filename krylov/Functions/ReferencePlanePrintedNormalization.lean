import krylov.Functions.ReferencePlaneOwnNormalization

/-!
Article: main_krylov, prop:Fcycle(iii), literal q₀² q_last normalization.
Use: compute the printed coefficient from the actual initial scalar gradient,
actual first secant, genuine true-minimizer Hessian and actual initial error.
Source: genuine CG homogeneity and exact two-metric energy normalization.
-/
namespace krylov.Functions
noncomputable section
open Matrix krylov.Reference krylov.Nonlinear krylov.Stability
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The actual positive-gradient scaling leaves every active energy ratio
unchanged. Article: main_krylov, prop:Fcycle(iii). -/
theorem referenceFibreRatio_positive_scalar (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) {ε : ℝ} (hε : 0<ε) (k : ℕ) :
    referenceFibreRatio A (ε • g) k=referenceFibreRatio A g k := by
  rw [referenceFibreRatio,Real.sqrt_div (by rw [cgEnergy_eq_norm_sq A hA]; positivity),
    cgEnergy_sqrt A hA,cgEnergy_sqrt A hA,canonicalCGStep_scalar A hA g ε hε.ne',
    canonicalCGStep_scalar A hA g ε hε.ne',norm_smul,norm_smul,
    Real.norm_of_nonneg hε.le,mul_div_mul_left _ _ hε.ne',
    referenceFibreRatio,Real.sqrt_div (by rw [cgEnergy_eq_norm_sq A hA]; positivity),
    cgEnergy_sqrt A hA,cgEnergy_sqrt A hA]

/-- The genuine full reference coefficient is exactly cubic in the original
initial-gradient scale. Article: main_krylov, prop:Fcycle(iii). -/
theorem referenceFibreCoefficient_positive_scalar (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) {ε : ℝ} (hε : 0<ε) (k : ℕ) :
    referenceFibreCoefficient A (ε • g) k=ε^3*referenceFibreCoefficient A g k := by
  simp only [referenceFibreCoefficient,referenceFibrePrefactor,
    referenceFibreRatio_positive_scalar A hA g hε]
  rw [cgEnergy_sqrt A hA,cgEnergy_sqrt A hA]
  simp only [cgEnergy_eq_norm_sq A hA,canonicalCGStep_scalar A hA g ε hε.ne',norm_smul,
    Real.norm_of_nonneg hε.le]
  ring

/-- The genuine sharp coefficient per true initial error cubed is invariant
under a common positive scaling of the actual initial gradient and error.
Article: main_krylov, prop:Fcycle(iii). -/
theorem referenceTwoMetricFibreCoefficient_positive_scalar
    (A H : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (hH : H.PosDef)
    (g u : EuclideanSpace ℝ (Fin n)) {ε : ℝ} (hε : 0<ε) (k : ℕ) :
    referenceTwoMetricFibreCoefficient A H (ε • g) (ε • u) k=
      referenceTwoMetricFibreCoefficient A H g u k := by
  rw [referenceTwoMetricFibreCoefficient,referenceFibreCoefficient_positive_scalar A hA g hε,
    referenceMetricSize_positive_scalar H hH u hε.le,mul_pow,referenceTwoMetricFibreCoefficient]
  exact mul_div_mul_left _ _ (pow_ne_zero 3 hε.ne')

/-- The own-reference coefficient is exactly the printed q₀² q_last factor
computed from the actual scalar gradient and the genuine true initial error.
Article: main_krylov, prop:Fcycle(iii), literal actual-source dictionary. -/
theorem referencePlaneOwnCoefficient_printed
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 2≤referenceAtomCount A hA g)
    {ε : ℝ} (hε : 0<ε) (t : krylov.Tensor.BinaryCubic) (z : EuclideanSpace ℝ (Fin n))
    (hB : (referencePlaneObservedMatrix A hA g ε t).PosDef)
    (hH : (referencePlaneTrueHessian A hA g ε t z).PosDef) :
    let B := referencePlaneObservedMatrix A hA g ε t
    let g₀ := gradient (referencePlaneCubicObjective A hA (ε • g) t) 0
    let ec := referencePlaneTrueInitialError A hA g ε t z
    let k := referenceAtomCount A hA g-1
    let r := referenceFibreRatio B g₀ k
    referencePlaneOwnCoefficient A hA g ε t z=
      (Real.sqrt (cgEnergy B g₀ 0)/ec)^2*(Real.sqrt (cgEnergy B g₀ k)/ec)*
        r*Real.sqrt (1+4*r^2)*krylov.Tensor.BinaryCubic.fibreMinimax r := by
  dsimp only
  rw [referencePlaneCubicObjective_initial_gradient A hA g hN hε]
  let v := (-ε⁻¹) • (metricCoordinates A hA).symm z
  have hs : ε • v=-(metricCoordinates A hA).symm z := by
    dsimp only [v]
    rw [smul_smul,mul_neg,mul_inv_cancel₀ hε.ne',neg_one_smul]
  have hh := referenceTwoMetricFibreCoefficient_positive_scalar
    (referencePlaneObservedMatrix A hA g ε t) (referencePlaneTrueHessian A hA g ε t z) hB hH g v hε
    (referenceAtomCount A hA g-1)
  rw [hs] at hh
  change _=referencePlaneOwnCoefficient A hA g ε t z at hh
  rw [←hh]
  exact referenceTwoMetricFibreCoefficient_printed _ _ hB (ε • g) _ _

end
end krylov.Functions
