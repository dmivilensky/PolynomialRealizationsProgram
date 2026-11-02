import krylov.Functions.ReferencePlaneScaling
import krylov.Functions.ReferenceTwoMetricNormalization

/-!
Article: main_krylov, prop:Fcycle(iii), printed sharp normalization.
Use: identify the actual first/last CG geometric ratio and the exact
q₀² q_last coefficient, retaining the true error metric independently.
Source: genuine CG energy identities and positive real square roots.
-/
namespace krylov.Functions
noncomputable section
open Matrix krylov.Reference krylov.Nonlinear
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The full actual geometric first/last ratio is the printed energy ratio.
Article: main_krylov, prop:Fcycle(iii). -/
theorem referencePlaneRatio_eq_fibreRatio (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) :
    referencePlaneRatio A hA g=referenceFibreRatio A g (referenceAtomCount A hA g-1) := by
  rw [referenceFibreRatio,Real.sqrt_div (by rw [cgEnergy_eq_norm_sq A hA]; positivity),
    cgEnergy_sqrt A hA,cgEnergy_sqrt A hA]
  rfl

/-- The exact coefficient of the full original source is its genuine sharp
reference coefficient. Article: main_krylov, prop:Fcycle(iii). -/
theorem referencePlane_coefficient (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 2≤referenceAtomCount A hA g) :
    (referencePlaneRatio A hA g)^2*Real.sqrt (1+4*(referencePlaneRatio A hA g)^2)*
      krylov.Tensor.BinaryCubic.fibreMinimax (referencePlaneRatio A hA g)*‖canonicalCGStep A g 0‖^3=
      referenceFibreCoefficient A g (referenceAtomCount A hA g-1) := by
  obtain ⟨hp,_,_,_,_,_,_⟩ := referencePlane_sample_lines A hA g hN
  change 0<‖canonicalCGStep A g 0‖ at hp
  rw [referenceFibreCoefficient,referenceFibrePrefactor,←referencePlaneRatio_eq_fibreRatio A hA,
    cgEnergy_eq_norm_sq A hA,cgEnergy_sqrt A hA]
  dsimp only [referencePlaneRatio]
  field_simp

/-- The printed q₀² q_last sharp coefficient uses the actual error metric,
while its reference energies and ratio use the independently observed matrix.
Article: main_krylov, prop:Fcycle(iii), exact two-metric dictionary. -/
theorem referenceTwoMetricFibreCoefficient_printed
    (A H : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g u : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    referenceTwoMetricFibreCoefficient A H g u k=
      (Real.sqrt (cgEnergy A g 0)/referenceMetricSize H u)^2*
      (Real.sqrt (cgEnergy A g k)/referenceMetricSize H u)*
      referenceFibreRatio A g k*Real.sqrt (1+4*(referenceFibreRatio A g k)^2)*
      krylov.Tensor.BinaryCubic.fibreMinimax (referenceFibreRatio A g k) := by
  have hc : 0≤cgEnergy A g 0 := by rw [cgEnergy_eq_norm_sq A hA]; positivity
  rw [referenceTwoMetricFibreCoefficient,referenceFibreCoefficient,referenceFibrePrefactor,div_pow,
    Real.sq_sqrt hc]
  ring

/-- Positive scaling of a true metric error is exact, including the genuine
positive-root norm. Article: main_krylov, prop:Fcycle(iii). -/
theorem referenceMetricSize_positive_scalar (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (u : EuclideanSpace ℝ (Fin n)) {ε : ℝ} (hε : 0≤ε) :
    referenceMetricSize A (ε • u)=ε*referenceMetricSize A u := by
  rw [referenceMetricSize_eq_norm A hA,map_smul,norm_smul,Real.norm_of_nonneg hε,
    referenceMetricSize_eq_norm A hA]

end
end krylov.Functions
