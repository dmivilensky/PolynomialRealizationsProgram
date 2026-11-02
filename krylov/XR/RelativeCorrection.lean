import krylov.LinearAlgebra.SymmetricBall
import krylov.Nonlinear.MetricCoordinates
import krylov.Secant.RelativeMetric

/-!
Article: main_krylov, thm:metric, the actual model-metric correction.
Use: transport the already proved robust symmetric-ball minimax through
the genuine positive square root of the observed model. This gives the
physical Newton correction, zero correction, critical segment and exact
minimax value, including zero observed residuals and empty windows.
Source: the proved symmetric-ball residual theorem and mathlib positive
functional calculus; robust least squares is cited in the article to
Chandrasekaran et al. (1998) and El Ghaoui--Lebret (1997).
-/
namespace krylov.XR
noncomputable section
open Matrix krylov.Reference krylov.Nonlinear krylov.LinearAlgebra krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator MatrixOrder
variable {p : ℕ}

/-- The real physical correction objective in the observed positive-model
metric. Its two terms are the exact symmetric uncertainty maximum.
Article: main_krylov, thm:metric. -/
def relativeCorrectionObjective (T : Matrix (Fin p) (Fin p) ℝ) (hT : T.PosDef)
    (r : EuclideanSpace ℝ (Fin p)) (Ω : ℝ) (w : EuclideanSpace ℝ (Fin p)) : ℝ :=
  ‖(metricCoordinates T hT).symm r+metricCoordinates T hT w‖+
    Ω*‖metricCoordinates T hT w‖

/-- The full observed-model correction in true physical coordinates.
Article: main_krylov, thm:metric. -/
def relativeNewtonCorrection (T : Matrix (Fin p) (Fin p) ℝ) (hT : T.PosDef)
    (r : EuclideanSpace ℝ (Fin p)) : EuclideanSpace ℝ (Fin p) :=
  -(metricCoordinates T hT).symm ((metricCoordinates T hT).symm r)

/-- The actual positive-root Newton correction has precisely the negative
normalized residual as its canonical coordinate. Article: thm:metric. -/
theorem relativeNewtonCorrection_coordinate (T : Matrix (Fin p) (Fin p) ℝ) (hT : T.PosDef)
    (r : EuclideanSpace ℝ (Fin p)) :
    metricCoordinates T hT (relativeNewtonCorrection T hT r)=-(metricCoordinates T hT).symm r := by
  simp only [relativeNewtonCorrection,map_neg,ContinuousLinearEquiv.apply_symm_apply]

/-- The canonical construction is the literal physical inverse-model
correction, rather than an unspecified whitening choice. Article: thm:metric. -/
theorem relativeNewtonCorrection_eq_inverse (T : Matrix (Fin p) (Fin p) ℝ) (hT : T.PosDef)
    (r : EuclideanSpace ℝ (Fin p)) :
    relativeNewtonCorrection T hT r= -cgOperator T⁻¹ r := by
  change -(cgOperator (metricRoot T)⁻¹ (cgOperator (metricRoot T)⁻¹ r))= -cgOperator T⁻¹ r
  simp only [cgOperator,←mul_apply_eq_comp,←map_mul,←Matrix.mul_inv_rev,metricRoot_square T hT]

/-- The actual correction objective has the original exact attained
minimax value, in the genuine observed model norm. Article: thm:metric. -/
theorem relativeCorrection_isLeast (T : Matrix (Fin p) (Fin p) ℝ) (hT : T.PosDef)
    (r : EuclideanSpace ℝ (Fin p)) (Ω : ℝ) (hΩ : 0≤Ω) :
    IsLeast (Set.range (relativeCorrectionObjective T hT r Ω))
      (min 1 Ω*‖(metricCoordinates T hT).symm r‖) := by
  have he : Set.range (relativeCorrectionObjective T hT r Ω)=
      Set.range (fun b : EuclideanSpace ℝ (Fin p)=>‖(metricCoordinates T hT).symm r+b‖+Ω*‖b‖) := by
    ext v
    constructor
    · rintro ⟨w,rfl⟩
      exact ⟨metricCoordinates T hT w,rfl⟩
    · rintro ⟨b,rfl⟩
      refine ⟨(metricCoordinates T hT).symm b,?_⟩
      simp only [relativeCorrectionObjective,ContinuousLinearEquiv.apply_symm_apply]
  rw [he]
  exact robust_identity_isLeast _ hΩ

/-- Below uncertainty one the full physical inverse-model correction is
the unique minimizer, including the zero-residual case. Article: thm:metric. -/
theorem relativeCorrection_small_iff (T : Matrix (Fin p) (Fin p) ℝ) (hT : T.PosDef)
    (r w : EuclideanSpace ℝ (Fin p)) (Ω : ℝ) (hΩ : 0≤Ω) (hΩ₁ : Ω<1) :
    relativeCorrectionObjective T hT r Ω w=Ω*‖(metricCoordinates T hT).symm r‖ ↔
      w=relativeNewtonCorrection T hT r := by
  rw [relativeCorrectionObjective,robust_identity_small_iff _ _ hΩ hΩ₁,
    ←relativeNewtonCorrection_coordinate T hT r]
  exact (metricCoordinates T hT).injective.eq_iff

/-- Above uncertainty one the unique robust correction is zero.
Article: main_krylov, thm:metric. -/
theorem relativeCorrection_large_iff (T : Matrix (Fin p) (Fin p) ℝ) (hT : T.PosDef)
    (r w : EuclideanSpace ℝ (Fin p)) (Ω : ℝ) (hΩ : 1<Ω) :
    relativeCorrectionObjective T hT r Ω w=‖(metricCoordinates T hT).symm r‖ ↔ w=0 := by
  rw [relativeCorrectionObjective,robust_identity_large_iff _ _ hΩ]
  exact (metricCoordinates T hT).map_eq_zero_iff

/-- At the critical radius the entire segment between full correction
and zero is the exact minimizer set. Article: main_krylov, thm:metric. -/
theorem relativeCorrection_critical_iff (T : Matrix (Fin p) (Fin p) ℝ) (hT : T.PosDef)
    (r w : EuclideanSpace ℝ (Fin p)) :
    relativeCorrectionObjective T hT r 1 w=‖(metricCoordinates T hT).symm r‖ ↔
      metricCoordinates T hT w∈segment ℝ (-(metricCoordinates T hT).symm r) 0 := by
  simp only [relativeCorrectionObjective,one_mul,robust_identity_critical_iff]

/-- The actual normalized symmetric model-error ball is exactly the
printed pair of physical Loewner uncertainty inequalities.
Article: main_krylov, thm:metric, final displayed interval. -/
theorem relativeCorrection_uncertainty (T B : Matrix (Fin p) (Fin p) ℝ)
    (hT : T.PosDef) (hB : B.IsSymm) (Ω : ℝ) (hΩ : 0≤Ω) :
    relativeBudget T (B-T)≤Ω ↔ (1-Ω) • T≤B ∧ B≤(1+Ω) • T := by
  rw [relative_norm_le_iff T (B-T) hT (hB.sub hT.isHermitian.isSymm) hΩ]
  constructor
  · rintro ⟨hl,hu⟩
    constructor
    · have hh := add_le_add_right hl T
      convert hh using 1 <;> module
    · have hh := add_le_add_right hu T
      convert hh using 1 <;> module
  · rintro ⟨hl,hu⟩
    constructor
    · have hh := sub_le_sub_right hl T
      convert hh using 1
      module
    · have hh := sub_le_sub_right hu T
      convert hh using 1
      module

end
end krylov.XR
