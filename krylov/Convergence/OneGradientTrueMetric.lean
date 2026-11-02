import krylov.Convergence.OneGradientSourceDomain
import krylov.Convergence.OneGradientMetricNormalization
import krylov.LinearAlgebra.SpectralLowerForms
import krylov.Correction.GatedAccepted

/-!
Article: main_krylov, thm:LB, literal true cubic Hessian and spectrum.
Use: form the actual Hessian at each constructed local minimizer, derive
its positivity and physical matrix drift, and transfer the original
spectral interval without assuming a true-source spectral certificate.
Source: true scalar cubic differentiation, real matrix/operator isometry
and spectral Rayleigh/norm perturbation estimates from the common library.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set krylov.Reference krylov.Functions krylov.Secant krylov.LinearAlgebra krylov.Correction
open scoped InnerProductSpace MatrixOrder Matrix.Norms.L2Operator
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The literal actual source Hessian matrix, at any real source point.
Article: main_krylov, thm:LB, H_star. -/
def oneGradientCubicTrueHessian (A : Matrix (Fin n) (Fin n) ℝ) (a : E) (b t : ℝ) (x : E) :
    Matrix (Fin n) (Fin n) ℝ :=
  physicalOperatorMatrix (oneGradientCubicHessian (cgOperator A+b • InnerProductSpace.rankOne ℝ a a) a t x)

/-- This real matrix is exactly the actual scalar source Hessian operator.
Article: main_krylov, thm:LB. -/
theorem oneGradientCubicTrueHessian_operator
    (A : Matrix (Fin n) (Fin n) ℝ) (a : E) (b t : ℝ) (x : E) :
    cgOperator (oneGradientCubicTrueHessian A a b t x)=
      oneGradientCubicHessian (cgOperator A+b • InnerProductSpace.rankOne ℝ a a) a t x :=
  physicalOperatorMatrix_operator _

/-- Genuine positive curvature at the actual critical point proves true
Hessian positivity, rather than presuming it as source data. Article: thm:LB. -/
theorem oneGradientCubicTrueHessian_posDef
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (a : E) (b t : ℝ) (x : E) (m : ℝ)
    (hm : 0<m) (hform : ∀ v,m*‖v‖^2≤ inner ℝ v
      (oneGradientCubicHessian (cgOperator A+b • InnerProductSpace.rankOne ℝ a a) a t x v)) :
    (oneGradientCubicTrueHessian A a b t x).PosDef := by
  have he : oneGradientCubicHessian (cgOperator A+b • InnerProductSpace.rankOne ℝ a a) a t x=
      cgOperator A+(b+t*inner ℝ a x) • InnerProductSpace.rankOne ℝ a a := by
    unfold oneGradientCubicHessian
    module
  apply physicalOperatorMatrix_posDef _
  · rw [he]
    exact oneGradientCubicFibre_symmetric A hA a _
  · intro v hv
    exact (mul_pos hm (sq_pos_of_pos (norm_pos_iff.mpr hv))).trans_le (hform v)

/-- True physical Hessian drift is exactly its spectral matrix drift.
Article: main_krylov, thm:LB, source metric replacement. -/
theorem oneGradientCubicTrueHessian_drift
    (A : Matrix (Fin n) (Fin n) ℝ) (a : E) (b t : ℝ) (x : E) :
    ‖oneGradientCubicTrueHessian A a b t x-A‖=
      ‖oneGradientCubicHessian (cgOperator A+b • InnerProductSpace.rankOne ℝ a a) a t x-cgOperator A‖ := by
  rw [←Matrix.l2_opNorm_toEuclideanCLM]
  change ‖cgOperator (oneGradientCubicTrueHessian A a b t x-A)‖=_
  rw [cgOperator,map_sub]
  change ‖cgOperator (oneGradientCubicTrueHessian A a b t x)-cgOperator A‖=_
  rw [oneGradientCubicTrueHessian_operator]

/-- A genuine source Hessian within a sufficiently small physical drift
has the original printed relative spectral interval.
Article: main_krylov, thm:LB, spec H_star subset[mu(1-delta),L(1+delta)]. -/
theorem oneGradient_true_metric_spectral_interval
    (A B : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (hB : B.PosDef)
    (μ L η : ℝ) (hμ : 0<μ) (hμL : μ≤L) (hη : 0≤η)
    (hband : ∀ i,μ≤hA.1.eigenvalues i ∧hA.1.eigenvalues i≤L)
    (hBA : ‖B-A‖≤η*μ) :
    ∀ i,μ*(1-η)≤hB.1.eigenvalues i ∧hB.1.eigenvalues i≤L*(1+η) := by
  have hlo := spectral_lower_perturbation A B hA.1 hB.1 (fun i=>(hband i).1) hBA
  have hAn : ‖A‖≤L := spectral_norm_le_of_eigenvalues A hA.1 (hμ.le.trans hμL)
    (fun i=>⟨hμ.le.trans (hband i).1,(hband i).2⟩)
  have hBn : ‖B‖≤η*μ+L := (norm_le_norm_sub_add B A).trans (add_le_add hBA hAn)
  intro i
  refine ⟨by nlinarith only [hlo i],?_⟩
  have he := eigenvalue_abs_le_spectral_norm B hB.1 i
  have hu := (le_abs_self (hB.1.eigenvalues i)).trans (he.trans hBn)
  have hscale := mul_le_mul_of_nonneg_left hμL hη
  nlinarith only [hu,hscale]

end
end krylov.Convergence
