import krylov.Methods.RFCProjection
import krylov.Methods.ProjectedModel
import krylov.Functions.MetricSearchOperator
import krylov.Functions.SearchTrajectory

/-!
Article: main_krylov, alg:fc and lem:cycle-transfer, ordinary native RFC.
Use: execute the correction with the genuine evaluated line-step/secant pair
and identify it with the original direction/probe implementation. The model
coordinate change is proved for every nonsingular line scaling, including
singular totalized model solves. Source: the existing exact diagonal model
rescaling theorem, not an assumed algorithmic equivalence.
-/

namespace krylov.Functions
noncomputable section
open Matrix krylov.Methods
open scoped Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual latest-model correction is unchanged when its newest observed
pair is rescaled by the genuine nonzero line-search scalar.
Article: main_krylov, alg:fc and lem:cycle-transfer.
Proof: express both real windows as finite arrays and reuse the exact
nonsingular diagonal model-coordinate identity already proved in the package. -/
theorem newest_pair_model_correction_rescale (W : List (E×E)) (d z g : E)
    (α : ℝ) (hα : α≠0) :
    combine (windowSteps ((α • d,α • z)::W))
      (modelCoefficients (windowSteps ((α • d,α • z)::W)) (windowModel ((α • d,α • z)::W)) g)=
    combine (windowSteps ((d,z)::W))
      (modelCoefficients (windowSteps ((d,z)::W)) (windowModel ((d,z)::W)) g) := by
  let D : Fin (W.length+1) → ℝ := Fin.cons α (fun _ => 1)
  have hD : IsUnit (diagonal D).det := by
    apply isUnit_iff_ne_zero.mpr
    rw [det_diagonal]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    refine Fin.cases ?_ (fun _ => ?_) i
    · exact hα
    · exact one_ne_zero
  have hS : windowSteps ((α • d,α • z)::W)=rescaleWindow (windowSteps ((d,z)::W)) D := by
    rw [windowSteps_cons,windowSteps_cons]
    funext i
    refine Fin.cases ?_ (fun _ => ?_) i <;> simp [rescaleWindow,D]
  have hY : windowImages ((α • d,α • z)::W)=rescaleWindow (windowImages ((d,z)::W)) D := by
    rw [windowImages_cons,windowImages_cons]
    funext i
    refine Fin.cases ?_ (fun _ => ?_) i <;> simp [rescaleWindow,D]
  simp only [← pairModel_window]
  rw [hS,hY,pairModel_rescale]
  exact modelCorrection_rescale _ _ D hD g

/-- The metric chord search used by the physical algorithm, transporting only
its actual primal direction and actual scalar objective.
Article: main_krylov, alg:fc and apG:E. -/
def metricLocalExactPoint (T : E ≃L[ℝ] E) (f : E → ℝ) (x d : E) (r : ℝ) : E :=
  T.symm (localExactPoint (coordinateObjective T f) (T x) (T d) r)

/-- The line parameter is read from the actually evaluated step and direction.
Article: main_krylov, alg:fc, genuine observed exact-search data. -/
def observedLineParameter (d s : E) : ℝ := inner ℝ d s / ‖d‖^2

/-- A nonzero actual direction makes its observed scalar equal its true line multiplier.
Article: main_krylov, lem:cycle-transfer, exact search/probe dictionary. -/
theorem observedLineParameter_smul (d : E) (α : ℝ) (hd : d≠0) :
    observedLineParameter d (α • d)=α := by
  have hnorm : ‖d‖^2≠0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hd)
  rw [observedLineParameter,inner_smul_right,real_inner_self_eq_norm_sq]
  exact mul_div_cancel_right₀ α hnorm

end
end krylov.Functions
