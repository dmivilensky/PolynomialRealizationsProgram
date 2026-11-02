import krylov.LotkaVolterra.GlobalSaddleField
import krylov.AnalyticTools.WeightedDilation
import krylov.AnalyticTools.ContinuousInverse
import krylov.AnalyticTools.OperatorImplicit

/-!
Article: main_krylov, apC:prop:LV, analytic stable graph at the saddle.
Use: lift the actual rational chord-slope equation to continuous paths. Near
the saddle both denominators are units of the path Banach algebra, so their
inverses and the lifted nonlinear equation are analytic.
Source: the Briot--Bouquet integral method and analytic algebra inversion.
-/

namespace krylov.LotkaVolterra
noncomputable section
open Set Filter
open krylov.AnalyticTools
open scoped Topology

abbrev SaddlePaths := C(SymmetricPathDomain, ℝ)

private def coordinatePath : SaddlePaths := ⟨Subtype.val, continuous_subtype_val⟩

def saddleLiftZ (c : ℝ) (p : ℝ × SaddlePaths) : SaddlePaths := (c * p.1) • coordinatePath

def saddleLiftV (r : ℝ) (p : ℝ × SaddlePaths) : SaddlePaths :=
  ContinuousMap.const SymmetricPathDomain r + p.2

/-- The exact nonlinear part H(czu,r+w)+a*w after its linear slope term
has been moved into the regular-singular operator z d/dz+a. -/
def saddleNonlinearLift (γ c r a : ℝ) (p : ℝ × SaddlePaths) : SaddlePaths :=
  ContinuousMap.const SymmetricPathDomain 2 *
    (ContinuousMap.const SymmetricPathDomain (saddleS γ) - saddleLiftV r p * saddleLiftZ c p) *
    Ring.inverse (ContinuousMap.const SymmetricPathDomain (saddleU γ) - saddleLiftZ c p) *
    (ContinuousMap.const SymmetricPathDomain γ - saddleLiftV r p) *
    Ring.inverse (1 - saddleLiftV r p) - saddleLiftV r p + a • p.2

theorem saddleNonlinearLift_apply {γ c r a : ℝ} {p : ℝ × SaddlePaths}
    (hA : IsUnit (ContinuousMap.const SymmetricPathDomain (saddleU γ) - saddleLiftZ c p))
    (hB : IsUnit (1 - saddleLiftV r p)) (u : SymmetricPathDomain) :
    saddleNonlinearLift γ c r a p u =
      saddleSlopeRate γ (c * p.1 * u) (r + p.2 u) + a * p.2 u := by
  simp only [saddleNonlinearLift, ContinuousMap.add_apply, ContinuousMap.sub_apply,
    ContinuousMap.mul_apply, ContinuousMap.smul_apply, ContinuousMap.const_apply]
  rw [inverse_continuousMap_apply hA, inverse_continuousMap_apply hB]
  simp only [saddleLiftZ, saddleLiftV, coordinatePath, ContinuousMap.coe_mk,
    ContinuousMap.smul_apply, ContinuousMap.add_apply, ContinuousMap.sub_apply,
    ContinuousMap.const_apply, ContinuousMap.one_apply, smul_eq_mul]
  unfold saddleSlopeRate
  ring

/-- Both actual rational denominators are invertible at zero path/parameter. -/
theorem saddleLift_units_zero {γ c r : ℝ} (hγ : γ < 1) (hr : r < 1) :
    IsUnit (ContinuousMap.const SymmetricPathDomain (saddleU γ) -
      saddleLiftZ c (0, 0)) ∧ IsUnit (1 - saddleLiftV r (0, 0)) := by
  constructor
  · apply ContinuousMap.isUnit_iff_forall_ne_zero _ |>.mpr
    intro u
    simpa [saddleLiftZ] using (saddleU_pos hγ).ne'
  · apply ContinuousMap.isUnit_iff_forall_ne_zero _ |>.mpr
    intro u
    simpa [saddleLiftV] using (by linarith : (1 : ℝ) - r ≠ 0)

/-- The concrete lifted saddle equation is analytic at its actual base point. -/
theorem analyticAt_saddleNonlinearLift {γ c r a : ℝ} (hγ : γ < 1) (hr : r < 1) :
    AnalyticAt ℝ (saddleNonlinearLift γ c r a) (0, 0) := by
  have hZ : AnalyticAt ℝ (saddleLiftZ c) (0, 0) :=
    (analyticAt_const.mul analyticAt_fst).smul analyticAt_const
  have hV : AnalyticAt ℝ (saddleLiftV r) (0, 0) := analyticAt_const.add analyticAt_snd
  have hA : AnalyticAt ℝ (fun p : ℝ × SaddlePaths ↦
      ContinuousMap.const SymmetricPathDomain (saddleU γ) - saddleLiftZ c p) (0, 0) :=
    analyticAt_const.sub hZ
  have hB : AnalyticAt ℝ (fun p : ℝ × SaddlePaths ↦ 1 - saddleLiftV r p) (0, 0) :=
    analyticAt_const.sub hV
  have hu := saddleLift_units_zero (c := c) hγ hr
  have hAI := (analyticAt_continuousMap_inverse hu.1).comp
    (f := fun p : ℝ × SaddlePaths ↦ ContinuousMap.const SymmetricPathDomain (saddleU γ) -
      saddleLiftZ c p) hA
  have hBI := (analyticAt_continuousMap_inverse hu.2).comp
    (f := fun p : ℝ × SaddlePaths ↦ 1 - saddleLiftV r p) hB
  have ha : AnalyticAt ℝ (fun _ : ℝ × SaddlePaths ↦ a) (0, 0) := analyticAt_const
  exact (((((analyticAt_const.mul (analyticAt_const.sub (hV.mul hZ))).mul hAI).mul
    (analyticAt_const.sub hV)).mul hBI).sub hV).add (ha.smul analyticAt_snd)

/-- A true root of H(0,·) gives the zero nonlinear base path. -/
theorem saddleNonlinearLift_zero {γ c r a : ℝ} (hγ : γ < 1) (hr : r < 1)
    (hroot : saddleSlopeRate γ 0 r = 0) : saddleNonlinearLift γ c r a (0, 0) = 0 := by
  have hu := saddleLift_units_zero (c := c) hγ hr
  ext u
  simpa [hroot] using saddleNonlinearLift_apply (a := a) hu.1 hu.2 u

end
end krylov.LotkaVolterra
