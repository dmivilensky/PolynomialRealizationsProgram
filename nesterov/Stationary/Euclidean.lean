import nesterov.Rates.Envelope
import polyak.Functions.Embedding
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
Article: Definition `def:rate` and Remark `rem:uniform-smoothness`.
Use: finite-dimensional Hilbert executions are genuine Euclidean executions,
with every point, initial condition and state norm transported isometrically.
The extra quadratic coordinate guarantees positive ambient dimension.
-/
namespace nesterov.Rates.HilbertRun
noncomputable section
open scoped BigOperators ContDiff

variable {M : StationaryMethod} {μ L : ℝ} (r : HilbertRun M μ L)
variable [FiniteDimensional ℝ r.Carrier]

/-- A concrete isometric coordinate map into a positive Euclidean dimension. -/
def euclideanMap : r.Carrier →ₗᵢ[ℝ]
    EuclideanSpace ℝ (Fin (Module.finrank ℝ r.Carrier+1)) :=
  (polyak.euclideanInclusion (Module.finrank ℝ r.Carrier) 1).comp
    (stdOrthonormalBasis ℝ r.Carrier).repr.toLinearIsometry

/-- The genuine objective on the Euclidean ambient space. -/
def euclideanObjective : EuclideanSpace ℝ (Fin (Module.finrank ℝ r.Carrier+1)) → ℝ :=
  polyak.extendObjective μ L (euclideanMap r) r.f

theorem euclideanObjective_admissible :
    polyak.CenteredSmoothStronglyConvex μ L (euclideanObjective r) :=
  r.admissible.extendObjective (euclideanMap r)

/-- All queried gradients transport through the same isometry. -/
theorem gradient_euclideanObjective (x : r.Carrier) :
    gradient (euclideanObjective r) (euclideanMap r x)=euclideanMap r (gradient r.f x) :=
  polyak.gradient_extendObjective_embed r.admissible.toSmoothStronglyConvex (euclideanMap r) x

/-- The actual complete trajectory transports, rather than merely its formal recurrence. -/
theorem euclidean_trajectory :
    M.IsTrajectory (gradient (euclideanObjective r)) (fun k => euclideanMap r (r.w k)) := by
  intro k
  have hq : M.query (fun i => euclideanMap r (r.w i)) k =
      euclideanMap r (M.query r.w k) := by simp [StationaryMethod.query,map_sum,map_smul]
  rw [hq,gradient_euclideanObjective]
  simpa only [map_sum,map_smul] using congrArg (euclideanMap r) (r.trajectory k)

/-- One actual Euclidean run with all original trajectories and norms retained. -/
def euclidean : HilbertRun M μ L where
  Carrier := EuclideanSpace ℝ (Fin (Module.finrank ℝ r.Carrier+1))
  f := euclideanObjective r
  admissible := euclideanObjective_admissible r
  w k := euclideanMap r (r.w k)
  trajectory := euclidean_trajectory r

@[simp] theorem euclidean_norm (k : ℕ) : ‖(euclidean r).w k‖=‖r.w k‖ :=
  (euclideanMap r).norm_map _

@[simp] theorem euclidean_stateNorm (k : ℕ) : (euclidean r).stateNorm k=r.stateNorm k := by
  change Real.sqrt (∑ j : Fin M.memory, ‖euclideanMap r (r.w (k+j))‖^2)=_
  simp only [(euclideanMap r).norm_map]
  rfl

/-- Infinite smoothness survives the coordinate transport and added quadratic direction. -/
theorem euclideanObjective_contDiff (hf : ContDiff ℝ ∞ r.f) :
    ContDiff ℝ ∞ (euclideanObjective r) := by
  unfold euclideanObjective polyak.extendObjective polyak.denormalizeFunction
    polyak.extendPotential polyak.normalizeFunction
  have hp : ContDiff ℝ ∞ (polyak.embeddingProjection (euclideanMap r)) :=
    (polyak.embeddingProjection (euclideanMap r)).contDiff
  have hn : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin (Module.finrank ℝ r.Carrier+1)) => ‖x‖^2) :=
    contDiff_norm_sq ℝ
  have hn' : ContDiff ℝ ∞ (fun x => ‖polyak.embeddingProjection (euclideanMap r) x‖^2) :=
    (contDiff_norm_sq ℝ).comp hp
  exact (contDiff_const.mul hn).sub (contDiff_const.mul
    (((contDiff_const.mul hn').sub (contDiff_const.mul (hf.comp hp))).div_const _))

end
end nesterov.Rates.HilbertRun
