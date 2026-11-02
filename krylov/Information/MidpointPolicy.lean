import krylov.Information.MidpointModelDirection
import krylov.Information.ObservedExtension
import krylov.Information.UnobservedNormal
import krylov.Information.MidpointCoefficient
import krylov.Methods.ChangedFinalExecution
import krylov.Correction.FirstIncrementGeometry
import krylov.Information.PlanarTerminalExecution

/-!
Article: main_krylov, thm:C2(c), actual finite-history known-base midpoint policy.
Use: reconstruct the genuine observed increment restriction from real
stored raw directions and probes, form its true consistency midpoint and
execute the actual one-query terminal model replacement.
Source: original known-base probe differences, exact full-query extension,
actual inverse-transpose normal and boundary-inclusive completion midpoint.
-/

namespace krylov.Information
noncomputable section
open Matrix Filter Asymptotics Topology Finset krylov.Reference krylov.Secant krylov.Envelope
  krylov.Correction krylov.Methods krylov.LinearAlgebra krylov.Stability krylov.Variation
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {N : ℕ}

/-- The true canonical raw query array read exclusively from the actual current direction and observed complete history.
Use: retain the original later-query hyperplane using only genuine available finite observations.
Article: main_krylov, thm:C2(c), actual observed canonical directions. -/
def observedCanonicalQueries (base : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (H : History (EuclideanSpace ℝ (Fin (N+1)))) (z : EuclideanSpace ℝ (Fin (N+1)))
    (i : Fin (N+1)) : EuclideanSpace ℝ (Fin (N+1)) :=
  cgOperator (metricRoot base) (historyQueryArray N H ((rfcMethod fullMemory 1).direction H) z i).1

/-- The actual canonical increment actions recovered from known-base probe differences, with the unobserved oldest slot set to zero.
Use: no unknown full source operator enters the genuine informed decision.
Article: main_krylov, thm:C2(c), data-only later increment images. -/
def observedIncrementImages (base : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (H : History (EuclideanSpace ℝ (Fin (N+1)))) (z : EuclideanSpace ℝ (Fin (N+1)))
    (i : Fin (N+1)) : EuclideanSpace ℝ (Fin (N+1)) :=
  if i.val<N then
    let p := historyQueryArray N H ((rfcMethod fullMemory 1).direction H) z i
    cgOperator (metricRoot base)⁻¹ (p.2-cgOperator base p.1)
  else 0

/-- The genuine finite-history consistency midpoint reconstructed solely from observed directions and probe answers plus the known prior.
Use: define the informed selector on all histories without assuming any selector regularity.
Article: main_krylov, thm:C2(c), actual informed midpoint decision. -/
def observedMidpoint (base : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (g : EuclideanSpace ℝ (Fin (N+1))) (ω : ℝ)
    (H : History (EuclideanSpace ℝ (Fin (N+1)))) (z : EuclideanSpace ℝ (Fin (N+1))) : ℝ :=
  let U := observedCanonicalQueries base H z
  let Y := observedIncrementImages base H z
  let v := transportedUnitNormal (fullBasisMatrix U) (sourceQueryMatrix base g 0) (canonicalCGUnitStep base g 0)
  budgetCompletionMidpoint ω v (canonicalCGUnitStep base g 0) (queryDataMatrix U Y)

/-- The genuine data-only midpoint change of the actual last native coefficient model.
Use: preserve true reference column scales while replacing the hidden first-CG scalar.
Article: main_krylov, thm:C2(c), observed informed native change. -/
def midpointModelChange (base : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (g : EuclideanSpace ℝ (Fin (N+1))) (ω : ℝ)
    (H : History (EuclideanSpace ℝ (Fin (N+1)))) (z : EuclideanSpace ℝ (Fin (N+1))) :
    Matrix (Fin (N+1)) (Fin (N+1)) ℝ := observedMidpoint base g ω H z • midpointModelDirection base g

/-- The actual known-base informed method, with the complete original RFC prefix and one true midpoint-modified terminal correction.
Use: supply a concrete source policy for the genuine sharp informed minimax upper bound.
Article: main_krylov, thm:C2(c), true known-base attaining algorithm. -/
def knownBaseMidpointMethod (base : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (g : EuclideanSpace ℝ (Fin (N+1))) (ω : ℝ) : ProbedMethod (EuclideanSpace ℝ (Fin (N+1))) :=
  changedFinalMethod N (midpointModelChange base g ω)

/-- The genuine finite-history canonical query array is exactly the original source executor's actual raw query basis.
Use: connect the data-only normal to the proved actual source normal tube.
Article: main_krylov, thm:C2(c), exact actual direction reconstruction.
Proof: read the genuine chronological raw query transcript at each original newest-first index. -/
theorem observedCanonicalQueries_run (base : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (g : EuclideanSpace ℝ (Fin (N+1))) (Θ : symmetricScenarios (N+1) (N+1)) :
    observedCanonicalQueries base
      (methodRun (rfcMethod fullMemory 1) (scenarioProbe base Θ.val) (scenarioCorrection base Θ.val) g N)
      (probedProbe (rfcMethod fullMemory 1) (scenarioProbe base Θ.val) (scenarioCorrection base Θ.val) g N)=
      sourceQueryColumns base g Θ := by
  funext i
  unfold observedCanonicalQueries
  change cgOperator (metricRoot base) (historyQueryArray N _
    (probedDirection (rfcMethod fullMemory 1) _ _ g N) (probedProbe (rfcMethod fullMemory 1) _ _ g N) i).1=_
  rw [historyQueryArray_run]
  rfl

/-- A positive original increment horizon sums the one genuine first increment exactly once.
Use: derive later known-base probe differences directly from the primitive source sequence.
Article: main_krylov, thm:C2(c), exact original single-increment sum.
Proof: the original range contains zero once and all other true increment slots vanish. -/
theorem firstIncrement_sum {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) {k : ℕ} (hk : 0<k) :
    ∑ i∈range k, firstIncrement M i=M := by
  rw [sum_eq_single 0]
  · simp only [firstIncrement,ite_true]
  · intro i _ hi
    simp only [firstIncrement,ite_eq_right hi]
  · exact fun h => (h (mem_range.mpr hk)).elim

/-- Every genuine later probe in the original one-increment model is precisely the known base plus the physical congruence of that first increment.
Use: recover the actual increment action from each true measured later probe.
Article: main_krylov, thm:C2(c), actual later single-increment oracle.
Proof: use the proved exact single-increment sum in the true canonical probe definition. -/
theorem firstIncrement_probe {n : ℕ} (base M : Matrix (Fin n) (Fin n) ℝ)
    {k : ℕ} (hk : 0<k) : canonicalFCPath base (firstIncrement M) 1 k=
      cgOperator base+cgOperator (metricRoot base*M*metricRoot base) := by
  simp only [canonicalFCPath,one_smul,cumulativeDrift,firstIncrement_sum M hk]
  rfl

/-- Every genuine later finite-history probe difference recovers exactly the true original canonical first-increment image on that actual query.
Use: discharge the information-access premise using real measured data rather than an assumed observed full operator.
Article: main_krylov, thm:C2(c), exact actual increment-image reconstruction.
Proof: the original transcript gives the real probe and direction. Its positive chronological index includes the genuine first increment. Subtract the known base and cancel the actual inverse metric root. -/
theorem observedIncrementImages_run (base : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (Θ : symmetricScenarios (N+1) (N+1))
    (M : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (hE : matrixSequenceExtension N Θ.val.1=firstIncrement M)
    (i : Fin (N+1)) (hi : i.val<N) :
    observedIncrementImages base
      (methodRun (rfcMethod fullMemory 1) (scenarioProbe base Θ.val) (scenarioCorrection base Θ.val) g N)
      (probedProbe (rfcMethod fullMemory 1) (scenarioProbe base Θ.val) (scenarioCorrection base Θ.val) g N) i=
      cgOperator M (sourceQueryColumns base g Θ i) := by
  -- Recover the true source operator action from the genuine chronological observed later probe.
  unfold observedIncrementImages
  rw [ite_eq_left hi]
  change cgOperator (metricRoot base)⁻¹ ((historyQueryArray N _
    (probedDirection (rfcMethod fullMemory 1) _ _ g N) (probedProbe (rfcMethod fullMemory 1) _ _ g N) i).2-
    cgOperator base (historyQueryArray N _
    (probedDirection (rfcMethod fullMemory 1) _ _ g N) (probedProbe (rfcMethod fullMemory 1) _ _ g N) i).1)=_
  rw [historyQueryArray_run]
  change cgOperator (metricRoot base)⁻¹
    (scenarioProbe base Θ.val (N-i.val) (probedDirection (rfcMethod fullMemory 1) _ _ g (N-i.val))-
      cgOperator base (probedDirection (rfcMethod fullMemory 1) _ _ g (N-i.val)))=_
  have hA : scenarioProbe base Θ.val=canonicalFCPath base (firstIncrement M) 1 := by
    change canonicalFCPath base (matrixSequenceExtension N Θ.val.1) 1=_
    rw [hE]
  have horacle (d : EuclideanSpace ℝ (Fin (N+1))) :
      cgOperator (metricRoot base)⁻¹ (scenarioProbe base Θ.val (N-i.val) d-cgOperator base d)=
        cgOperator M (cgOperator (metricRoot base) d) := by
    rw [hA,firstIncrement_probe base M (by omega)]
    simp only [_root_.add_apply,add_sub_cancel_left]
    rw [← inverseRootForm base M hb,inverseRootForm_action base M hb]
  exact horacle _

/-- The genuine finite-history informed midpoint equals the original true-source completion midpoint on its actual observed moving hyperplane.
Use: the sharp geometric coefficient applies to a concrete nonanticipating policy built only from available measurements.
Article: main_krylov, thm:C2(c), complete actual finite-data midpoint bridge.
Proof: the genuine observed directions are the true query basis, and every later probe difference is its original increment image. The actual unit normal annihilates exactly those real later columns. The proved full-query extension theorem identifies the entire genuine completion restriction and hence its true midpoint. -/
theorem observedMidpoint_run (base : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hcount : referenceAtomCount base hb g=N+1)
    (Θ : symmetricScenarios (N+1) (N+1)) (hu : IsUnit (sourceQueryMatrix base g Θ).det)
    (hv : ‖sourceUnobservedNormal base g Θ‖=1)
    (M : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (hE : matrixSequenceExtension N Θ.val.1=firstIncrement M) (ω : ℝ) :
    observedMidpoint base g ω
      (methodRun (rfcMethod fullMemory 1) (scenarioProbe base Θ.val) (scenarioCorrection base Θ.val) g N)
      (probedProbe (rfcMethod fullMemory 1) (scenarioProbe base Θ.val) (scenarioCorrection base Θ.val) g N)=
      budgetCompletionMidpoint ω (sourceUnobservedNormal base g Θ) (canonicalCGUnitStep base g 0) M := by
  -- All actual observed columns determine the same full source completion restriction.
  unfold observedMidpoint
  dsimp only
  rw [observedCanonicalQueries_run]
  apply queryDataMatrix_midpoint _ _ hu _ _ hv (Fin.last N)
  · intro i hi
    exact sourceUnobservedNormal_orthogonal base hb g hcount Θ hu i (by
      have hlt := i.isLt
      by_contra hn
      apply hi
      apply Fin.ext
      simp only [Fin.val_last]
      omega)
  · intro i hi
    apply observedIncrementImages_run base hb g Θ M hE i
    have hlt := i.isLt
    by_contra hn
    apply hi
    apply Fin.ext
    simp only [Fin.val_last]
    omega

end
end krylov.Information
