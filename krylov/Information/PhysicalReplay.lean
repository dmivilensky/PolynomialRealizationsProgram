import krylov.Information.DirectionSpan
import krylov.Information.PhysicalCentre
import krylov.LinearAlgebra.OldestPair

/-!
Article: main_krylov, thm:centre, complete actual observation replay for the physical twin.
Use: specialize the abstract query replay to the constructed physical
reflection and the method's own genuine direction basis.
Source: the proved physical column preservation, actual direction-span
inclusion for every correction branch, and the true nonanticipating executor.
-/

namespace krylov.Information
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.LinearAlgebra
open scoped Matrix.Norms.L2Operator
variable {p : ℕ}

/-- The real physical probe oracle of a constructed finite scenario.
Use: execute the source scenario through the genuine probed-method protocol.
Article: main_krylov, thm:centre, physical A_k queries. -/
def Scenario.probeOracle (S : Scenario p) :
    ℕ → EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p) :=
  fun k => cgOperator (S.probe k)

/-- The actual intermediate and terminal correction oracle of the finite scenario.
Use: expose intermediate perturbations and the distinct final perturbation to the true executor.
Article: main_krylov, thm:centre, physical B_k queries. -/
def Scenario.correctionOracle (S : Scenario p) (N : ℕ) :
    ℕ → EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p) :=
  fun k => if k<N then cgOperator (S.intermediate k) else cgOperator (S.lastOperator N)

/-- The constructed physical twin preserves the entire actual preterminal run of every source-span-restricted method.
Use: common observations are proved for the method's own arbitrary nondegenerate direction basis, without assuming the desired history equality.
Article: main_krylov, thm:centre, full data-preserving physical involution.
Proof: derive every actual correction branch's inclusion in the method's
own direction flag. The concrete physical reflection preserves the current
probe column and every intermediate correction column in that flag; linearity
extends the latter equality to the entire genuine span. The actual query replay
theorem then preserves every complete history and every intermediate observation. -/
theorem Scenario.physical_twin_run {N : ℕ} (S : Scenario (N+1))
    (D : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hD : IsUnit D.det)
    (memory : ℕ → ℕ) (m : ProbedMethod (EuclideanSpace ℝ (Fin (N+1))))
    (hm : ProbedSpanRestricted memory m) (g : EuclideanSpace ℝ (Fin (N+1)))
    (hdir : ∀ i : Fin (N+1), probedDirection m (S.inPhysical D).probeOracle
      ((S.inPhysical D).correctionOracle N) g i.val=euclideanColumn D i) :
    methodRun m (S.inPhysical D).probeOracle ((S.inPhysical D).correctionOracle N) g N=
      methodRun m ((S.reflect N).inPhysical D).probeOracle
        (((S.reflect N).inPhysical D).correctionOracle N) g N := by
  -- Use the method's true direction flag, derived from the original full execution.
  let A := (S.inPhysical D).probeOracle
  let B := (S.inPhysical D).correctionOracle N
  let C := ((S.reflect N).inPhysical D).probeOracle
  let F := ((S.reflect N).inPhysical D).correctionOracle N
  apply run_replay m A B C F g N (executedDirectionSpan m A B g)
  · intro k hk
    change A k (probedDirection m A B g k)=C k (probedDirection m A B g k)
    rw [hdir (⟨k,by omega⟩ : Fin (N+1))]
    ext a
    exact (S.physical_reflect_probe_column D hD hk.le ⟨k,by omega⟩ rfl a).symm
  · intro k _
    exact correction_in_executedDirectionSpan memory m hm A B g k
  · intro k hk u hu
    -- Check actual preserved matrix columns before extending equality through the genuine span.
    have he : executedDirectionSpan m A B g k≤(B k-F k).toLinearMap.ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j,hj,rfl⟩
      change j≤k at hj
      change B k (probedDirection m A B g j)-F k (probedDirection m A B g j)=0
      rw [hdir (⟨j,by omega⟩ : Fin (N+1))]
      apply sub_eq_zero.mpr
      simp only [B,F,Scenario.correctionOracle,ite_eq_left hk]
      ext a
      exact (S.physical_reflect_intermediate_column D hD hk.le ⟨j,by omega⟩ hj a).symm
    exact sub_eq_zero.mp (he hu)

/-- The physical twin also preserves the genuine final probe after its complete equal preterminal history.
Use: the method sees the same full information before choosing its last correction.
Article: main_krylov, thm:centre, equal final H and z.
Proof: the preceding genuine run theorem gives the same actual final direction;
the constructed physical reflection preserves its true last basis column as well. -/
theorem Scenario.physical_twin_last_probe {N : ℕ} (S : Scenario (N+1))
    (D : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hD : IsUnit D.det)
    (memory : ℕ → ℕ) (m : ProbedMethod (EuclideanSpace ℝ (Fin (N+1))))
    (hm : ProbedSpanRestricted memory m) (g : EuclideanSpace ℝ (Fin (N+1)))
    (hdir : ∀ i : Fin (N+1), probedDirection m (S.inPhysical D).probeOracle
      ((S.inPhysical D).correctionOracle N) g i.val=euclideanColumn D i) :
    probedProbe m (S.inPhysical D).probeOracle ((S.inPhysical D).correctionOracle N) g N=
      probedProbe m ((S.reflect N).inPhysical D).probeOracle
        (((S.reflect N).inPhysical D).correctionOracle N) g N := by
  -- The actual preserved past selects the same true last direction before its preserved physical probe.
  have hr := S.physical_twin_run D hD memory m hm g hdir
  change (S.inPhysical D).probeOracle N (m.direction (methodRun m _ _ g N))=
    ((S.reflect N).inPhysical D).probeOracle N (m.direction (methodRun m _ _ g N))
  rw [← hr]
  change (S.inPhysical D).probeOracle N (probedDirection m _ _ g N)=
    ((S.reflect N).inPhysical D).probeOracle N (probedDirection m _ _ g N)
  have hdN := hdir (Fin.last N)
  simp only [Fin.val_last] at hdN
  rw [hdN]
  ext a
  exact (S.physical_reflect_probe_column D hD le_rfl (Fin.last N) rfl a).symm

/-- The two actual physical scenarios force the same complete last correction decision tree.
Use: in the at-most-one-correction information class their final physical correction query is identical.
Article: main_krylov, thm:centre, common last decision from equal actual data.
Proof: the actual preterminal histories and the real last observed probes
are equal, so the nonanticipating policy receives precisely the same two inputs. -/
theorem Scenario.physical_twin_last_decision {N : ℕ} (S : Scenario (N+1))
    (D : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hD : IsUnit D.det)
    (memory : ℕ → ℕ) (m : ProbedMethod (EuclideanSpace ℝ (Fin (N+1))))
    (hm : ProbedSpanRestricted memory m) (g : EuclideanSpace ℝ (Fin (N+1)))
    (hdir : ∀ i : Fin (N+1), probedDirection m (S.inPhysical D).probeOracle
      ((S.inPhysical D).correctionOracle N) g i.val=euclideanColumn D i) :
    m.correction (methodRun m (S.inPhysical D).probeOracle ((S.inPhysical D).correctionOracle N) g N)
      (probedProbe m (S.inPhysical D).probeOracle ((S.inPhysical D).correctionOracle N) g N)=
    m.correction (methodRun m ((S.reflect N).inPhysical D).probeOracle
      (((S.reflect N).inPhysical D).correctionOracle N) g N)
      (probedProbe m ((S.reflect N).inPhysical D).probeOracle
        (((S.reflect N).inPhysical D).correctionOracle N) g N) := by
  rw [S.physical_twin_run D hD memory m hm g hdir,S.physical_twin_last_probe D hD memory m hm g hdir]

end
end krylov.Information
