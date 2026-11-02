import krylov.Functions.EndpointValueReader

/-!
Article: main_krylov, thm:Fplanar, actual scalar global continuation.
Use: execute the globally admitted original method on a genuine scalar
objective and identify its actual final queried point. Source: direct
causal execution of the original correction trees and true scalar searches.
-/
namespace krylov.Functions
noncomputable section
open krylov.Methods krylov.Reference
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The true scalar executor has exactly one record per actual iteration.
Article: main_krylov, thm:Fplanar. -/
theorem scalarFunctionRun_length (m : ProbedMethod E) (T : E ≃L[ℝ] E)
    (f : E → ℝ) (G : E → E) (R : ℝ) (x₀ : E) (k : ℕ) :
    (scalarFunctionRun m T f G R x₀ k).records.length=k := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [scalarFunctionRun,List.length_cons] using congrArg Nat.succ ih

/-- The genuine global value-aware method executes exactly its original
scalar prefix before the final correction, on every scalar objective.
No prescribed query path or derivative is used. Article: thm:Fplanar. -/
theorem scalarFunctionRun_valueContinued_before (m : ProbedMethod E) (N : ℕ)
    (choose : History E → E → E) (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (R : ℝ) (x₀ : E) (k : ℕ) (hk : k<N) :
    scalarFunctionRun (valueContinuedMethod m N choose) T f G R x₀ k=
      scalarFunctionRun m T f G R x₀ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    let H := scalarFunctionRun m T f G R x₀ k
    have hlen : H.records.length=k := scalarFunctionRun_length m T f G R x₀ k
    have hd : (valueContinuedMethod m N choose).direction H=m.direction H :=
      ite_eq_left (by omega)
    have hc z : (valueContinuedMethod m N choose).correction H z=m.correction H z := by
      change (if H.records.length+1=N then _ else if H.records.length<N then _ else _)=_
      rw [ite_eq_right (by omega),ite_eq_left (by omega)]
    have hr : scalarFunctionRecord (valueContinuedMethod m N choose) T f G R x₀ H=
        scalarFunctionRecord m T f G R x₀ H := by
      unfold scalarFunctionRecord
      rw [hd]
      dsimp only
      rw [hc]
    rw [scalarFunctionRun,scalarFunctionRun,ih (by omega)]
    change (⟨H.initial,scalarFunctionRecord (valueContinuedMethod m N choose) T f G R x₀ H::H.records⟩ : History E)=_
    rw [hr]

/-- The real globally continued scalar executor evaluates exactly the
genuine searched endpoint plus its compiled data-only candidate. Its
current probe is reconstructed from actual gradient differences, before
the new final gradient is queried. Article: thm:Fplanar. -/
theorem scalarFunctionPoint_valueContinued_final (m : ProbedMethod E) (N : ℕ)
    (choose : History E → E → E) (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (R : ℝ) (x₀ : E) (k : ℕ) (hfinal : k+1=N) :
    let H := scalarFunctionRun m T f G R x₀ k
    let x := x₀+H.displacement
    let d := m.direction H
    let y := metricLocalExactPoint T f x d R
    let z := (observedLineParameter d (y-x))⁻¹ • (G y-H.gradient)
    scalarFunctionPoint (valueContinuedMethod m N choose) T f G R x₀ (k+1)=
      y+guardedValueCandidate m choose H z := by
  let H := scalarFunctionRun m T f G R x₀ k
  let x := x₀+H.displacement
  let d := m.direction H
  let y := metricLocalExactPoint T f x d R
  let z := (observedLineParameter d (y-x))⁻¹ • (G y-H.gradient)
  have hlen : H.records.length=k := scalarFunctionRun_length m T f G R x₀ k
  have hd : (valueContinuedMethod m N choose).direction H=m.direction H := ite_eq_left (by omega)
  have hc : (valueContinuedMethod m N choose).correction H z=guardedValueAfter m choose H z :=
    ite_eq_left (by omega)
  have hs : (scalarFunctionRecord (valueContinuedMethod m N choose) T f G R x₀ H).step=
      (y-x)+guardedValueCandidate m choose H z := by
    unfold scalarFunctionRecord
    rw [hd]
    change (y-x)+(scalarFunctionCorrections ((valueContinuedMethod m N choose).correction H z) G y).movement=_
    rw [hc]
    simp only [guardedValueAfter,scalarFunctionCorrections,add_zero]
  rw [scalarFunctionPoint,scalarFunctionRun,scalarFunctionRun_valueContinued_before m N choose T f G R x₀ k (by omega)]
  change x₀+((scalarFunctionRecord (valueContinuedMethod m N choose) T f G R x₀ H).step+H.displacement)=_
  rw [hs]
  dsimp only [x]
  module

end
end krylov.Functions
