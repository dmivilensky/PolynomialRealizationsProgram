import krylov.Methods.DeferredMethod
import krylov.Methods.FullProbedWindow

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:mu(d), actual final deferred secant equations.
Use: identify the genuine final current-direction pairing with every
true earlier recorded secant in the actual full observed history.
Source: real full-window pair membership and the proved genuine deferred
observed conjugacy equation on its actual inverse domain.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual final deferred direction has precisely the prescribed true inverse-estimate secant/old-step residual pairing for every genuine earlier recorded pair.
Use: The actual final deferred direction has precisely the prescribed true inverse-estimate secant/old-step residual pairing for every genuine earlier recorded pair.
Article: main_krylov, apB:lem:mu(d), actual final deferred secant equations.
Proof: Locate the actual chronological pair in the genuine full retained window and apply the real deferred inverse solve selected by the true final iteration count. -/
theorem deferredMethod_last_secant_pairing (a : ℝ) (A B : ℕ → E →L[ℝ] E) (g : E) (k i : ℕ) (hi : i<k)
    (hdet : IsUnit (crossGram
      (windowImages (selectedWindow fullMemory (methodRun (deferredMethod fullMemory (k+1) a) A B g k)))
      (windowSteps (selectedWindow fullMemory (methodRun (deferredMethod fullMemory (k+1) a) A B g k)))).det) :
    inner ℝ (probedSecant (deferredMethod fullMemory (k+1) a) A B g i)
      (probedDirection (deferredMethod fullMemory (k+1) a) A B g k)=
    -a⁻¹*inner ℝ (probedStep (deferredMethod fullMemory (k+1) a) A B g i)
      (probedGradient (deferredMethod fullMemory (k+1) a) A B g k) := by
  -- Locate the real earlier recorded pair in the genuine full window before reading its actual tilted conjugacy equation.
  let m := deferredMethod fullMemory (k+1) a (E := E)
  let H := methodRun m A B g k
  let W := selectedWindow fullMemory H
  have hp : (probedStep m A B g i,probedSecant m A B g i)∈W := probedPair_mem_fullWindow m A B g k i hi
  obtain ⟨j,hj,hget⟩ := List.mem_iff_getElem.mp hp
  have hx : windowSteps W (⟨j,hj⟩ : Fin W.length)=probedStep m A B g i := congrArg Prod.fst hget
  have hy : windowImages W (⟨j,hj⟩ : Fin W.length)=probedSecant m A B g i := congrArg Prod.snd hget
  -- The true observed record count selects the actual deferred solve at its genuine final iteration.
  have hd : probedDirection m A B g k=deferredDirection (windowSteps W) (windowImages W) H.gradient a := by
    change (if H.records.length+1=k+1 then _ else _)=_
    rw [show H.records.length=k from methodRun_length m A B g k,ite_eq_left rfl]
  have hc := deferredDirection_conjugacy (windowSteps W) (windowImages W) H.gradient a hdet (⟨j,hj⟩ : Fin W.length)
  rw [← hd,hx,hy] at hc
  exact hc
end
end krylov.Methods
