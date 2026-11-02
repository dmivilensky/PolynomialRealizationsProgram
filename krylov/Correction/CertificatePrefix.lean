import krylov.Correction.CertificatePhase
import krylov.Methods.SmoothProbedFields

/-!
Article: main_krylov, prop:deep, genuine source execution and singular-model certification.
Use: Actual finite source-prefix correspondence with the original real RFC executor.
Source: original RFC array execution, earlier-package integer checker
soundness, standard real continuity and the intermediate value theorem.
-/

namespace krylov.Correction.Certificate
noncomputable section
open Matrix Finset chebyshev2.Numerics.IntegerCertificate krylov.Methods krylov.Reference
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

/-- The exact finite source-program prefix with its genuine current gradient and newest-first total-step and measured-secant arrays.
Use: Connect checked arithmetic to the actual original stored-data executor.
Article: main_krylov, prop:deep, actual checked source-family argument. -/
structure TermPrefix (n k : ℕ) where
  /-- The actual current observed-gradient expression after the completed prefix. -/
  gradient : Fin n → Term
  /-- The actual earlier total evaluated-step expressions in genuine newest-first order. -/
  steps : Fin k → Fin n → Term
  /-- The actual earlier measured gradient-difference secant expressions in the same storage order. -/
  images : Fin k → Fin n → Term

/-- The genuine conjugacy-direction expression of the current compiled observed prefix.
Use: Use precisely the original data-only direction rule.
Article: main_krylov, prop:deep, actual checked source-family argument. -/
def TermPrefix.direction {n k : ℕ} (h : TermPrefix n k) : Fin n → Term :=
  termDirection h.steps h.images h.gradient

/-- The original next gradient, total evaluated step and measured gradient-difference secant compiled from one actual source phase.
Use: Retain all real recorded source data in the next arithmetic certificate.
Article: main_krylov, prop:deep, actual checked source-family argument. -/
def TermPrefix.advance {n k : ℕ} (h : TermPrefix n k)
    (A B : Matrix (Fin n) (Fin n) Term) : TermPrefix n (k+1) :=
  let d := h.direction
  let z := termMatVec A d
  let gn := termPhaseGradient h.steps h.images h.gradient d z B
  let step := termPhaseStep h.steps h.images h.gradient d z
  ⟨gn,Fin.cons step h.steps,Fin.cons (termAdd gn (termNeg h.gradient)) h.images⟩

/-- The genuine finite original full-memory one-correction RFC arithmetic prefix, retaining actual total steps and measured secants.
Use: Define a source execution independently of any generated interval annotations.
Article: main_krylov, prop:deep, actual checked source-family argument. -/
def termRun {n : ℕ} (A B : ℕ → Matrix (Fin n) (Fin n) Term) (g : Fin n → Term) : (k : ℕ) → TermPrefix n k
  | 0 => ⟨g,Fin.elim0,Fin.elim0⟩
  | k+1 => (termRun A B g k).advance (A k) (B k)

/-- The actual executed full-memory RFC direction is exactly its finite newest-first observed-array conjugacy solve.
Use: Identify the real policy decision with the same independently compiled source arrays.
Article: main_krylov, prop:deep, actual checked source-family argument.
Proof: The genuine retained-window transcript has its actual chronological ages. The existing exact window-direction coordinate theorem removes the true finite length cast. -/
theorem full_rfc_direction_array {n : ℕ} (count : ℕ)
    (A B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    probedDirection (rfcMethod fullMemory count) A B g k=
      conjugacyDirection
        (fun i : Fin k => probedStep (rfcMethod fullMemory count) A B g (k-1-i.val))
        (fun i : Fin k => probedSecant (rfcMethod fullMemory count) A B g (k-1-i.val))
        (probedGradient (rfcMethod fullMemory count) A B g k) := by
  change windowDirection (selectedWindow fullMemory (methodRun (rfcMethod fullMemory count) A B g k))
    (probedGradient (rfcMethod fullMemory count) A B g k)=_
  rw [selectedWindow_methodRun,windowDirection_executed_take]
  rw [show min (fullMemory k) k=k from min_self k]

/-- Exact equality between a compiled source prefix and the genuine RFC gradient, recorded total steps and measured secants on its actual interpreted physical oracle sequence.
Use: State the correspondence that the finite source induction derives.
Article: main_krylov, prop:deep, actual checked source-family argument. -/
def TermPrefix.Realizes {n k : ℕ} (h : TermPrefix n k)
    (A B : ℕ → Matrix (Fin n) (Fin n) Term) (g : Fin n → Term) (x : ℕ → ℝ) : Prop :=
  let Ap := fun k => cgOperator (matrixValue (A k) x)
  let Bp := fun k => cgOperator (matrixValue (B k) x)
  let m := rfcMethod fullMemory 1
  euclideanValue h.gradient x=probedGradient m Ap Bp (euclideanValue g x) k ∧
    (∀ i : Fin k, euclideanValue (h.steps i) x=probedStep m Ap Bp (euclideanValue g x) (k-1-i.val)) ∧
    (∀ i : Fin k, euclideanValue (h.images i) x=probedSecant m Ap Bp (euclideanValue g x) (k-1-i.val))

/-- One actual empty or accepted source-data gate propagates exact equality of the compiled prefix with the true RFC gradient and all newly recorded physical data.
Use: Tie arithmetic certificate states to the original real oracle executor without assuming a desired trajectory.
Article: main_krylov, prop:deep, actual checked source-family argument.
Proof: Identify the true current gradient and actual observed arrays first. Their proved conjugacy semantics give the real chosen direction and true probe. The actual array-phase theorem gives the returned gradient and total step, while the real measured secant is the difference of consecutive actual gradients. Split the genuine newest record from the preserved earlier tail. -/
theorem TermPrefix.Realizes.advance {n k : ℕ} {h : TermPrefix n k}
    {A B : ℕ → Matrix (Fin n) (Fin n) Term} {g : Fin n → Term} {x : ℕ → ℝ}
    (hh : h.Realizes A B g x)
    (hgate : k=0 ∨ 0<k ∧ ‖pairDefect (fun i => euclideanValue (h.steps i) x) (fun i => euclideanValue (h.images i) x)‖<1) :
    (h.advance (A k) (B k)).Realizes A B g x := by
  -- Fix the actual gradient and recorded arrays before comparing the real direction, probe and executed phase.
  let Ap := fun j => cgOperator (matrixValue (A j) x)
  let Bp := fun j => cgOperator (matrixValue (B j) x)
  let g₀ := euclideanValue g x
  let m := rfcMethod fullMemory 1 (E := EuclideanSpace ℝ (Fin n))
  let S := fun i : Fin k => probedStep m Ap Bp g₀ (k-1-i.val)
  let Y := fun i : Fin k => probedSecant m Ap Bp g₀ (k-1-i.val)
  have hg : euclideanValue h.gradient x=probedGradient m Ap Bp g₀ k := hh.1
  have hs : (fun i => euclideanValue (h.steps i) x)=S := funext hh.2.1
  have hy : (fun i => euclideanValue (h.images i) x)=Y := funext hh.2.2
  have hd : euclideanValue h.direction x=probedDirection m Ap Bp g₀ k := by
    rw [TermPrefix.direction,termDirection_value,hs,hy,hg]
    exact (full_rfc_direction_array 1 Ap Bp g₀ k).symm
  have hz : euclideanValue (termMatVec (A k) h.direction) x=Ap k (probedDirection m Ap Bp g₀ k) := by
    rw [euclideanValue_matVec,hd]
    rfl
  have hp := termPhase_value h.steps h.images h.gradient h.direction (termMatVec (A k) h.direction) (B k) x hgate
  dsimp only at hp
  rw [hs,hy,hg,hd,hz] at hp
  have he := probedRFC_phase_array fullMemory 1 Ap Bp g₀ k
  rw [show min (fullMemory k) k=k from min_self k] at he
  change probedPhase m Ap Bp g₀ k=rfcArrayPhase S Y (probedGradient m Ap Bp g₀ k)
    (probedDirection m Ap Bp g₀ k) (Ap k (probedDirection m Ap Bp g₀ k)) (Bp k) 1 at he
  change euclideanValue (termPhaseGradient h.steps h.images h.gradient h.direction (termMatVec (A k) h.direction) (B k)) x=
      (rfcArrayPhase S Y _ _ _ (Bp k) 1).gradient ∧
    euclideanValue (termPhaseStep h.steps h.images h.gradient h.direction (termMatVec (A k) h.direction)) x=
      lineLength (probedGradient m Ap Bp g₀ k) (probedDirection m Ap Bp g₀ k) (Ap k (probedDirection m Ap Bp g₀ k)) •
        probedDirection m Ap Bp g₀ k+
        (rfcArrayPhase S Y (probedGradient m Ap Bp g₀ k) (probedDirection m Ap Bp g₀ k)
          (Ap k (probedDirection m Ap Bp g₀ k)) (Bp k) 1).movement at hp
  simp only [← he] at hp
  refine ⟨?_,?_,?_⟩
  · change euclideanValue (termPhaseGradient h.steps h.images h.gradient h.direction (termMatVec (A k) h.direction) (B k)) x=_
    exact hp.1
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · have hi : k+1-1-(0 : Fin (k+1)).val=k := by simp
      change euclideanValue (termPhaseStep h.steps h.images h.gradient h.direction (termMatVec (A k) h.direction)) x=_
      rw [hi]
      exact hp.2
    · have hi : k+1-1-j.succ.val=k-1-j.val := by simp only [Fin.val_succ]; omega
      change euclideanValue (h.steps j) x=_
      rw [hi]
      exact hh.2.1 j
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · have hi : k+1-1-(0 : Fin (k+1)).val=k := by simp
      change euclideanValue (termAdd _ (termNeg h.gradient)) x=_
      rw [euclideanValue_add,euclideanValue_neg,hp.1,hg,hi]
      rfl
    · have hi : k+1-1-j.succ.val=k-1-j.val := by simp only [Fin.val_succ]; omega
      change euclideanValue (h.images j) x=_
      rw [hi]
      exact hh.2.2 j


/-- Every finite compiled prefix whose genuine source-array gates pass equals the actual original full-memory RFC gradient and complete recorded step/secant arrays.
Use: Use independently checked real gates to derive the actual source trajectory.
Article: main_krylov, prop:deep, actual checked source-family argument.
Proof: The empty actual prefix agrees exactly. The genuine one-step execution correspondence propagates the actual gradient, total steps and measured secants through every certified source gate. -/
theorem termRun_realizes {n : ℕ} (A B : ℕ → Matrix (Fin n) (Fin n) Term) (g : Fin n → Term)
    (x : ℕ → ℝ) (k : ℕ)
    (hgate : ∀ j<k, j=0 ∨ 0<j ∧
      ‖pairDefect (fun i => euclideanValue ((termRun A B g j).steps i) x)
        (fun i => euclideanValue ((termRun A B g j).images i) x)‖<1) :
    (termRun A B g k).Realizes A B g x := by
  induction k with
  | zero =>
    refine ⟨rfl,?_,?_⟩ <;> intro i <;> exact Fin.elim0 i
  | succ k ih =>
    exact (ih (fun j hj => hgate j (by omega))).advance (hgate k (by omega))

end
end krylov.Correction.Certificate
