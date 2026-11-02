import krylov.Envelope.Continuation

set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(a), genuine finite continuation coefficient dependence.
Use: transfer true measured CG continuation coefficients through an actual Lanczos prefix while ignoring the genuinely unused terminal recurrence ratio.
Source: the actual finite gradient/direction continuation state and genuine chronological coefficient ranges.
-/

namespace krylov.Envelope
noncomputable section
open Polynomial

/-- The actual complete finite continuation state depends only on the genuine used line and recurrence coefficients.
Use: The actual complete finite continuation state depends only on the genuine used line and recurrence coefficients.
Article: main_krylov, prop:phi(a), genuine finite continuation coefficient dependence.
Proof: Induct through the real continuation updates and replace exactly their actual chronological input coefficients. -/
theorem continuationRun_congr (α β a b : ℕ → ℝ) (j k : ℕ)
    (ha : ∀ i<k,α (j+i)=a (j+i)) (hb : ∀ i<k,β (j+i)=b (j+i)) :
    continuationRun α β j k=continuationRun a b j k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [continuationRun,continuationRun,ih (fun i hi => ha i (by omega)) (fun i hi => hb i (by omega)),
      ha k (by omega),hb k (by omega)]

/-- The genuine terminal continuation residual does not depend on the actual last recurrence ratio.
Use: The genuine terminal continuation residual does not depend on the actual last recurrence ratio.
Article: main_krylov, prop:phi(a), genuine finite continuation coefficient dependence.
Proof: Match the true preceding complete state, then apply the final actual gradient update, which uses only its genuine last line coefficient. -/
theorem phi_coefficients_congr (α β a b : ℕ → ℝ) (j k : ℕ)
    (ha : ∀ i<k,α (j+i)=a (j+i)) (hb : ∀ i,i+1<k → β (j+i)=b (j+i)) :
    phi α β j k=phi a b j k := by
  cases k with
  | zero => rfl
  | succ k =>
    have he := continuationRun_congr α β a b j k (fun i hi => ha i (by omega)) (fun i hi => hb i (by omega))
    have hφ : phi α β j k=phi a b j k := congrArg Prod.fst he
    have hψ : psi α β j k=psi a b j k := congrArg Prod.snd he
    rw [phi_succ,phi_succ,hφ,hψ,ha k (by omega)]
end
end krylov.Envelope
