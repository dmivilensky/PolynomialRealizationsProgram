import krylov.Envelope.Continuation

set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(a), genuine scalar continuation recurrence.
Use: identify the actual measured gradient/direction continuation with its true scalar two-term determinant transfer, without dividing by the polynomial variable.
Source: the proved actual continuation state, genuine nonzero measured line coefficient and elementary polynomial ring identities.
-/

namespace krylov.Envelope
noncomputable section
open Polynomial
variable {α β : ℕ → ℝ}

/-- The actual continuation polynomial satisfies exactly its true three-term scalar frozen recurrence.
Use: The actual continuation polynomial satisfies exactly its true three-term scalar frozen recurrence.
Article: main_krylov, prop:phi(a), genuine scalar continuation recurrence.
Proof: Eliminate the genuine direction response using only the true nonzero scalar line coefficient and the proved original polynomial state updates. -/
theorem phi_add_two (α β : ℕ → ℝ) (j k : ℕ) (ha : α (j+k)≠0) :
    phi α β j (k+2)=
      (1-C (α (j+k+1))*X+C (α (j+k+1)*β (j+k)/α (j+k)))*phi α β j (k+1)-
        C (α (j+k+1)*β (j+k)/α (j+k))*phi α β j k := by
  -- Eliminate the actual direction response through a genuine scalar reciprocal; no inverse of the polynomial variable is used.
  let μ := α (j+k+1)*β (j+k)/α (j+k)
  have hcoef : C μ*C (α (j+k))=C (α (j+k+1))*C (β (j+k)) := by
    rw [← C_mul,← C_mul]
    congr 1
    exact div_mul_cancel₀ _ ha
  have hp : C (α (j+k))*X*psi α β j k=phi α β j (k+1)-phi α β j k := by
    rw [phi_succ]
    ring
  rw [show k+2=(k+1)+1 by omega,phi_succ,psi_succ]
  rw [show j+(k+1)=j+k+1 by omega]
  calc
    _ = (1-C (α (j+k+1))*X)*phi α β j (k+1)+
        C μ*(C (α (j+k))*X*psi α β j k) := by
      linear_combination -(X*psi α β j k)*hcoef
    _ = _ := by
      rw [hp]
      ring

/-- The genuine first continuation polynomial is exactly the actual one-step residual.
Use: The genuine first continuation polynomial is exactly the actual one-step residual.
Article: main_krylov, prop:phi(a), genuine scalar continuation recurrence.
Proof: Use the true initial gradient and direction polynomial state. -/
theorem phi_one (α β : ℕ → ℝ) (j : ℕ) : phi α β j 1=1-C (α j)*X := by
  rw [show 1=0+1 from rfl,phi_succ,phi_zero,psi_zero]
  simp only [Nat.add_zero,mul_neg_one,sub_eq_add_neg]
end
end krylov.Envelope
