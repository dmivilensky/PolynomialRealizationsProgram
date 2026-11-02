import bezout.Channel.Roots.Actual

/-!
Article: bezout, the LF/fractal competitor in Appendix D.
Use: the literal recursively interlaced root schedule is executed by the actual
zero-momentum oracle program; all physical-response and root-order identities
therefore refer to its execution, including its exact Chebyshev terminal.
Proof: the natural-index schedule is exactly the finite root-step extension.
-/

namespace bezout.Comparisons.Competitors.LF
noncomputable section
open bezout.Channel.Roots

/-- Literal interlaced LF steps, with unused natural indices extended by zero. -/
def config (I : chebyshev1.SpectralInterval) (k : ℕ) : Momentum :=
  Stepsize.config (schedule I (2^k) (dyadicPermutation k))

/-- Actual N=2^k-call LF causal history. -/
def history (I : chebyshev1.SpectralInterval) (k : ℕ) : bezout.History (2^k) :=
  (config I k).history (2^k)

/-- Every active coefficient is the printed reciprocal cosine-root step. -/
theorem coefficients (I : chebyshev1.SpectralInterval) (k : ℕ) (s : Fin (2^k)) :
    (config I k).alpha s.val=1/((I.L+I.mu)/2-I.delta/2*
      Real.cos (angle (2^k) (dyadicPermutation k s))) ∧ (config I k).beta s.val=0 := by
  simp [config,Stepsize.config,schedule,s.isLt,steps,node]

/-- The literal LF program is the actual root history used in Proposition D.1. -/
theorem history_eq_roots (I : chebyshev1.SpectralInterval) (k : ℕ) :
    history I k=lfHistory I k := rfl

/-- The actual LF finite terminal is exactly the normalized Chebyshev terminal. -/
theorem terminal (I : chebyshev1.SpectralInterval) (k : ℕ) :
    (history I k).terminal=I.residual (2^k) := lfHistory_exact I k

/-- Complete all-oracle-stream equivalence for the actual LF configuration. -/
theorem output_eq_history {E : Type*} [AddCommGroup E] [Module ℝ E]
    (I : chebyshev1.SpectralInterval) (k : ℕ) (oracle : Fin (2^k) → E → E) (initial : E) :
    ((config I k).program (2^k)).output oracle initial=(history I k).oracleOutput initial oracle :=
  Momentum.output_eq_history _ _ _ _

/-- The LF implementation consumes exactly its declared dyadic call budget. -/
theorem oracle_calls {E : Type*} [AddCommGroup E] [Module ℝ E]
    (I : chebyshev1.SpectralInterval) (k : ℕ) (oracle : Fin (2^k) → E → E) (initial : E) :
    (((config I k).program (2^k)).run oracle initial).calls=2^k := Momentum.oracle_calls _ _ _ _

end
end bezout.Comparisons.Competitors.LF
