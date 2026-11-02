import bezout.Comparisons.Competitors.Stages
import bezout.Comparisons.Competitors.Propagation
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Ring

/-!
Article: bezout, Equation `eq:competitor-masg` and comparison protocol p=1.
Use: literal M-ASG parameters, prescribed stage resets and exact budget stopping,
including horizons below the cited convergence theorem's budget condition.
Proof: the deterministic stage clock consumes each call exactly once; its live
coefficients instantiate the proved physical momentum/extrapolation execution.
-/

namespace bezout.Comparisons.Competitors.MASG
noncomputable section
open scoped BigOperators Matrix

/-- The objective's prescribed spectral condition number. -/
def conditionNumber (I : chebyshev1.SpectralInterval) : ℝ := I.L/I.mu

/-- The exact rounded block length from the cited p=1 configuration. -/
def blockLength (I : chebyshev1.SpectralInterval) : ℕ :=
  ⌈3*Real.sqrt (conditionNumber I)*Real.log 2⌉₊

/-- The rounded block length is strictly positive. -/
theorem blockLength_pos (I : chebyshev1.SpectralInterval) : 0<blockLength I := by
  apply Nat.ceil_pos.mpr
  have hc : 0<conditionNumber I := div_pos (I.mu_pos.trans I.mu_lt_L) I.mu_pos
  exact mul_pos (mul_pos (by norm_num) (Real.sqrt_pos.mpr hc)) (Real.log_pos (by norm_num))

/-- The first stage uses 1/L; stage k>=2 uses the literal inverse 4^k L. -/
def stageAlpha (I : chebyshev1.SpectralInterval) (k : ℕ) : ℝ :=
  if k=1 then 1/I.L else (4^k*I.L)⁻¹

/-- The exact Nesterov momentum of each prescribed stage. -/
def stageBeta (I : chebyshev1.SpectralInterval) (k : ℕ) : ℝ :=
  (1-Real.sqrt (I.mu*stageAlpha I k))/(1+Real.sqrt (I.mu*stageAlpha I k))

/-- Every actual stage stepsize is strictly positive. -/
theorem stageAlpha_pos (I : chebyshev1.SpectralInterval) (k : ℕ) : 0<stageAlpha I k := by
  have hL : 0<I.L := I.mu_pos.trans I.mu_lt_L
  unfold stageAlpha
  split_ifs <;> positivity

/-- The prescribed momentum denominator is never zero. -/
theorem stageBeta_denominator_pos (I : chebyshev1.SpectralInterval) (k : ℕ) :
    0<1+Real.sqrt (I.mu*stageAlpha I k) := by positivity

/-- The literal finite-budget M-ASG momentum configuration. -/
def config (I : chebyshev1.SpectralInterval) (N : ℕ) : Momentum where
  alpha s := stageAlpha I (clock N (blockLength I) s).stage
  beta s := stageBeta I (clock N (blockLength I) s).stage
  extrapolated := true
  reset s := decide ((clock N (blockLength I) s).used=0)

/-- The exact finite-budget causal history, including its partial final stage. -/
def history (I : chebyshev1.SpectralInterval) (N : ℕ) : bezout.History N := (config I N).history N

/-- Every physical call selects a valid prescribed stage and used-call count. -/
theorem selected_stage_valid (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2≤N) (s : ℕ) :
    1≤(clock N (blockLength I) s).stage ∧
      (clock N (blockLength I) s).used<stageLength N (blockLength I) (clock N (blockLength I) s).stage :=
  clock_valid N (blockLength I) hN (blockLength_pos I) s

/-- The first floor(N/2) calls use the prescribed alpha_1=1/L. -/
theorem first_stage_alpha (I : chebyshev1.SpectralInterval) (N s : ℕ) (hs : s<N/2) :
    (config I N).alpha s=1/I.L := by
  simp [config,clock_first_stage N (blockLength I) s hs,stageAlpha]

/-- Within the first stage there is exactly its initial prescribed reset. -/
theorem first_stage_reset (I : chebyshev1.SpectralInterval) (N s : ℕ) (hs : s<N/2) :
    (config I N).reset s=decide (s=0) := by
  simp [config,clock_first_stage N (blockLength I) s hs]

/-- Later stages use exactly n_k=2^k B calls before any budget truncation. -/
theorem later_stage_length (I : chebyshev1.SpectralInterval) (N k : ℕ) (hk : 2≤k) :
    stageLength N (blockLength I) k=2^k*blockLength I := by simp [stageLength,show k≠1 by omega]

/-- The last actual call lies in a complete or partial prescribed stage, and
its total consumed budget is exactly N. No corollary budget hypothesis is used. -/
theorem truncated_last_stage (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2≤N) :
    (clock N (blockLength I) (N-1)).used+1≤
      stageLength N (blockLength I) (clock N (blockLength I) (N-1)).stage ∧
    completedLength N (blockLength I) (clock N (blockLength I) (N-1)).stage+
      ((clock N (blockLength I) (N-1)).used+1)=N :=
  last_stage_budget N (blockLength I) hN (blockLength_pos I)

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- At a stage start the previous state is reset before the physical query. -/
theorem query_at_reset (I : chebyshev1.SpectralInterval) (N s : ℕ) (x p : E)
    (hs : (clock N (blockLength I) s).used=0) : (config I N).query s x p=x := by
  simp only [Momentum.query,Momentum.previous,config,hs,decide_true,ite_true]
  module

/-- M-ASG makes exactly the original N fresh oracle calls, even inside its last stage. -/
theorem oracle_calls (I : chebyshev1.SpectralInterval) (N : ℕ)
    (oracle : Fin N → E → E) (initial : E) :
    (((config I N).program N).run oracle initial).calls=N := Momentum.oracle_calls _ _ _ _

/-- The literal scheduled program agrees with its actual history for every oracle stream. -/
theorem output_eq_history (I : chebyshev1.SpectralInterval) (N : ℕ)
    (oracle : Fin N → E → E) (initial : E) :
    ((config I N).program N).output oracle initial = (history I N).oracleOutput initial oracle :=
  Momentum.output_eq_history _ _ _ _

/-- The actual response includes every later scheduled reset, including a partial stage. -/
theorem response_eval (I : chebyshev1.SpectralInterval) (N : ℕ) (s : Fin N) (lam : ℝ) :
    ((history I N).response s).eval lam =
      -(config I N).alpha s.val *
        (chebyshev1.orderedProduct (fun i => (config I N).matrix (s.val+1+i) lam)
          (N-(s.val+1)) *ᵥ ![1,0]) 0 := Momentum.response_eval _ _ _ _

end
end bezout.Comparisons.Competitors.MASG
