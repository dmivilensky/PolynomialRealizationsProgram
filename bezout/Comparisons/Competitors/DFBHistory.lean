import bezout.Comparisons.Competitors.DFB
import bezout.Comparisons.Competitors.AveragedHistory
import bezout.Probability.Covariance

/-!
Article: bezout, Equations `eq:competitor-dfb` and `eq:experiment-general-mse`.
Use: the literal accelerated running average has an actual causal history, with
its stated terminal and physical responses; vector and matrix covariance
predictions therefore describe the executed averaging algorithm itself.
Proof: the exact all-oracle affine-average bridge, scalar physical impulses,
and the general polynomial response and covariance trace theorem.
-/

namespace bezout.Comparisons.Competitors.DFB
noncomputable section
open chebyshev1 Polynomial MeasureTheory
open scoped BigOperators

/-- The physical history of the literal DFB running-average implementation. -/
def history (L : ℝ) (N : ℕ) : bezout.History N := (config L).averagedHistory N

/-- DFB's actual averaged output agrees with its causal history for arbitrary oracles. -/
theorem output_eq_history {E : Type*} [AddCommGroup E] [Module ℝ E]
    (L : ℝ) (N : ℕ) (oracle : Fin N → E → E) (initial : E) :
    output L N oracle initial=(history L N).oracleOutput initial oracle :=
  Momentum.averagedOutput_eq_history _ _ _ _

/-- The actual averaged terminal evaluates to the printed d_j average. -/
theorem terminal_eval (L lam : ℝ) (N : ℕ) :
    (history L N).terminal.eval lam=terminalValue L lam N := by
  have h := output_eq_history L N (Momentum.scalarOracle N lam (fun _ => 0)) (1:ℝ)
  rw [terminalValue_actual] at h
  change terminalValue L lam N=(history L N).oracleOutput 1
    (fun _ x => bezout.History.scalarOperator lam x+(0:ℝ)) at h
  rw [bezout.History.oracleOutput_linear,bezout.History.nominal_output,
    bezout.History.scalarOperator_polynomial_action,mul_one] at h
  exact h.symm

/-- The averaged history response is its actual one-physical-call impulse. -/
theorem response_eval_actual (L lam : ℝ) (N : ℕ) (s : Fin N) :
    ((history L N).response s).eval lam=responseValue L lam N s := by
  unfold responseValue
  rw [output_eq_history]
  change _=(history L N).oracleOutput 0
    (fun j x => bezout.History.scalarOperator lam x+(if j=s then 1 else 0))
  rw [bezout.History.oracleOutput_linear,bezout.Risk.scalar_output]
  simp only [mul_zero,zero_add,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

/-- The literal DFB average has exactly the stated finite physical error response. -/
theorem response_eval (L lam : ℝ) (hL : L≠0) (hlam : lam≠0) (N : ℕ) (s : Fin N) :
    ((history L N).response s).eval lam=-(1-d L lam (N-s.val))/(lam*((N:ℝ)+1)) := by
  rw [response_eval_actual,responseValue_eq L lam hL hlam]

/-- Exact physical insertion formula for arbitrary vector Hessians and error streams. -/
theorem physical_response {E : Type*} [AddCommGroup E] [Module ℝ E]
    (L : ℝ) (N : ℕ) (H : E →ₗ[ℝ] E) (initial : E) (noise : Fin N → E) :
    output L N (fun s y => H y+noise s) initial=
      (aeval H (history L N).terminal) initial+
        ∑ s, (aeval H ((history L N).response s)) (noise s) :=
  Momentum.averaged_physical_response _ _ _ _ _


/-- Exact common-covariance prediction for the literal matrix DFB average. -/
theorem integral_output_common_covariance {Ω J : Type*} [Fintype J] [DecidableEq J]
    {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {𝓕 : Filtration ℕ mΩ} {w : ℕ → Ω → EuclideanSpace ℝ J}
    (L : ℝ) (N : ℕ) (H : Matrix J J ℝ) (initial : EuclideanSpace ℝ J)
    (hw : bezout.Probability.MartingaleDifferences N 𝓕 w μ)
    (V : Matrix J J ℝ) (hV : ∀ s : Fin N, bezout.Probability.covarianceMatrix (w s.val) μ=V) :
    (∫ ω, ‖output L N (fun s y => bezout.History.matrixEnd H y+w s.val ω) initial‖^2 ∂μ)=
      ‖(aeval (bezout.History.matrixEnd H) (history L N).terminal) initial‖^2+
        ∑ s : Fin N, Matrix.trace
          (aeval H ((history L N).response s)*V*(aeval H ((history L N).response s)).transpose) := by
  have he (ω : Ω) : output L N (fun s y => bezout.History.matrixEnd H y+w s.val ω) initial=
      (history L N).stochasticOutput (bezout.History.matrixEnd H) initial w ω := by
    rw [output_eq_history,bezout.History.oracleOutput_linear]
    rfl
  simp_rw [he]
  exact bezout.History.integral_stochasticOutput_common_covariance _ H initial hw V hV

end
end bezout.Comparisons.Competitors.DFB
