import krylov.Stability.AnalyticFC

/-!
Article: main_krylov, lem:U(a), local analytic quadratic remainder calculus.
Use: apply genuine power-series remainder bounds to actual algorithm outputs,
with their true Fréchet derivatives rather than assumed first-order coefficients.
Source: mathlib's HasFPowerSeriesAt.isBigO_sub_partialSum_pow and derivative identification.
-/

namespace krylov.Stability
noncomputable section
open Filter Topology Asymptotics
variable {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Every actual analytic vector function has a quadratic Taylor remainder with its genuine Fréchet derivative.
Use: derive pointwise local algorithm remainder estimates after proving actual trajectory analyticity.
Article: main_krylov, lem:U(a), k=2 local analytic case.
Source: mathlib's analytic power-series remainder theorem.
Proof: the actual degree-two partial sum is exactly the function value plus
its true linear derivative; identify those two actual series coefficients in the proved quadratic remainder bound. -/
theorem analytic_quadratic_remainder {f : X → F} {x : X} (hf : AnalyticAt ℝ f x) :
    (fun h => f (x+h)-f x-fderiv ℝ f x h)=O[𝓝 (0 : X)] (fun h => ‖h‖^2) := by
  -- The derivative coefficient is identified from the actual power series, not supplied as a separate expansion premise.
  obtain ⟨p,hp⟩ := hf
  have h := hp.isBigO_sub_partialSum_pow 2
  have he (v : X) : p.partialSum 2 v=f x+fderiv ℝ f x v := by
    rw [FormalMultilinearSeries.partialSum,show (2 : ℕ)=1+1 from rfl,Finset.sum_range_succ,Finset.sum_range_one,
      hp.coeff_zero,hp.fderiv_eq,continuousMultilinearCurryFin1_apply]
    rfl
  apply h.congr_left
  intro v
  rw [he]
  abel

end
end krylov.Stability
