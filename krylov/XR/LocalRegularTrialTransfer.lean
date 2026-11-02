import krylov.XR.LocalPrescribedTrial

/-!
Article: main_krylov, lem:xr-local, regular-trial transfer of expansions.
Use: derive the required first-order trial drift from genuine differentiability
of the primitive trial vector, then apply the actual joint-output C² theorem.
No output expansion or trial-difference estimate is assumed. Consequently
all fixed-trial first responses and second-order remainder estimates transfer
to a regular varying trial vector through this proved quadratic difference.
-/
namespace krylov.XR
noncomputable section
open Filter Topology Asymptotics krylov.Reference
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Genuine C-one regularity of a trial vector gives the native prescribed
XRFC comparison with the fixed reference trials to second order. -/
theorem prescribedXRFC_regular_trial_transfer (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v, v ≠ 0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hpre : ∀ i < N, CG.gradient Q g i ≠ 0)
    (tau₀ : Fin N → ℝ) (htau : ∀ i, tau₀ i ≠ 0)
    (tau : (Fin (N+1) → E →L[ℝ] E) → Fin N → ℝ)
    (hregular : DifferentiableAt ℝ tau 0) (hreference : tau 0 = tau₀) :
    (fun e => prescribedXRFCOutput Q g N (e, tau e) - prescribedXRFCOutput Q g N (e, tau₀))
      =O[𝓝 0] (fun e : Fin (N+1) → E →L[ℝ] E => ‖e‖^2) := by
  have hdiff : (fun e => tau e - tau₀) =O[𝓝 0]
      (fun e : Fin (N+1) → E →L[ℝ] E => ‖e‖) := by
    simpa only [hreference, sub_zero] using hregular.isBigO_sub.norm_right
  have ht : Tendsto tau (𝓝 0) (𝓝 tau₀) := by
    rw [←hreference]
    exact hregular.continuousAt
  exact prescribedXRFC_trial_comparison Q hQ hpos g N hpre tau₀ htau
    (fun _ => tau₀) tau tendsto_const_nhds ht hdiff

end
end krylov.XR
