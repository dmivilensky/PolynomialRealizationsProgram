import nesterov.Rates.Envelope
import polyak.Functions.Normalization

/-!
Article: §2 notation, §4 normalization, and Appendix A.
Use: the centered function convention preserves actual original trajectories
and the exact state ratios used by the uniform envelope.
-/
namespace nesterov
noncomputable section

namespace StationaryMethod
variable (M : nesterov.StationaryMethod)
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem IsTrajectory.centerObjective {f : E → ℝ} {w : ℕ → E}
    (hw : M.IsTrajectory (gradient f) w) (hf : Differentiable ℝ f) (a : E) :
    M.IsTrajectory (gradient (polyak.centerObjective f a)) (fun k => w k-a) := by
  have hc := hw.center M a
  have hg : gradient (polyak.centerObjective f a) = fun e => gradient f (a+e) := by
    funext e
    exact (polyak.hasGradientAt_centerObjective hf a e).gradient
  rwa [hg]

/-- Both the minimizer and the complete centered actual execution exist. -/
theorem exists_centered_trajectory {μ L : ℝ} {f : E → ℝ}
    (hf : polyak.SmoothStronglyConvex μ L f) {w : ℕ → E}
    (hw : M.IsTrajectory (gradient f) w) :
    ∃ a, (∀ y, f a≤f y) ∧
      polyak.CenteredSmoothStronglyConvex μ L (polyak.centerObjective f a) ∧
      M.IsTrajectory (gradient (polyak.centerObjective f a)) (fun k => w k-a) := by
  obtain ⟨a,ha,hcenter⟩ := hf.exists_centered
  exact ⟨a,ha,hcenter,hw.centerObjective M hf.differentiable a⟩

end StationaryMethod

namespace Rates
variable (M : nesterov.StationaryMethod)

/-- Original noncentered objectives and arbitrary restart times satisfy the
same literal all-Hilbert envelope; the denominator uses the actual minimizer. -/
theorem original_stateNorm_le_envelope {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {μ L : ℝ} {f : E → ℝ}
    (hf : polyak.SmoothStronglyConvex μ L f) (a : E) (ha : ∀ y,f a≤f y)
    {w : ℕ → E} (hw : M.IsTrajectory (gradient f) w) (k n : ℕ) :
    M.stateNorm (fun j => w j-a) (k+n) ≤
      envelope M μ L n*M.stateNorm (fun j => w j-a) k := by
  have hc : polyak.CenteredSmoothStronglyConvex μ L (polyak.centerObjective f a) := by
    refine ⟨hf.centerObjective a,by simp [polyak.centerObjective],?_⟩
    rw [(polyak.hasGradientAt_centerObjective hf.differentiable a 0).gradient]
    simpa using (hf.minimizer_iff a).mp ha
  exact actual_stateNorm_le_envelope M hc (hw.centerObjective M hf.differentiable a) k n

end Rates
end
end nesterov
