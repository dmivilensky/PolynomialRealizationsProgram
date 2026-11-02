import krylov.Convergence.OrderNativeSharpC3
import krylov.Convergence.RestartedFCOrder
import krylov.Convergence.RestartedRFCOrder

/-!
Article: main_krylov, thm:D, sharp actual restarted inequalities.
Use: retain a uniform sharp one-cycle leading constant along the genuine
restart trajectory, including stationary tails. The scalar normalization is
the true canonical initial error, so no condition-number factor is lost.
Source: exact normalization of an actual iterate and the uniform cycle bound.
-/
namespace krylov.Convergence
noncomputable section
open Set Metric Filter Topology krylov.Methods krylov.Reference krylov.Functions
  krylov.Tensor krylov.Nonlinear krylov.Design krylov.Secant
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator

/-- A uniform actual canonical-unit cycle bound gives the same leading
constant along a convergent actual restarted trajectory. Stationarity,
rather than an arbitrary positive-error convention, handles zero tails. -/
theorem sharp_restarted_of_unit_cycle
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : E ≃L[ℝ] E) (cycle : E → E) (hzero : cycle 0=0)
    (admission : E → Prop) (p : ℕ) (hp : 0<p) (C : ℝ)
    (hcycle : ∀ η : ℝ,0<η →∃ ep : ℝ,0<ep ∧∀ ε : ℝ,0<ε →ε<ep →
      ∀ u,‖T u‖=1 →admission (ε • u) →‖T (cycle (ε • u))‖≤(C+η)*ε^p)
    (x : ℕ → E) (hx : ∀ c,x (c+1)=cycle (x c))
    (hadmit : ∀ᶠ c in atTop,0<‖T (x c)‖ →admission (x c))
    (hconv : Tendsto (fun c=>‖T (x c)‖) atTop (𝓝 0)) :
    ∀ η : ℝ,0<η →∀ᶠ c in atTop,‖T (x (c+1))‖≤(C+η)*‖T (x c)‖^p := by
  intro η hη
  obtain ⟨ep,hep,hbound⟩:=hcycle η hη
  filter_upwards [hconv.eventually (gt_mem_nhds hep),hadmit] with c hc hn
  by_cases he : 0<‖T (x c)‖
  · let ε:=‖T (x c)‖
    let u:=ε⁻¹ • x c
    have hunit : ‖T u‖=1 := by
      rw [show u=ε⁻¹ • x c from rfl,map_smul,norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr he.le)]
      exact inv_mul_cancel₀ he.ne'
    have hdecomp : ε • u=x c := by
      dsimp only [u]
      rw [smul_smul,mul_inv_cancel₀ he.ne',one_smul]
    have hh:=hbound ε he hc u hunit (by rw [hdecomp];exact hn he)
    rwa [hdecomp,←hx c] at hh
  · have he0 : ‖T (x c)‖=0 := le_antisymm (by linarith only [he]) (norm_nonneg _)
    have hx0 : x c=0 := T.injective (by simpa only [map_zero] using norm_eq_zero.mp he0)
    rw [hx c,hx0,hzero,map_zero,norm_zero]
    simp only [zero_pow hp.ne',mul_zero,le_refl]

end
end krylov.Convergence
