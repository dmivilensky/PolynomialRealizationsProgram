import nesterov.Momentum.Stationary
import nesterov.Stationary.Execution
import nesterov.Stationary.Euclidean
import nesterov.Rates.Rest
import polyak.Dynamics.Embedding
import polyak.Dynamics.Rate

/-!
Article: Definition `def:rate`, the heavy-ball specialization τ=0.
Use: exact equality with the existing Polyak package's original finite-dimensional
from-rest suprema and asymptotic factor, including translated minimizers.
-/
namespace nesterov.Momentum
noncomputable section
open Set

/-- An actual constant-memory rest trajectory has the source executor's iterates. -/
theorem fromRest_latest_eq_iterate {β τ h μ L : ℝ} (hh : h ≠ 0)
    (r : Rates.HilbertRun (method β τ h hh) μ L) (hr : r.FromRest) (n : ℕ) :
    r.w (n+1)=iterate (gradient r.f) β τ h (r.w 0) n := by
  have he : r.w=history (gradient r.f) β τ h (r.w 0) (r.w 0) := by
    apply StationaryMethod.IsTrajectory.unique (method β τ h hh) r.trajectory
      (history_isTrajectory _ β τ h hh _ _)
    intro j
    rw [hr j]
    fin_cases j <;> rfl
  exact congrFun he (n+1)

/-- At τ=0 the literal new ratio set is exactly Polyak's original Euclidean
ratio set over all positive dimensions, arbitrary minimizers and starts. -/
theorem restRatios_heavyBall (β h μ L : ℝ) (hh : h ≠ 0) (n : ℕ) :
    Rates.restRatios (method β 0 h hh) μ L n=polyak.Dynamics.allRatios μ L h β n := by
  ext x
  constructor
  · rintro ⟨r,hfd,hr,hz,hx⟩
    let _ : FiniteDimensional ℝ r.Carrier := hfd
    let J := Rates.HilbertRun.euclideanMap r
    let G := Rates.HilbertRun.euclideanObjective r
    have hG : polyak.CenteredSmoothStronglyConvex μ L G := r.euclideanObjective_admissible
    have hmin : ∀ y, G 0 ≤ G y :=
      (hG.toSmoothStronglyConvex.minimizer_iff 0).mpr hG.gradient_zero
    have hzJ : J (r.w 0) ≠ 0 := by
      intro he
      apply hz
      exact J.injective (he.trans J.map_zero.symm)
    have hgrad : ∀ y, gradient G (J y)=J (gradient r.f y) := r.gradient_euclideanObjective
    have hrun := polyak.Dynamics.iterate_embedding J (gradient r.f) (gradient G) hgrad h β (r.w 0) n
    refine ⟨Module.finrank ℝ r.Carrier+1,by omega,G,hG.toSmoothStronglyConvex,
      0,J (r.w 0),hmin,hzJ,?_⟩
    rw [sub_zero,sub_zero,hrun,J.norm_map,J.norm_map]
    rw [← iterate_heavyBall,← fromRest_latest_eq_iterate hh r hr n]
    change x=‖r.w (n+1)‖/‖r.w 0‖
    simpa only [method,show n+2-1=n+1 by omega] using hx
  · rintro ⟨d,_,f,hf,a,x₀,hmin,hne,hx⟩
    let g := polyak.centerObjective f a
    have hg : polyak.CenteredSmoothStronglyConvex μ L g := by
      refine ⟨hf.centerObjective a,?_,?_⟩
      · simp [g,polyak.centerObjective]
      · rw [(polyak.hasGradientAt_centerObjective hf.differentiable a 0).gradient]
        simpa using (hf.minimizer_iff a).mp hmin
    let r : Rates.HilbertRun (method β 0 h hh) μ L :=
      ⟨EuclideanSpace ℝ (Fin d),g,hg,history (gradient g) β 0 h (x₀-a) (x₀-a),
        history_isTrajectory _ β 0 h hh _ _⟩
    have hr : r.FromRest := by
      intro j
      fin_cases j <;> rfl
    have hz : r.w 0 ≠ 0 := sub_ne_zero.mpr hne
    have htranslate := polyak.Dynamics.iterate_translate (gradient f) (gradient g) a h β
      (fun e => (polyak.hasGradientAt_centerObjective hf.differentiable a e).gradient.symm)
      (x₀-a) n
    simp only [add_sub_cancel] at htranslate
    rw [htranslate,add_sub_cancel_left] at hx
    refine ⟨r,inferInstance,hr,hz,?_⟩
    change x=‖history (gradient g) β 0 h (x₀-a) (x₀-a) (n+2-1)‖/‖x₀-a‖
    rw [show n+2-1=n+1 by omega]
    change x=‖iterate (gradient g) β 0 h (x₀-a) n‖/‖x₀-a‖
    rw [iterate_heavyBall]
    exact hx

/-- The two packages' actual finite-horizon from-rest suprema agree exactly. -/
theorem restEnvelope_heavyBall (β h μ L : ℝ) (hh : h ≠ 0) (n : ℕ) :
    Rates.restEnvelope (method β 0 h hh) μ L n=polyak.Dynamics.worstAll μ L h β n := by
  unfold Rates.restEnvelope polyak.Dynamics.worstAll
  rw [restRatios_heavyBall]

/-- The reused Polyak asymptotic rate is exactly the new from-rest rate at τ=0. -/
theorem restRate_heavyBall (β h μ L : ℝ) (hh : h ≠ 0) :
    Rates.restRate (method β 0 h hh) μ L=polyak.Dynamics.rate μ L h β := by
  unfold Rates.restRate polyak.Dynamics.rate
  congr 1
  funext n
  rw [restEnvelope_heavyBall]

end
end nesterov.Momentum
