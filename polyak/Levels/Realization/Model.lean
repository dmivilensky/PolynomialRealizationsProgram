import polyak.Realization.Actual
import polyak.Waves.Dynamics
import polyak.Waves.Interpolation

/-! Article: exact threshold criterion, Appendix E, the arbitrary-spectrum startup.
The continuous spectral measure is realized in its actual real L² space
plus one decaying scalar coordinate. One amplitude and one potential
interpolate the whole infinite table, including the corrected initial node. -/

namespace polyak.Levels.Realization
noncomputable section
open Interpolation Waves Spectral Dynamics Filter
open scoped Topology

theorem exists_continuous_startup_model {μ L α β : ℝ} (hμ : 0<μ) (hμL : μ<L) (hα : 0<α)
    (hβ : 0≤β) (hβ1 : β<1) (hquad : α*L<2*(1+β)) (ν : Spectrum)
    (h : MixtureFeasible ν (multiplierMap (normalizedA μ L α β)
      (normalizedB μ L α) β 0) 0 0) :
    ∃ τ Y : ℝ,∃ ψ : WithLp 2 (WaveSpace ν×ℝ)→ℝ,
      |τ|<1 ∧ 0<Y ∧ NormalizedSmooth ψ ∧
      Tendsto (polyak.Realization.response
        (normalizedA μ L α β+normalizedB μ L α*τ) β) atTop (𝓝 0) ∧
      ∀ N : ℕ,iterate (gradient (denormalizeFunction μ L ψ)) α β
        (polyak.Realization.startupPosition (mixturePosition ν 0)
          (normalizedA μ L α β) (normalizedB μ L α) β τ Y (some 0)) N=
        polyak.Realization.startupPosition (mixturePosition ν 0)
          (normalizedA μ L α β) (normalizedB μ L α) β τ Y (some N) := by
  let A:=normalizedA μ L α β
  let B:=normalizedB μ L α
  let m:=multiplierMap A B β 0
  let x:=mixturePosition ν 0
  let σ:=mixtureGradient ν m 0
  let v:=mixtureValue ν m 0 0
  have hB : 0<B := by dsimp [B,normalizedB]; positivity
  have hx : x none=0 := by
    change lift ν (positionMap 0 none)=0
    have he : positionMap 0 none=0 := by ext; rfl
    rw [he,map_zero]
  have hσ : σ none=0 := by
    change lift ν (gradientMap m 0 none)=0
    have he : gradientMap m 0 none=0 := by ext; simp [gradientMap,positionMap,position]
    rw [he,map_zero]
  have hv : v none=0 := by simp [v]
  have hcontrol : ∀ k : ℕ,‖x (some k)‖≤1 := by
    intro k
    simp only [x,norm_mixturePosition,mul_zero,Real.exp_zero,le_refl]
  obtain ⟨τ,Y,ψ,hτ,hY,hψ,hlim,hdata⟩:=polyak.Realization.exists_startup_potential
    hB hβ hβ1 (normalizedA_abs_add_B_lt hμ hα hquad) x σ v
    ((mixture_tableFeasible_iff ν m 0 0).mpr h) hx hσ hv (Or.inl hcontrol)
    (polyak.Realization.initialGradient x A B β)
  refine ⟨τ,Y,ψ,hτ,hY,hψ,hlim,fun N=>?_⟩
  exact polyak.Realization.startup_iterate x σ hψ hB.ne'
    (fun i=>(hdata i).2) (mixture_recurrence ν A B β 0 hB.ne') N

end
end polyak.Levels.Realization
