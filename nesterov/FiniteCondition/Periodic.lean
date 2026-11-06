import nesterov.FiniteCondition.Counterexample

/-! The actual dimension-three periodic trajectory promised by tonguefree(b). -/
namespace nesterov.FiniteCondition
noncomputable section
open Spectral Set Filter
open scoped NNReal Topology

def HasThreePeriodicOrbit (q : Momentum.Tuning) (μ L : ℝ) : Prop :=
  ∃ f : EuclideanSpace ℝ (Fin 3)→ℝ,polyak.CenteredSmoothStronglyConvex μ L f ∧
    ∃ x₀,x₀≠0 ∧ ∃ c₀ : ℝ,0<c₀ ∧
      ∃ P : EuclideanSpace ℂ (Fin 1)→ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3),
        (∀ n : ℕ,c₀*‖x₀‖≤‖Momentum.iterate (gradient f) q.beta q.tau q.stepSize x₀ n‖) ∧
        Function.Periodic (fun n : ℕ=>P (Spectral.finiteLatent (fun _ : Fin 1=>(1:ℝ≥0))
          (fun _=>Phase.frequency (2*Real.pi/3)) 0 (n+1))) 3 ∧
        Tendsto (fun n : ℕ=>Momentum.iterate (gradient f) q.beta q.tau q.stepSize x₀ n-
          P (Spectral.finiteLatent (fun _ : Fin 1=>(1:ℝ≥0))
            (fun _=>Phase.frequency (2*Real.pi/3)) 0 (n+1))) atTop (𝓝 0)

theorem three_periodic_witness {β τ : ℝ} (hβ : 0≤β) (hβ1 : β<1) (hτ : 0≤τ)
    (ht : τ<tauThree β) :
    ∃ (q : Momentum.Tuning) (μ L : ℝ),q.beta=β ∧ q.tau=τ ∧ q.stepSize=1 ∧
      0<μ ∧ μ<L ∧ q.Stable μ L ∧ Phase.momentumAngle q μ L (2*Real.pi/3)<Real.pi/3 ∧
        HasThreePeriodicOrbit q μ L ∧
          1<Momentum.momentumRestRate q.beta q.tau q.stepSize q.step_pos.ne' μ L := by
  obtain ⟨q,μ,L,hb,htau,hh,hμ,hL,hs,hphase,hr⟩ := three_tongue_witness hβ hβ1 hτ ht
  refine ⟨q,μ,L,hb,htau,hh,hμ,hL,hs,hphase,?_,hr⟩
  have hp := Phase.exists_periodic_startup q hμ hL hs (j:=1) (K:=3) le_rfl le_rfl
    (by norm_num) (by simp) (by simpa only [Nat.cast_one,mul_one,Nat.cast_ofNat] using hphase.le)
  simpa only [HasThreePeriodicOrbit,Nat.cast_one,mul_one,Nat.cast_ofNat] using hp

end
end nesterov.FiniteCondition
