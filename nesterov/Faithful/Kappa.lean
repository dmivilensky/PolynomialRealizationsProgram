import nesterov.Faithful.Price
import nesterov.Faithful.LeadingOrder
import nesterov.Slow.Kappa

/-! Literal condition-number versions of faithful discretization and its price. -/
namespace nesterov.Faithful
noncomputable section
open Filter Set Polynomial
open scoped Topology
variable {θ y : ℝ} (F : Slow.SecondOrderFamily θ y)

theorem faithful_kappa_tendsto (hc : F.CoeffCk 1)
    (hs : ∀ z : ℂ,(F.middlePolynomial 0).eval z=0 → ‖z‖<1)
    (hS : ∀ ω∈Ioc (0:ℝ) Real.pi,0<limitSymbol (F.u 0) F.q0 ω) :
    Tendsto F.kappaCoefficient atTop (𝓝 (Flow.cF θ y)) := by
  have ht := (faithful_coefficient_tendsto F hc hs hS).comp Slow.epsilon_tendsto
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with κ hκ
  exact (F.kappa_coefficient_eq hκ).symm

/-- Faithful(a) with the exact original C^{2p} and u₀−2v₀ hypotheses. -/
theorem faithful_source {p : ℕ} (hp : 2≤p) (hc : F.CoeffCk (2*p))
    (hs : ∀ z : ℂ,evalComplex (F.u 0-C 2*F.v 0) z=0 → ‖z‖<1)
    (hS : ∀ ω∈Ioc (0:ℝ) Real.pi,0<limitSymbol (F.u 0) F.q0 ω) :
    Tendsto F.kappaCoefficient atTop (𝓝 (Flow.cF θ y)) ∧
      ∀ c : ℝ,c<Flow.cF θ y → ∀ᶠ ε in 𝓝[>] (0:ℝ),
        Rates.rate (F.method ε) (ε^2) 1<1-c*ε := by
  have hc1 := coeffCk_one_of_twice F (by omega : 1≤p) hc
  have hmid := source_middle_stability F hs
  exact ⟨faithful_kappa_tendsto F hc1 hmid hS,fun _ hcF=>faithful_rate_linear F hc1 hmid hS hcF⟩

theorem faithful_price_kappa_ceilings
    (hs : ∀ᶠ ε in 𝓝[>] (0:ℝ),Rates.quadraticRate (F.method ε) (ε^2) 1≤1)
    (hS : ∀ ω∈Ioo (0:ℝ) Real.pi,0≤limitSymbol (F.u 0) F.q0 ω) :
    y≤2 ∧ limsup (fun κ=>(F.kappaCoefficient κ:EReal)) atTop≤1 ∧
      limsup (fun κ=>(F.kappaQuadraticCoefficient κ:EReal)) atTop≤(Real.sqrt 2:EReal) := by
  rw [F.kappa_limsup_eq,F.kappa_quadratic_limsup_eq]
  exact faithful_price_ceilings F hs hS

theorem optimal_kappa_transfer_rigidity
    (hs : ∀ᶠ ε in 𝓝[>] (0:ℝ),Rates.quadraticRate (F.method ε) (ε^2) 1≤1)
    (hS : ∀ ω∈Ioo (0:ℝ) Real.pi,0≤limitSymbol (F.u 0) F.q0 ω)
    (hlim : (1:EReal)≤liminf (fun κ=>(F.kappaCoefficient κ:EReal)) atTop) :
    θ=3 ∧ y=2 ∧ (F.u 0)=(C 1-C 3*X)*F.q0 ∧
      effectiveLead (F.u 0) F.q0 y=1/2 ∧ ∀ ω : ℝ,limitSymbol (F.u 0) F.q0 ω=0 := by
  rw [F.kappa_liminf_eq] at hlim
  exact optimal_transfer_rigidity F hs hS hlim

theorem negative_lead_kappa_liminf (hlead : effectiveLead (F.u 0) F.q0 y<0) :
    (1:EReal)<liminf (fun κ=>(Rates.quadraticRate (F.method (Slow.epsilon κ)) (1/κ) 1:EReal)) atTop := by
  have heq : liminf (fun κ=>(Rates.quadraticRate (F.method (Slow.epsilon κ)) (1/κ) 1:EReal)) atTop=
      liminf (fun ε=>(Rates.quadraticRate (F.method ε) (ε^2) 1:EReal)) (𝓝[>] (0:ℝ)) := by
    rw [←Slow.epsilon_liminf]
    apply liminf_congr
    filter_upwards [eventually_gt_atTop (0:ℝ)] with κ hκ
    rw [Slow.epsilon_sq hκ.le]
  rw [heq]
  exact negative_lead_liminf F hlead

end
end nesterov.Faithful
