import nesterov.Faithful.FamilyPositive
import nesterov.Slow.MiddleStability
import nesterov.Slow.Ceiling

/-! Article Theorem 5.4(a): actual rates and the faithful coefficient limit. -/
namespace nesterov.Faithful
noncomputable section
open Polynomial Filter Set
open scoped Topology
variable {θ y : ℝ} (F : Slow.SecondOrderFamily θ y)

/-- The source polynomial u₀−2v₀ is exactly the middle characteristic
polynomial multiplied by −2, so the root hypothesis is literal. -/
theorem source_middle_stability
    (hs : ∀ z : ℂ,evalComplex (F.u 0-C 2*F.v 0) z=0 → ‖z‖<1) :
    ∀ z : ℂ,(F.middlePolynomial 0).eval z=0 → ‖z‖<1 := by
  intro z hz
  apply hs z
  rw [Slow.SecondOrderFamily.middlePolynomial,StationaryMethod.characteristicPolynomial_eq_source] at hz
  simp only [zero_pow (by decide : 2≠0),add_zero] at hz
  simp only [evalComplex,Polynomial.map_sub,Polynomial.map_mul,Polynomial.map_C,eval_sub,eval_mul,eval_C]
  simp only [eval_sub,eval_mul,eval_C] at hz
  have hhalf : (((1:ℝ)/2:ℝ):ℂ)=(1/2:ℂ) := by norm_num
  rw [hhalf] at hz
  change _-(2:ℂ)*_=0
  linear_combination -2*hz

/-- Strict positivity of the limit symbol and strict stability of the fast
middle modes give the true uniform rate bound. -/
theorem faithful_rate_exp (hc : F.CoeffCk 1)
    (hs : ∀ z : ℂ,(F.middlePolynomial 0).eval z=0 → ‖z‖<1)
    (hS : ∀ ω∈Ioc (0:ℝ) Real.pi,0<limitSymbol (F.u 0) F.q0 ω)
    {c : ℝ} (hc0 : 0<c) (hcF : c<Flow.cF θ y) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ),Rates.rate (F.method ε) (ε^2) 1<Real.exp (-c*ε) := by
  have hpos := family_symbol_eventually_positive F hc hc0 hcF hS
  have hmid := F.middleRadius_lt_exp hs c
  have hsmall : ∀ᶠ ε in 𝓝[>] (0:ℝ),ε<1 :=
    (eventually_lt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds
  filter_upwards [hpos,hmid,hsmall,self_mem_nhdsWithin] with ε hp hm he hε
  change 0<ε at hε
  apply rate_lt_of_lagOne (F.method ε) (sq_pos_of_pos hε) (by nlinarith)
    (by nlinarith : -c*ε≤0) hm
  intro z hz
  have hw : polyak.Waves.z (-c*ε) z.arg=z := by
    rw [←radial_circle_eq]
    change (Real.exp (-c*ε):ℂ)*Complex.exp ((z.arg:ℂ)*Complex.I)=z
    rw [←hz]
    exact Complex.norm_mul_exp_arg_mul_I z
  simpa only [familySymbol,hw] using hp z.arg

/-- The source's linear-radius formulation, including every real c<c_F. -/
theorem faithful_rate_linear (hc : F.CoeffCk 1)
    (hs : ∀ z : ℂ,(F.middlePolynomial 0).eval z=0 → ‖z‖<1)
    (hS : ∀ ω∈Ioc (0:ℝ) Real.pi,0<limitSymbol (F.u 0) F.q0 ω)
    {c : ℝ} (hcF : c<Flow.cF θ y) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ),Rates.rate (F.method ε) (ε^2) 1<1-c*ε := by
  obtain ⟨d,hd,hdF⟩ := exists_between (max_lt hcF (Flow.cF_pos F.theta_pos F.step_pos))
  have hcd : c<d := (le_max_left _ _).trans_lt hd
  have hd0 : 0<d := (le_max_right _ _).trans_lt hd
  have hrate := faithful_rate_exp F hc hs hS hd0 hdF
  have hexp := (Slow.SecondOrderFamily.exponential_coefficient_limit d).eventually
    (eventually_gt_nhds hcd)
  filter_upwards [hrate,hexp,self_mem_nhdsWithin] with ε hr he hε
  change 0<ε at hε
  have hh := (lt_div_iff₀ hε).mp he
  linarith

/-- Full faithful asymptotics of the actual nonlinear rate. -/
theorem faithful_coefficient_tendsto (hc : F.CoeffCk 1)
    (hs : ∀ z : ℂ,(F.middlePolynomial 0).eval z=0 → ‖z‖<1)
    (hS : ∀ ω∈Ioc (0:ℝ) Real.pi,0<limitSymbol (F.u 0) F.q0 ω) :
    Tendsto F.coefficient (𝓝[>] (0:ℝ)) (𝓝 (Flow.cF θ y)) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [faithful_rate_linear F hc hs hS ha,self_mem_nhdsWithin] with ε he hε
    change 0<ε at hε
    change a<(1-Rates.rate (F.method ε) (ε^2) 1)/ε
    exact (lt_div_iff₀ hε).mpr (by linarith)
  · intro a ha
    obtain ⟨b,hb,hba⟩ := exists_between ha
    filter_upwards [F.coefficient_eventually_le hb] with ε he
    exact he.trans_lt hba

/-- The article's C^{2p} hypothesis implies the C¹ regularity sufficient above. -/
theorem coeffCk_one_of_twice {p : ℕ} (hp : 1≤p) (hc : F.CoeffCk (2*p)) : F.CoeffCk 1 := by
  constructor <;> intro j
  · exact (hc.1 j).of_le (by exact_mod_cast (by omega : 1≤2*p))
  · exact (hc.2 j).of_le (by exact_mod_cast (by omega : 1≤2*p))

end
end nesterov.Faithful
