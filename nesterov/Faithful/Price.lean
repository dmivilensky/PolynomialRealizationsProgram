import nesterov.Faithful.Upper
import nesterov.Faithful.Necessary
import nesterov.Trace.Endpoint
import nesterov.Slow.Consequences

/-! Article Corollary 5.7: the price of a faithful lead. -/
namespace nesterov.Faithful
noncomputable section
open Filter Set Polynomial
open scoped Topology
variable {θ y : ℝ} (F : Slow.SecondOrderFamily θ y)

def traceData : Trace.DoubleRootData :=
  ⟨F.method 0,F.q0,y,F.step_pos,F.initial_factor,F.q0_one⟩

theorem traceData_symbol (ω : ℝ) : (traceData F).symbol ω=limitSymbol (F.u 0) F.q0 ω := by
  unfold Trace.DoubleRootData.symbol
  simp_rw [Trace.DoubleRootData.eval_phi]
  simp only [star_neg,mul_neg,neg_mul,neg_neg]
  change ((1-circle ω)*(F.method 0).characteristic 0 (circle ω)*
    star ((F.method 0).characteristic 1 (circle ω))).re=limitSymbol (F.u 0) F.q0 ω
  rw [mul_assoc,←limitProduct_characteristic (F.method 0) F.q0 F.initial_factor]
  rfl

/-- Continuous root persistence turns eventual quadratic stability into the
closed-disk pencil hypothesis of the trace theorem. -/
theorem closed_limit_pencil
    (hs : ∀ᶠ ε in 𝓝[>] (0:ℝ),Rates.quadraticRate (F.method ε) (ε^2) 1≤1) :
    (traceData F).ClosedPencil 0 := by
  intro lam hlam z hz
  by_contra h
  have hnorm : 1<‖z‖ := lt_of_not_ge h
  have hroot : (F.method 0).characteristic lam z=0 := by
    rw [Trace.DoubleRootData.eval_phi] at hz
    exact neg_eq_zero.mp hz
  obtain ⟨r,hr,he⟩ := F.fixed_unstable_root_lower hlam hroot hnorm
  obtain ⟨ε,hε⟩ := (he.and hs).exists
  obtain ⟨_,_,_,hq⟩ := hε.1
  exact not_lt_of_ge hε.2 (hr.trans hq)

/-- A nonnegative limit symbol costs step y≤2, and equality determines
exactly the TMM transfer function, even with common independent modes. -/
theorem step_bound_rigid
    (hs : ∀ᶠ ε in 𝓝[>] (0:ℝ),Rates.quadraticRate (F.method ε) (ε^2) 1≤1)
    (hS : ∀ ω∈Ioo (0:ℝ) Real.pi,0≤limitSymbol (F.u 0) F.q0 ω) :
    y≤2 ∧ (y=2 ↔ (F.u 0)=(C 1-C 3*X)*F.q0) := by
  exact (traceData F).trace_bound_rigid (by norm_num) (by norm_num) (closed_limit_pencil F hs)
    (fun ω hω=>by rw [traceData_symbol];exact hS ω hω)

/-- Both literal rate ceilings in corollary (i). -/
theorem faithful_price_ceilings
    (hs : ∀ᶠ ε in 𝓝[>] (0:ℝ),Rates.quadraticRate (F.method ε) (ε^2) 1≤1)
    (hS : ∀ ω∈Ioo (0:ℝ) Real.pi,0≤limitSymbol (F.u 0) F.q0 ω) :
    y≤2 ∧ limsup (fun ε=>(F.coefficient ε:EReal)) (𝓝[>] (0:ℝ))≤1 ∧
      limsup (fun ε=>(F.quadraticCoefficient ε:EReal)) (𝓝[>] (0:ℝ))≤(Real.sqrt 2:EReal) := by
  have hy := (step_bound_rigid F hs hS).1
  have hsqrt : Real.sqrt (y/2)≤1 := by
    rw [Real.sqrt_le_one]
    linarith
  refine ⟨hy,F.nonlinear_optimal_ceiling.trans (by exact_mod_cast hsqrt),?_⟩
  exact F.quadratic_limsup_coefficient_le.trans (EReal.coe_le_coe_iff.mpr
    ((Flow.cQ_le_sqrt F.theta_pos F.step_pos).trans (Real.sqrt_le_sqrt hy)))

/-- Constant at least one forces θ=3, y=2 and the exact TMM transfer. -/
theorem optimal_transfer_rigidity
    (hs : ∀ᶠ ε in 𝓝[>] (0:ℝ),Rates.quadraticRate (F.method ε) (ε^2) 1≤1)
    (hS : ∀ ω∈Ioo (0:ℝ) Real.pi,0≤limitSymbol (F.u 0) F.q0 ω)
    (hlim : (1:EReal)≤liminf (fun ε=>(F.coefficient ε:EReal)) (𝓝[>] (0:ℝ))) :
    θ=3 ∧ y=2 ∧ (F.u 0)=(C 1-C 3*X)*F.q0 ∧
      effectiveLead (F.u 0) F.q0 y=1/2 ∧ ∀ ω : ℝ,limitSymbol (F.u 0) F.q0 ω=0 := by
  obtain ⟨hθ,hyθ,_,hy⟩ := F.necessary_slow_data hlim
  have hbound := step_bound_rigid F hs hS
  have hy2 : y=2 := le_antisymm hbound.1 hy
  have hθ3 : θ=3 := by linarith
  have ht := hbound.2.mp hy2
  have hlead := (traceData F).tmmTransfer_effectiveLead ht
  refine ⟨hθ3,hy2,ht,hlead,fun ω=>?_⟩
  rw [←traceData_symbol]
  exact (traceData F).tmmTransfer_zero_symbol ht ω

/-- Strict positivity excludes equality in the trace bound. -/
theorem strict_faithful_step
    (hc : F.CoeffCk 1)
    (hs : ∀ z : ℂ,(F.middlePolynomial 0).eval z=0 → ‖z‖<1)
    (hS : ∀ ω∈Ioc (0:ℝ) Real.pi,0<limitSymbol (F.u 0) F.q0 ω) :
    y<2 ∧ Flow.cF θ y≤Real.sqrt (y/2) ∧ Real.sqrt (y/2)<1 := by
  have hr := faithful_rate_linear F hc hs hS (c:=0) (Flow.cF_pos F.theta_pos F.step_pos)
  have hsmall : ∀ᶠ ε in 𝓝[>] (0:ℝ),ε<1 :=
    (eventually_lt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds
  have hq : ∀ᶠ ε in 𝓝[>] (0:ℝ),Rates.quadraticRate (F.method ε) (ε^2) 1≤1 := by
    filter_upwards [hr,hsmall,self_mem_nhdsWithin] with ε he hε1 hε
    change 0<ε at hε
    exact (Rates.quadraticRate_le_rate _ (sq_pos_of_pos hε) (by nlinarith)).trans (by simpa using he.le)
  have hb := step_bound_rigid F hq (fun ω hω=>(hS ω ⟨hω.1,hω.2.le⟩).le)
  have hne : y≠2 := by
    intro hy
    have hz := (traceData F).tmmTransfer_zero_symbol (hb.2.mp hy) (Real.pi/2)
    rw [traceData_symbol] at hz
    have hp := hS (Real.pi/2) ⟨by positivity,by linarith [Real.pi_pos]⟩
    linarith
  refine ⟨lt_of_le_of_ne hb.1 hne,Flow.cF_le_optimal F.step_pos,?_⟩
  have hy := lt_of_le_of_ne hb.1 hne
  have hy0 := F.step_pos
  nlinarith [Real.sq_sqrt (by positivity : 0≤y/2),Real.sqrt_nonneg (y/2)]

end
end nesterov.Faithful
