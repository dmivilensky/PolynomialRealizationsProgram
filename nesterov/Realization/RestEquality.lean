import nesterov.Realization.RestQuadratic

/-! Corollary `cor:rest`: equality of the literal rest and free-state factors,
with a single genuine finite-dimensional objective attaining the factor. -/
noncomputable section
open Filter Set
open scoped Topology BigOperators NNReal
namespace nesterov.Realization
open Spectral

theorem restRate_eq_momentumRate_of_quadratic (q : Momentum.Tuning) {μ L : ℝ}
    (hμ : 0<μ) (hμL : μ<L)
    (hT : Closure.T (Momentum.method q.beta q.tau q.stepSize q.step_pos.ne') μ L=
      Real.log (Rates.quadraticRate (Momentum.method q.beta q.tau q.stepSize q.step_pos.ne') μ L)) :
    Momentum.momentumRestRate q.beta q.tau q.stepSize q.step_pos.ne' μ L=
      Momentum.momentumRate q.beta q.tau q.stepSize q.step_pos.ne' μ L := by
  apply le_antisymm (Momentum.restRate_le_momentumRate q.step_pos.ne' hμ hμL)
  have hrate := Closure.rate_eq_exp_T
    (Momentum.method q.beta q.tau q.stepSize q.step_pos.ne') hμ hμL
  rw [hT,Real.exp_log (Rates.quadraticRate_pos _ hμ hμL),
    Momentum.quadraticRate_method] at hrate
  change _≤Momentum.momentumRestRate _ _ _ _ _ _
  rw [show Momentum.momentumRate q.beta q.tau q.stepSize q.step_pos.ne' μ L=
    Quadratic.quadraticRate μ L q.beta q.tau q.stepSize from hrate]
  exact Momentum.quadraticRate_le_momentumRestRate q.step_pos hμ hμL

/-- At the quadratic endpoint one fixed quadratic on the actual real line,
initialized at 1, attains the whole nonlinear factor from rest. -/
theorem exists_quadratic_worst_from_rest (q : Momentum.Tuning) {μ L : ℝ}
    (hμ : 0<μ) (hμL : μ<L)
    (hT : Closure.T (Momentum.method q.beta q.tau q.stepSize q.step_pos.ne') μ L=
      Real.log (Rates.quadraticRate (Momentum.method q.beta q.tau q.stepSize q.step_pos.ne') μ L)) :
    ∃ lam∈Icc μ L,polyak.CenteredSmoothStronglyConvex μ L (fun x : ℝ=>lam/2*‖x‖^2) ∧
      limsup (fun n : ℕ=>‖Momentum.iterate (gradient (fun x : ℝ=>lam/2*‖x‖^2))
        q.beta q.tau q.stepSize 1 n‖^((n:ℝ)⁻¹)) atTop=
          Momentum.momentumRate q.beta q.tau q.stepSize q.step_pos.ne' μ L := by
  obtain ⟨lam,hlam,hf,he⟩ := Momentum.exists_real_quadratic_rest_attainment
    (β:=q.beta) (τ:=q.tau) q.step_pos hμ hμL
  refine ⟨lam,hlam,hf,?_⟩
  rw [he]
  have hh := Closure.rate_eq_exp_T
    (Momentum.method q.beta q.tau q.stepSize q.step_pos.ne') hμ hμL
  rw [hT,Real.exp_log (Rates.quadraticRate_pos _ hμ hμL),
    Momentum.quadraticRate_method] at hh
  exact hh.symm

/-- Above the quadratic boundary, one fixed finite-dimensional real objective
and one fixed from-rest initialization attain the nonlinear factor. -/
theorem exists_worst_from_rest_above_quadratic (q : Momentum.Tuning) {μ L : ℝ}
    (hμ : 0<μ) (hμL : μ<L) (hs : q.Stable μ L)
    (ht : Closure.T (Momentum.method q.beta q.tau q.stepSize q.step_pos.ne') μ L≠0)
    (htq : Real.log (Rates.quadraticRate (Momentum.method q.beta q.tau q.stepSize q.step_pos.ne') μ L)<
      Closure.T (Momentum.method q.beta q.tau q.stepSize q.step_pos.ne') μ L) :
    Momentum.momentumRestRate q.beta q.tau q.stepSize q.step_pos.ne' μ L=
      Momentum.momentumRate q.beta q.tau q.stepSize q.step_pos.ne' μ L ∧
    ∃ d : ℕ,0<d ∧ ∃ (f : EuclideanSpace ℝ (Fin d)→ℝ) (x₀ : EuclideanSpace ℝ (Fin d)),
      polyak.CenteredSmoothStronglyConvex μ L f ∧ x₀≠0 ∧
      (∃ c₀ : ℝ,0<c₀ ∧ ∀ n : ℕ,c₀*Real.exp ((n:ℝ)*
        Closure.T (Momentum.method q.beta q.tau q.stepSize q.step_pos.ne') μ L)*‖x₀‖≤
          ‖Momentum.iterate (gradient f) q.beta q.tau q.stepSize x₀ n‖) ∧
      limsup (fun n : ℕ=>‖Momentum.iterate (gradient f) q.beta q.tau q.stepSize x₀ n‖^
        ((n:ℝ)⁻¹)) atTop=Momentum.momentumRate q.beta q.tau q.stepSize q.step_pos.ne' μ L := by
  classical
  let M := Momentum.method q.beta q.tau q.stepSize q.step_pos.ne'
  let t := Closure.T M μ L
  obtain ⟨ν,C,hfeas⟩ := Closure.T_mem M hμ hμL
  obtain ⟨F,hF,_,hcarrier⟩ := Attainment.exists_finite_boundary_carrier M hμ hμL ht htq
  let : Fintype F := hF.fintype
  obtain ⟨w,hw,he⟩ := polyak.Spectral.exists_finiteSpectrum_of_support ν (hcarrier ν C hfeas)
  have hstrict := Attainment.optimal_strict_minimizer M hμ hμL ht htq hfeas
  rw [←he] at hfeas hstrict
  have hrest : Real.exp t≤Momentum.momentumRestRate q.beta q.tau q.stepSize q.step_pos.ne' μ L :=
    exp_le_momentumRestRate_of_feasible q hμ hμL hs w (fun j=>j.val) hw hfeas (fun _=>hstrict)
  have heq : Momentum.momentumRestRate q.beta q.tau q.stepSize q.step_pos.ne' μ L=
      Momentum.momentumRate q.beta q.tau q.stepSize q.step_pos.ne' μ L := by
    apply le_antisymm (Momentum.restRate_le_momentumRate q.step_pos.ne' hμ hμL)
    exact (Closure.rate_eq_exp_T M hμ hμL).le.trans hrest
  obtain ⟨lam,_,Y,f,_,hf,_,hx,_,c₀,hc₀,hbound⟩ :=
    exists_real_startup q hμ hμL hs w (fun j=>j.val) hw hfeas (fun _=>hstrict)
  let x₀ := startupCoordinates F (physical (finiteLatent w (fun j=>j.val) t)
    q.beta q.tau q.stepSize lam Y 0)
  refine ⟨heq,2*Fintype.card F+1,by omega,f,x₀,hf,hx,⟨c₀,hc₀,hbound⟩,?_⟩
  apply le_antisymm
  · exact (Momentum.iterate_root_limsup_le_restRate q.step_pos.ne' hf hx).trans_eq heq
  · rw [show Momentum.momentumRate q.beta q.tau q.stepSize q.step_pos.ne' μ L=
      Real.exp t from Closure.rate_eq_exp_T M hμ hμL]
    apply Rates.exp_le_root_limsup_of_lower_bound (mul_pos hc₀ (norm_pos_iff.mpr hx)) _
      (Momentum.iterate_roots_bounded q.step_pos.ne' hf hx)
    intro n
    calc
      _ = c₀*Real.exp ((n:ℝ)*t)*‖x₀‖ := by ring
      _ ≤ _ := hbound n

theorem restRate_eq_momentumRate_above_quadratic (q : Momentum.Tuning) {μ L : ℝ}
    (hμ : 0<μ) (hμL : μ<L) (hs : q.Stable μ L)
    (ht : Closure.T (Momentum.method q.beta q.tau q.stepSize q.step_pos.ne') μ L≠0)
    (htq : Real.log (Rates.quadraticRate (Momentum.method q.beta q.tau q.stepSize q.step_pos.ne') μ L)<
      Closure.T (Momentum.method q.beta q.tau q.stepSize q.step_pos.ne') μ L) :
    Momentum.momentumRestRate q.beta q.tau q.stepSize q.step_pos.ne' μ L=
      Momentum.momentumRate q.beta q.tau q.stepSize q.step_pos.ne' μ L :=
  (exists_worst_from_rest_above_quadratic q hμ hμL hs ht htq).1
end nesterov.Realization
