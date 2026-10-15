import «2610.05164v2».Filters.Causality

/-!
Article: 2610.05164v2, Proposition 8.
Literal polynomial drift b(Y)m-d(Y) of equation (23).
Use: `«2610.05164v2».Filters.state_limits` feeds `«2610.05164v2».Residual.statePotential_null`
(state Potential null).
Proof chain: `«2610.05164v2».Residual.statePotential_null` — 2610.05164v2, Theorem 3.5; Pointwise
cubic-conjugate criterion, gauge invariance and regular price.
-/
namespace «2610.05164v2».Filters
noncomputable section
open Set MeasureTheory Real Filter «2610.05164v2».GroundState
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/--
Absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval (fun x => (f x,g
x)) a b`.

Use: `«2610.05164v2».Filters.state_locallyAC` uses this identity to establish absolute
continuity on the specified interval: `AbsolutelyContinuousOnInterval (state G) a b`.

Article: 2610.05164v2, Theorem 3.5 via `«2610.05164v2».Residual.statePotential_null`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem absolutelyContinuous_prod {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℝ → E} {g : ℝ → F} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hg : AbsolutelyContinuousOnInterval g a b) :
    AbsolutelyContinuousOnInterval (fun x => (f x,g x)) a b := by
  -- Expand/rewrite the named definitions and identities appearing in the tactic block; the
  -- remaining goal is a direct simplification or algebraic consequence.
  have h1 := (ContinuousLinearMap.inl ℝ E F).lipschitzWith.comp_absolutelyContinuousOnInterval hf
  have h2 := (ContinuousLinearMap.inr ℝ E F).lipschitzWith.comp_absolutelyContinuousOnInterval hg
  apply (h1.add h2).congr
  intro x _
  simp

/--
Definition 5's actual state, at the printed scales 32 and 64.

Use: `«2610.05164v2».Filters.state_polynomial_drift` rewrites with this definition to establish
the identity stated in that declaration.

Article: 2610.05164v2, Theorem 3.5 via `«2610.05164v2».Residual.statePotential_null`.
-/
def state {m : ℝ → ℝ} {hm : Integrable m} {hn : ∀ t, 0 ≤ m t}
    (G : GroundWitness hm hn) (x : ℝ) : ℝ × ℝ × ℝ × ℝ :=
  (G.q x,nonlinear 32 m x/32,nonlinear 64 m x/64,defect G x)

/--
Defines `stateDerivative` of type `ℝ × ℝ × ℝ × ℝ` by `(groundParameter hm hn*m x-G.q x*(2-G.q
x), (32*m x-2*nonlinear 32 m x-(nonlinear 32 m x)^2)/32, (64*m x-2*nonlinear 64 m x-(nonlinear
64 m x)^2)/64, (G.q x)^2-2*defect G x)`.

Use: `«2610.05164v2».Filters.state_polynomial_drift` rewrites with this definition to establish
the identity stated in that declaration.

Article: 2610.05164v2, Theorem 3.5 via `«2610.05164v2».Residual.statePotential_null`.
-/
def stateDerivative {m : ℝ → ℝ} {hm : Integrable m} {hn : ∀ t, 0 ≤ m t}
    (G : GroundWitness hm hn) (x : ℝ) : ℝ × ℝ × ℝ × ℝ :=
  (groundParameter hm hn*m x-G.q x*(2-G.q x),
    (32*m x-2*nonlinear 32 m x-(nonlinear 32 m x)^2)/32,
    (64*m x-2*nonlinear 64 m x-(nonlinear 64 m x)^2)/64,
    (G.q x)^2-2*defect G x)

variable {m : ℝ → ℝ} {hm : Integrable m} {hn : ∀ t, 0 ≤ m t} (G : GroundWitness hm hn)

/--
Absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval (state G) a b`.

Use: `«2610.05164v2».Residual.statePotential_locallyAC` uses this assertion to establish
absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval (fun x => Ψ
(state G x)) a b`.

Article: 2610.05164v2, Theorem 3.5 via `«2610.05164v2».Residual.statePotential_null`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.nonlinear_locallyAC`,
`«2610.05164v2».Filters.absolutelyContinuous_prod`,
`«2610.05164v2».GroundState.GroundWitness.coordinate_locallyAC` with the arguments shown in the
proof.
-/
theorem state_locallyAC (a b : ℝ) : AbsolutelyContinuousOnInterval (state G) a b := by
  -- Use the identities/estimates `«2610.05164v2».Filters.nonlinear_locallyAC`,
  -- `«2610.05164v2».Filters.absolutelyContinuous_prod`,
  -- `«2610.05164v2».GroundState.GroundWitness.coordinate_locallyAC` with the arguments shown
  -- in the proof.
  have h0 : AbsolutelyContinuousOnInterval (fun x => nonlinear 32 m x/32) a b := by
    apply ((nonlinear_locallyAC hm hn (by norm_num : (0:ℝ) ≤ 32) a b).const_mul (1/32:ℝ)).congr
    intro x _
    change (1/32:ℝ)*nonlinear 32 m x=nonlinear 32 m x/32
    ring
  have h1 : AbsolutelyContinuousOnInterval (fun x => nonlinear 64 m x/64) a b := by
    apply ((nonlinear_locallyAC hm hn (by norm_num : (0:ℝ) ≤ 64) a b).const_mul (1/64:ℝ)).congr
    intro x _
    change (1/64:ℝ)*nonlinear 64 m x=nonlinear 64 m x/64
    ring
  exact absolutelyContinuous_prod (G.coordinate_locallyAC a b)
    (absolutelyContinuous_prod h0 (absolutelyContinuous_prod h1 (defect_locallyAC G a b)))

/--
Establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, HasDerivAt (state G)
(stateDerivative G x) x`.

Use: `«2610.05164v2».Residual.statePotential_derivative` uses this assertion to establish
establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, HasDerivAt (fun x => Ψ
(state G x)) (fderiv ℝ Ψ (state G x) (stateDerivative G x)) x`.

Article: 2610.05164v2, Theorem 3.5 via `«2610.05164v2».Residual.statePotential_null`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem state_derivative : ∀ᵐ x, HasDerivAt (state G) (stateDerivative G x) x := by
  filter_upwards [G.coordinate_derivative,nonlinear_derivative hm hn (by norm_num : (0:ℝ) ≤ 32),
    nonlinear_derivative hm hn (by norm_num : (0:ℝ) ≤ 64),defect_derivative_ae G] with x hq h0 h1 hh
  exact hq.prodMk ((h0.div_const 32).prodMk ((h1.div_const 64).prodMk hh))

/--
Integrability of the displayed function: `Integrable (stateDerivative G)`.

Use: `«2610.05164v2».Residual.statePotential_derivative_integrable` uses this integrability
result to establish integrability of the displayed function: `Integrable (fun x => fderiv ℝ Ψ
(state G x) (stateDerivative G x))`.

Article: 2610.05164v2, Theorem 3.5 via `«2610.05164v2».Residual.statePotential_null`.

Proof: Use the identities/estimates
`«2610.05164v2».GroundState.GroundWitness.coordinate_integrability`,
`«2610.05164v2».Filters.nonlinear_derivative_integrable`,
`«2610.05164v2».Filters.defect_derivative_integrable` with the arguments shown in the proof.
-/
theorem state_derivative_integrable : Integrable (stateDerivative G) :=
  G.coordinate_integrability.2.prodMk
    (((nonlinear_derivative_integrable hm hn (by norm_num : (0:ℝ) ≤ 32)).div_const 32).prodMk
      (((nonlinear_derivative_integrable hm hn (by norm_num : (0:ℝ) ≤ 64)).div_const 64).prodMk
        (defect_derivative_integrable hm hn G)))

/--
Literal polynomial drift b(Y)m-d(Y) of equation (23).

The precise assertion is `stateDerivative G x= (groundParameter hm hn*m x-(state G
x).1*(2-(state G x).1), m x-2*(state G x).2.1-32*((state G x).2.1)^2, m x-2*(state G
x).2.2.1-64*((state G x).2.2.1)^2, ((state G x).1)^2-2*(state G x).2.2.2)`.

Use: `«2610.05164v2».Residual.state_drift` rewrites with this identity to establish the precise
assertion is `stateDerivative G x= m x • inputVector (groundParameter hm hn)-driftVector (state
G x)`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem state_polynomial_drift (x : ℝ) : stateDerivative G x=
    (groundParameter hm hn*m x-(state G x).1*(2-(state G x).1),
      m x-2*(state G x).2.1-32*((state G x).2.1)^2,
      m x-2*(state G x).2.2.1-64*((state G x).2.2.1)^2,
      ((state G x).1)^2-2*(state G x).2.2.2) := by
  -- Rewrite the definitions and library identities explicitly named in the proof, then
  -- discharge the resulting algebraic or order relation.
  simp only [state,stateDerivative,Prod.mk.injEq]
  constructor
  · trivial
  constructor
  · ring
  constructor
  · ring
  · trivial

/--
Convergence along the specified source filter to the specified limit: `Tendsto (state G) atBot
(𝓝 (0,0,0,0)) ∧ Tendsto (state G) atTop (𝓝 (2,0,0,2))`.

Use: `«2610.05164v2».Residual.statePotential_null` uses this limit to establish the identity
`(∫ x, fderiv ℝ Ψ (state G x) (stateDerivative G x))=0`.

Article: 2610.05164v2, Theorem 3.5 via `«2610.05164v2».Residual.statePotential_null`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.nonlinear_limits`,
`«2610.05164v2».GroundState.GroundWitness.coordinate_limits`,
`«2610.05164v2».Filters.defect_limits` with the arguments shown in the proof.
-/
theorem state_limits : Tendsto (state G) atBot (𝓝 (0,0,0,0)) ∧
    Tendsto (state G) atTop (𝓝 (2,0,0,2)) := by
  -- Use the identities/estimates `«2610.05164v2».Filters.nonlinear_limits`,
  -- `«2610.05164v2».GroundState.GroundWitness.coordinate_limits`,
  -- `«2610.05164v2».Filters.defect_limits` with the arguments shown in the proof.
  have h0 := nonlinear_limits hm hn (s := 32) (by norm_num)
  have h1 := nonlinear_limits hm hn (s := 64) (by norm_num)
  constructor
  · have h := G.coordinate_limits.1.prodMk_nhds ((h0.1.div_const 32).prodMk_nhds
      ((h1.1.div_const 64).prodMk_nhds (defect_limits G).1))
    change Tendsto (fun x => (G.q x,nonlinear 32 m x/32,nonlinear 64 m x/64,defect G x)) _ _
    simpa only [zero_div] using h
  · have h := G.coordinate_limits.2.prodMk_nhds ((h0.2.div_const 32).prodMk_nhds
      ((h1.2.div_const 64).prodMk_nhds (defect_limits G).2))
    change Tendsto (fun x => (G.q x,nonlinear 32 m x/32,nonlinear 64 m x/64,defect G x)) _ _
    simpa only [zero_div] using h

end
end «2610.05164v2».Filters
