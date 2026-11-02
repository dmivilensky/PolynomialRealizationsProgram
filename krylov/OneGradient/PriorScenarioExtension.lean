import krylov.OneGradient.SpectralUniformMinimax
import krylov.OneGradient.RelativeUniformMinimax
set_option autoImplicit false
/-!
Article: main_krylov, cor:quant(c), genuine enlargement of scenario classes.
Use: embed the original constant-prefix physical adversaries in arbitrary
larger classes of actual operator sequences, preserving their true errors.
Source: actual one-gradient execution recursion and the already proved exact
physical spectral and central relative-ball arbitrary-method lower bounds.
The accompanying compact varying-prefix upper expansions are the original
xrfc_step_compact_expansion and xrfc_direction_compact_expansion, under their
primitive C2 trial hypotheses; no endpoint rule is presumed globally smooth.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Reference krylov.Methods krylov.Secant
variable {m : ℕ}

/-- The actual constant-prefix scenario with a separate unobserved output
operator after the original final evaluated query.
Use: inject physical minimax adversaries into larger genuine sequence classes.
Article: main_krylov, cor:quant(c). -/
def constantOutputScenario (N : ℕ) (A B : Matrix (Fin m) (Fin m) ℝ) : ℕ → Matrix (Fin m) (Fin m) ℝ :=
  fun k => if k<N+1 then A else B

/-- Original normalized output error on any genuine physical operator
sequence, with the actual base metric and true last reference CG denominator.
Use: enlarged scenario classes retain the executed one-gradient semantics.
Article: main_krylov, cor:quant(c). -/
def oneGradientScenarioError (A : Matrix (Fin m) (Fin m) ℝ) (g : EuclideanSpace ℝ (Fin m))
    (N : ℕ) (method : OneGradientMethod (EuclideanSpace ℝ (Fin m)))
    (operators : ℕ → Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  ‖cgOperator (metricRoot A)⁻¹ (method.outputGradient (cgOperator (operators (N+1)))
    (oneGradientRun method (fun k => cgOperator (operators k)) g (N+1)))‖/‖cgCanonicalError A g N‖

/-- The genuine executor sees precisely the original constant operator on
every actual evaluated prefix of the injected physical scenario.
Use: no unobserved output matrix enters any prior decision or gradient.
Article: main_krylov, cor:quant(c).
Proof: induct over the original executed recursion, retaining the true query
boundary that excludes the final output operator from evaluated steps. -/
theorem one_gradient_constant_scenario_run (A B : Matrix (Fin m) (Fin m) ℝ)
    (g : EuclideanSpace ℝ (Fin m)) (N : ℕ) (method : OneGradientMethod (EuclideanSpace ℝ (Fin m)))
    (k : ℕ) (hk : k≤N+1) :
    oneGradientRun method (fun j => cgOperator (constantOutputScenario N A B j)) g k=
      oneGradientRun method (fun _ => cgOperator A) g k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [oneGradientRun,oneGradientRun,ih (by omega)]
    simp only [constantOutputScenario,ite_eq_left (show k<N+1 by omega)]

/-- Injecting a constant-prefix scenario preserves its true original
normalized physical error, including the actual unobserved output action.
Use: original lower bounds transfer to actual larger sequence classes.
Article: main_krylov, cor:quant(c).
Proof: the original evaluated transcript is identical and the output-time
operator is exactly the supplied physical output matrix. -/
theorem one_gradient_constant_scenario_error (A B : Matrix (Fin m) (Fin m) ℝ)
    (g : EuclideanSpace ℝ (Fin m)) (N : ℕ) (method : OneGradientMethod (EuclideanSpace ℝ (Fin m))) :
    oneGradientScenarioError A g N method (constantOutputScenario N A B)=
      ‖cgOperator (metricRoot A)⁻¹ (method.outputGradient (cgOperator B)
        (oneGradientRun method (fun _ => cgOperator A) g (N+1)))‖/‖cgCanonicalError A g N‖ := by
  have hout : constantOutputScenario N A B (N+1)=B := by simp only [constantOutputScenario,lt_self_iff_false,ite_false]
  rw [oneGradientScenarioError,hout,one_gradient_constant_scenario_run A B g N method (N+1) le_rfl]

/-- The exact spectral one-gradient lower bound persists in every actual
scenario class containing the original constant-prefix physical adversaries.
Use: the larger class may permit arbitrary earlier variation; no smoothness
or CG consistency is imposed on its competing method.
Article: main_krylov, cor:quant(c), spectral lower-bound persistence.
Proof: each true original physical adversary is an actual member of the
larger sequence class and has exactly the same normalized executed error.
Restrict its uniform guarantee and apply the proved original sharp bound. -/
theorem spectral_prior_enlarged_scenario_lower (mu upper : ℝ) (hmu : 0 < mu) (hmuL : mu < upper)
    (n : ℕ) (method : OneGradientMethod (EuclideanSpace ℝ (Fin (n+2)))) (hm : OneGradientSpanRestricted method)
    {omega : ℝ} (homega : 0≤omega) (hsmall : omega≤1)
    (allowed : Matrix (Fin (n+2)) (Fin (n+2)) ℝ → EuclideanSpace ℝ (Fin (n+2)) →
      (ℕ → Matrix (Fin (n+2)) (Fin (n+2)) ℝ) → Prop)
    (hcontains : ∀ P : SpectralPriorReference n mu upper,∀ b : ℝ,
      (lanczosCompletion P.matrix P.positive P.gradient P.gradient_ne_zero P.full_support b-mu • 1).PosSemidef →
      (upper • 1-lanczosCompletion P.matrix P.positive P.gradient P.gradient_ne_zero P.full_support b).PosSemidef →
      ∀ B : Matrix (Fin (n+2)) (Fin (n+2)) ℝ,B.IsSymm →
        relativeBudget (lanczosCompletion P.matrix P.positive P.gradient P.gradient_ne_zero P.full_support b)
          (B-lanczosCompletion P.matrix P.positive P.gradient P.gradient_ne_zero P.full_support b)≤omega →
        let C := lanczosCompletion P.matrix P.positive P.gradient P.gradient_ne_zero P.full_support b
        allowed C P.gradient (constantOutputScenario (n+1) C B))
    (v : ℝ) (hbound : ∀ A g operators,allowed A g operators → oneGradientScenarioError A g (n+1) method operators≤v) :
    ((upper-mu)/(upper+mu))*omega≤v := by
  apply spectral_prior_method_uniform_lower mu upper hmu hmuL n method hm homega hsmall v
  intro P b hlo hhi B hB hbudget
  let C := lanczosCompletion P.matrix P.positive P.gradient P.gradient_ne_zero P.full_support b
  have he := hbound C P.gradient (constantOutputScenario (n+1) C B) (hcontains P b hlo hhi B hB hbudget)
  rw [one_gradient_constant_scenario_error] at he
  exact he

/-- The attained central relative-ball lower bound persists in every actual
larger scenario class containing its real physical endpoint scenarios.
Use: variation or additional scenarios cannot improve the original uniform
one-gradient lower bound; the unobserved physical output matrix is retained.
Article: main_krylov, cor:quant(c), relative-ball lower-bound persistence.
Proof: genuine constant-prefix embedding preserves the actual normalized
errors, and the original central-fibre arbitrary-method minimum applies. -/
theorem relative_prior_enlarged_scenario_lower {n : ℕ}
    (center : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hcenter : center.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues center hcenter.1 g).card=n+1)
    (method : OneGradientMethod (EuclideanSpace ℝ (Fin (n+1)))) (hm : OneGradientSpanRestricted method)
    {rho omega : ℝ} (hrho : 0≤rho) (hrhosmall : rho < 1) (homega : 0≤omega) (homegasmall : omega≤1)
    (allowed : Matrix (Fin (n+1)) (Fin (n+1)) ℝ → (ℕ → Matrix (Fin (n+1)) (Fin (n+1)) ℝ) → Prop)
    (hcontains : ∀ b : ℝ,relativeBudget center (lanczosCompletion center hcenter g hg hc b-center)≤rho →
      ∀ B : Matrix (Fin (n+1)) (Fin (n+1)) ℝ,B.IsSymm →
        relativeBudget (lanczosCompletion center hcenter g hg hc b) (B-lanczosCompletion center hcenter g hg hc b)≤omega →
        let C := lanczosCompletion center hcenter g hg hc b
        allowed C (constantOutputScenario n C B))
    (v : ℝ) (hbound : ∀ A operators,allowed A operators → oneGradientScenarioError A g n method operators≤v) :
    rho*omega≤v := by
  apply (central_fibre_exact_minimax center hcenter g hg hc hrho hrhosmall homega homegasmall).2
  refine ⟨method,hm,?_⟩
  intro b hb B hB hbudget
  let C := lanczosCompletion center hcenter g hg hc b
  have he := hbound C (constantOutputScenario n C B) (hcontains b hb B hB hbudget)
  rw [one_gradient_constant_scenario_error] at he
  exact he

end
end krylov.OneGradient
