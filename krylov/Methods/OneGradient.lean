import krylov.Methods.QuadraticCycles

/-!
Article: main_krylov, def:classes(M₁), alg:xrfc and lem:consistent(b).
Use: distinguish evaluated steps from a genuinely unevaluated final output,
and implement the actual data-only step-basis XRFC policy.
Source: the source article's one-gradient virtual-launch protocol.
-/

namespace krylov.Methods
noncomputable section
open Matrix krylov.Reference
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A policy with one actual evaluated step per iteration and a data-only unevaluated output.
Use: the unknown output operator is absent from both decision functions.
Article: main_krylov, def:classes(M₁). -/
structure OneGradientMethod (E : Type*) where
  /-- Choose the next evaluated displacement solely from already observed data. -/
  step : History E → E
  /-- Choose the final unevaluated displacement solely from already observed data. -/
  output : History E → E

/-- Execute one genuinely evaluated one-gradient step.
Use: the only new operator action is the prescribed actual step query; auxiliary probed-record slots are zero.
Article: main_krylov, def:classes(M₁), g_(k+1)=g_k+A_ks_k. -/
def oneGradientAdvance (m : OneGradientMethod E) (A : E →L[ℝ] E) (H : History E) : History E :=
  let s := m.step H
  ⟨H.initial, ⟨0,0,s,H.gradient+A s,[]⟩::H.records⟩

/-- The actual evaluated run of a data-only one-gradient policy.
Use: final outputs do not appear as evaluated records or future observations.
Article: main_krylov, def:classes(M₁), D_N. -/
def oneGradientRun (m : OneGradientMethod E) (A : ℕ → E →L[ℝ] E) (g : E) : ℕ → History E
  | 0 => ⟨g,[]⟩
  | k+1 => oneGradientAdvance m (A k) (oneGradientRun m A g k)

/-- The actual physical displacement of the final unevaluated output.
Use: the output point includes its virtual displacement without spending another gradient.
Article: main_krylov, def:classes(M₁), x̂_N−x₀. -/
def OneGradientMethod.outputDisplacement (m : OneGradientMethod E) (H : History E) : E :=
  H.displacement+m.output H

/-- The semantic gradient at the unevaluated output under its actual output operator.
Use: this quantity is for analysis only and is never an input to the policy.
Article: main_krylov, def:classes(M₁), g_N+Bu_N. -/
def OneGradientMethod.outputGradient (m : OneGradientMethod E) (B : E →L[ℝ] E) (H : History E) : E :=
  H.gradient+B (m.output H)

/-- The actual M₁ CG-consistency condition concerns the unevaluated physical output.
Use: a trial point need not coincide with the true reference iterate.
Article: main_krylov, def:classes(M₁), x̂_k=x_k⁰. -/
def OneGradientConsistent (m : OneGradientMethod E) : Prop :=
  ∀ (Q : E →L[ℝ] E), Q.toLinearMap.IsSymmetric →
    (∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) → ∀ g k,
      m.outputDisplacement (oneGradientRun m (fun _ => Q) g k)=CG.displacement Q g k

/-- Every actual one-gradient iteration contributes exactly one evaluated record.
Use: its cost is N+1 gradients, including the initial gradient and excluding the final output.
Article: main_krylov, def:classes, one-gradient observation cost.
Proof: induction on the genuinely evaluated execution recursion. -/
theorem oneGradientRun_length (m : OneGradientMethod E) (A : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    (oneGradientRun m A g k).records.length=k := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg Nat.succ ih

/-- The actual number of observed gradients in a one-gradient run, including its initial observation.
Use: the output displacement causes no extra oracle call.
Article: main_krylov, def:classes, N+1 gradients. -/
def oneGradientCost (H : History E) : ℕ := 1+H.records.length

/-- The actual evaluated one-gradient run costs exactly N+1 gradients.
Use: the stated cost follows from its real query transcript.
Article: main_krylov, def:classes, M₁ observation count.
Proof: the actual transcript length counts exactly the evaluated updates. -/
theorem oneGradientCost_run (m : OneGradientMethod E) (A : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    oneGradientCost (oneGradientRun m A g k)=k+1 := by
  rw [oneGradientCost, oneGradientRun_length, Nat.add_comm]

/-- The actual stored-window virtual model coefficients.
Use: XRFC forms its correction entirely from the stored observed step/secant data.
Article: main_krylov, alg:xrfc, w=−T̄⁻¹Sᵀg. -/
def virtualCoefficients (W : List (E × E)) (g : E) : Fin W.length → ℝ :=
  modelCoefficients (windowSteps W) (windowModel W) g

/-- The actual virtual displacement from the current evaluated point.
Use: this is XRFC's unevaluated final output displacement as well as its next virtual launch.
Article: main_krylov, alg:xrfc, Sw. -/
def virtualCorrection (W : List (E × E)) (g : E) : E := combine (windowSteps W) (virtualCoefficients W g)

/-- The virtual gradient extrapolated from actual observed secants.
Use: its evaluation spends no unknown operator action.
Article: main_krylov, alg:xrfc, ĝ=g+Yw. -/
def virtualGradient (W : List (E × E)) (g : E) : E := g+combine (windowImages W) (virtualCoefficients W g)

/-- The actual step-basis XRFC policy, with a data-only trial-step rule.
Use: all virtual solves and the final unevaluated output use the actual selected window.
Article: main_krylov, alg:xrfc, s=Sw+τd and output x+Sw. -/
def xrfcMethod (memory : ℕ → ℕ) (trial : History E → ℝ) : OneGradientMethod E where
  step H :=
    let W := selectedWindow memory H
    virtualCorrection W H.gradient+trial H • windowDirection W (virtualGradient W H.gradient)
  output H := virtualCorrection (selectedWindow memory H) H.gradient

/-- An actual static one-gradient history records the true quadratic gradient of its actual physical iterate.
Use: the semantic output gradient is the true gradient at the unevaluated physical output.
Article: main_krylov, def:classes(M₁), quadratic interpretation.
Proof: induct over actual evaluated updates and telescope the actual physical displacements. -/
theorem oneGradientRun_quadratic_gradient (m : OneGradientMethod E) (Q : E →L[ℝ] E) (g : E) (k : ℕ) :
    let H := oneGradientRun m (fun _ => Q) g k
    H.gradient=g+Q H.displacement := by
  -- Each real query adds Qs to the observed gradient and s to the actual accumulated displacement.
  induction k with
  | zero => simp only [oneGradientRun, History.gradient, History.displacement, List.map_nil, List.sum_nil, map_zero, add_zero]
  | succ k ih =>
    change (oneGradientRun m (fun _ => Q) g k).gradient+Q (m.step _)=
      g+Q (m.step (oneGradientRun m (fun _ => Q) g k)+(oneGradientRun m (fun _ => Q) g k).displacement)
    rw [ih, map_add]
    abel

end
end krylov.Methods
