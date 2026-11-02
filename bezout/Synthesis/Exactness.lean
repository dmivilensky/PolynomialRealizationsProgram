import bezout.Synthesis.Theorem

/-!
Article: bezout, Section 2 and Theorem 2.1, the comparison class `C_N`.
Use: identifies the polynomial terminal constraint with the literal noiseless
oracle behavior on every scalar spectral point of the prescribed interval.
Testing the actual one-dimensional execution at initial error one is already
sufficient; terminal exactness then gives the prescribed output in every real
module and for every noiseless physical execution.
Proof: equality on a nondegenerate real interval is polynomial equality, and
the exact execution theorem evaluates the terminal polynomial in the Hessian.
-/

namespace bezout.History
noncomputable section
open Polynomial
variable {N : ℕ}

/-- Terminal polynomial exactness is equivalent to scalar exactness throughout the interval.
Use: the algebraic definition of `ChebyshevExact` is exactly the article's comparison class. -/
theorem chebyshevExact_iff_scalar_terminal (h : bezout.History N)
    (I : chebyshev1.SpectralInterval) :
    h.ChebyshevExact I ↔ ∀ lam ∈ Set.Icc I.mu I.L,
      h.terminal.eval lam = (I.residual N).eval lam := by
  constructor
  · intro he lam _
    exact congrArg (fun p : ℝ[X] => p.eval lam) he
  · intro he
    exact I.polynomial_eq he

/-- The actual one-dimensional Hessian, acting by multiplication by its spectral value.
Use: constructs the scalar oracle executions testing comparison-class membership. -/
def scalarOperator (lam : ℝ) : ℝ →ₗ[ℝ] ℝ :=
  algebraMap ℝ (Module.End ℝ ℝ) lam

/-- The scalar operator is literal scalar multiplication.
Use: its physical oracle is the quadratic gradient `lam*x`. -/
@[simp] theorem scalarOperator_apply (lam x : ℝ) : scalarOperator lam x = lam * x := by
  simp only [scalarOperator, Module.algebraMap_end_apply, smul_eq_mul]

/-- Polynomial action on a one-dimensional Hessian is ordinary polynomial evaluation.
Use: relates actual noiseless runs to the terminal evaluations in the comparison class. -/
theorem scalarOperator_polynomial_action (lam : ℝ) (p : ℝ[X]) (x : ℝ) :
    (aeval (scalarOperator lam) p) x = p.eval lam * x := by
  rw [scalarOperator, aeval_algebraMap_apply_eq_algebraMap_eval]
  simp only [Module.algebraMap_end_apply, smul_eq_mul]

/-- The actual noiseless scalar oracle run returns the polynomial terminal value.
Use: tests exactness using physical execution rather than a supplied transfer identity. -/
theorem noiseless_scalar_output (h : bezout.History N) (lam initial : ℝ) :
    (h.run (scalarOperator lam) initial (fun _ => 0)).output =
      h.terminal.eval lam * initial := by
  calc
    _ = (aeval (scalarOperator lam) h.terminal) initial :=
      h.nominal_output (scalarOperator lam) initial
        (h.run (scalarOperator lam) initial (fun _ => 0))
    _ = _ := scalarOperator_polynomial_action lam h.terminal initial

/-- Exact actual noiseless scalar runs at unit initial error characterize the whole class.
Use: closes the semantic equivalence between the literal oracle model and polynomial exactness. -/
theorem chebyshevExact_iff_noiseless_scalar_run (h : bezout.History N)
    (I : chebyshev1.SpectralInterval) :
    h.ChebyshevExact I ↔ ∀ lam ∈ Set.Icc I.mu I.L,
      (h.run (scalarOperator lam) 1 (fun _ => 0)).output = (I.residual N).eval lam := by
  rw [h.chebyshevExact_iff_scalar_terminal I]
  constructor
  · intro he lam hlam
    rw [h.noiseless_scalar_output, mul_one]
    exact he lam hlam
  · intro he lam hlam
    have hvalue := he lam hlam
    simpa only [h.noiseless_scalar_output, mul_one] using hvalue

/-- Every actual noiseless execution of a Chebyshev-exact history has the prescribed terminal.
Use: transfers scalar comparison-class membership to arbitrary-dimensional quadratic oracles. -/
theorem chebyshevExact_noiseless_output {E : Type*} [AddCommGroup E] [Module ℝ E]
    (h : bezout.History N) (I : chebyshev1.SpectralInterval) (he : h.ChebyshevExact I)
    (H : E →ₗ[ℝ] E) (initial : E) (u : h.Execution H initial (fun _ => 0)) :
    u.output = (aeval H (I.residual N)) initial := by
  rw [h.nominal_output H initial u, he]

end
end bezout.History
