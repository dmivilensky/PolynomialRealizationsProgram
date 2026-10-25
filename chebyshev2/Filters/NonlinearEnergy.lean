import chebyshev2.Filters.NonlinearMass

/-!
Article: chebyshev2, Proposition 8.
Proposition 3(ii)'s derivative bound for any uniform bound B on the filter.
Use: `chebyshev2.Filters.defect_derivative_integrable` feeds
`chebyshev2.Filters.state_derivative_integrable` (state derivative integrable).
Proof chain: `chebyshev2.Residual.statePotential_null` — chebyshev2, Theorem 3.5; Pointwise
cubic-conjugate criterion, gauge invariance and regular price.
-/
namespace chebyshev2.Filters
noncomputable section
open Set MeasureTheory Real Filter chebyshev2.GroundState
set_option backward.isDefEq.respectTransparency false

variable {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t) {s : ℝ} (hs : 0 ≤ s)
include hm hn hs

/--
The stated quantitative bound `nonlinear s m x ≤ s*(∫ t, m t)`.

Use: `chebyshev2.Filters.nonlinear_square_integrable` uses this bound to establish
integrability of the displayed function: `Integrable (fun x => (nonlinear s m x)^2)`.

Article: chebyshev2, Theorem 3.5 via `chebyshev2.Residual.statePotential_null`.

Proof: Use the identities/estimates `chebyshev2.Filters.nonlinear_bounds`,
`chebyshev2.Filters.causal_le_mass` with the arguments shown in the proof.
-/
theorem nonlinear_uniform_bound (x : ℝ) : nonlinear s m x ≤ s*(∫ t, m t) :=
  (nonlinear_bounds hm hn hs x).2.trans (mul_le_mul_of_nonneg_left
    (causal_le_mass (by norm_num : (0:ℝ) ≤ 2) hm (Eventually.of_forall hn) x) hs)

/--
Integrability of the displayed function: `Integrable (fun x => (nonlinear s m x)^2)`.

Use: `chebyshev2.Filters.nonlinear_derivative_integrable` uses this integrability result to
establish integrability of the displayed function: `Integrable (fun x => s*m x-2*nonlinear s m
x-(nonlinear s m x)^2)`.

Article: chebyshev2, Theorem 3.5 via `chebyshev2.Residual.statePotential_null`.

Proof: Use the identities/estimates `chebyshev2.Filters.nonlinear_integrable`,
`chebyshev2.Filters.nonlinear_continuous`, `chebyshev2.Filters.nonlinear_bounds` with
the arguments shown in the proof.
-/
theorem nonlinear_square_integrable : Integrable (fun x => (nonlinear s m x)^2) := by
  -- Use the identities/estimates `chebyshev2.Filters.nonlinear_integrable`,
  -- `chebyshev2.Filters.nonlinear_continuous`, `chebyshev2.Filters.nonlinear_bounds`
  -- with the arguments shown in the proof.
  apply ((nonlinear_integrable hm hn hs).norm.mul_const (s*(∫ t, m t))).mono'
  · exact (nonlinear_continuous hm hn hs).pow 2 |>.aestronglyMeasurable
  · exact Eventually.of_forall (fun x => by
      change ‖(nonlinear s m x)^2‖ ≤ ‖nonlinear s m x‖*(s*(∫ t, m t))
      have h0 := (nonlinear_bounds hm hn hs x).1
      have h1 := nonlinear_uniform_bound hm hn hs x
      simp only [Real.norm_eq_abs,abs_of_nonneg h0,abs_of_nonneg (sq_nonneg (nonlinear s m x))]
      nlinarith)

/--
Integrability of the displayed function: `Integrable (fun x => s*m x-2*nonlinear s m
x-(nonlinear s m x)^2)`.

Use: `chebyshev2.Filters.nonlinear_derivative_L1` uses this integrability result to
establish the stated quantitative bound `(∫ x, ‖s*m x-2*nonlinear s m x-(nonlinear s m x)^2‖) ≤
s*(∫ x, m x)+(2+B)*log (transmission s m)`.

Article: chebyshev2, Theorem 3.5 via `chebyshev2.Residual.statePotential_null`.

Proof: Use the identities/estimates `chebyshev2.Filters.nonlinear_integrable`,
`chebyshev2.Filters.nonlinear_square_integrable` with the arguments shown in the proof.
-/
theorem nonlinear_derivative_integrable :
    Integrable (fun x => s*m x-2*nonlinear s m x-(nonlinear s m x)^2) :=
  ((hm.const_mul s).sub ((nonlinear_integrable hm hn hs).const_mul 2)).sub
    (nonlinear_square_integrable hm hn hs)

/--
Proposition 3(ii)'s derivative bound for any uniform bound B on the filter.

The stated quantitative bound `(∫ x, ‖s*m x-2*nonlinear s m x-(nonlinear s m x)^2‖) ≤ s*(∫ x, m
x)+(2+B)*log (transmission s m)`.

Use: `chebyshev2.Filters.nonlinear_derivative_L1_spectral` uses this bound to establish the
stated quantitative bound `(∫ x, ‖s*m x-2*nonlinear s m x-(nonlinear s m x)^2‖) ≤ s*(∫ x, m
x)+(2+‖nonlinearBounded hm hn hs‖)*logDeterminant (kernelEigenvalue hm hn) s`.

Article: chebyshev2, Proposition 8.

Proof: Use the identities/estimates `chebyshev2.Filters.nonlinear_integrable`,
`chebyshev2.Filters.nonlinear_derivative_integrable`,
`chebyshev2.Filters.nonlinear_bounds` with the arguments shown in the proof.
-/
theorem nonlinear_derivative_L1 {B : ℝ} (hB : ∀ x, nonlinear s m x ≤ B) :
    (∫ x, ‖s*m x-2*nonlinear s m x-(nonlinear s m x)^2‖) ≤
      s*(∫ x, m x)+(2+B)*log (transmission s m) := by
  -- Use the identities/estimates `chebyshev2.Filters.nonlinear_integrable`,
  -- `chebyshev2.Filters.nonlinear_derivative_integrable`,
  -- `chebyshev2.Filters.nonlinear_bounds` with the arguments shown in the proof.
  have hi := nonlinear_integrable hm hn hs
  calc
    _ ≤ ∫ x, s*m x+(2+B)*nonlinear s m x := by
      apply integral_mono_ae (nonlinear_derivative_integrable hm hn hs).norm
        ((hm.const_mul s).add (hi.const_mul _))
      exact Eventually.of_forall (fun x => by
        change ‖s*m x-2*nonlinear s m x-(nonlinear s m x)^2‖ ≤ s*m x+(2+B)*nonlinear s m x
        have h0 := (nonlinear_bounds hm hn hs x).1
        have hsq : (nonlinear s m x)^2 ≤ B*nonlinear s m x := by nlinarith [hB x]
        calc
          _ ≤ ‖s*m x‖+‖2*nonlinear s m x‖+‖(nonlinear s m x)^2‖ :=
            (norm_sub_le _ _).trans (add_le_add (norm_sub_le (s*m x) (2*nonlinear s m x)) le_rfl)
          _ = s*m x+2*nonlinear s m x+(nonlinear s m x)^2 := by
            simp only [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hs (hn x)),
              abs_of_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) h0),abs_of_nonneg (sq_nonneg (nonlinear s m x))]
          _ ≤ _ := by nlinarith)
    _ = _ := by
      rw [integral_add (hm.const_mul s) (hi.const_mul _),integral_const_mul,integral_const_mul,
        nonlinear_mass hm hn hs]

omit hs in
/--
Integrability of the displayed function: `Integrable (fun x => groundParameter hm hn*m
x-2*linear hm hn x)`.

Use: `chebyshev2.Filters.defect_derivative_integrable` uses this integrability result to
establish integrability of the displayed function: `Integrable (fun x => (G.q x)^2-2*defect G
x)`.

Article: chebyshev2, Theorem 3.5 via `chebyshev2.Residual.statePotential_null`.

Proof: Use the identities/estimates `chebyshev2.Filters.linear_integrable` with the
arguments shown in the proof.
-/
theorem linear_derivative_integrable :
    Integrable (fun x => groundParameter hm hn*m x-2*linear hm hn x) :=
  (hm.const_mul _).sub ((linear_integrable (hm := hm) (hn := hn)).const_mul 2)

omit hs in
/--
Integrability of the displayed function: `Integrable (fun x => (G.q x)^2-2*defect G x)`.

Use: `chebyshev2.Filters.state_derivative_integrable` uses this integrability result to
establish integrability of the displayed function: `Integrable (stateDerivative G)`.

Article: chebyshev2, Theorem 3.5 via `chebyshev2.Residual.statePotential_null`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem defect_derivative_integrable (G : GroundWitness hm hn) :
    Integrable (fun x => (G.q x)^2-2*defect G x) := by
  have hi := G.coordinate_integrability.2.sub (linear_derivative_integrable hm hn)
  convert hi using 1
  funext x
  change (G.q x)^2-2*(G.q x-linear hm hn x)=
    (groundParameter hm hn*m x-G.q x*(2-G.q x))-(groundParameter hm hn*m x-2*linear hm hn x)
  ring

end
end chebyshev2.Filters
