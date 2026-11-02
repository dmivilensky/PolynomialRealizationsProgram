import jacobi.Oscillation.PhaseInvariant

/-!
Article: jacobi, Proposition B.1.
The same explicit corrected ordinary phase used for McMahon extends to
an actual bounded potential perturbation e with genuine primitive P.
Differentiation cancels the entire nonoscillatory first-order perturbation.
The remaining terms are integrable inverse-square terms and true e,e'
remainders. No averaged phase identity is assumed.
Use: differentiates the actual finite Jacobi phase without assuming it satisfies the unperturbed Bessel phase equation.
-/
namespace jacobi.Oscillation
noncomputable section
open Real Set
set_option backward.isDefEq.respectTransparency false

/-- The literal variation of the McMahon invariant under an arbitrary genuine phase derivative.
Use: differentiates the actual finite Jacobi phase without assuming it satisfies the unperturbed Bessel phase equation.
Article: jacobi, Proposition B.1.
Proof: differentiate the same three explicit phase corrections as in the
unperturbed identity. The excess actual derivative multiplies exactly
the ordinary derivative of the invariant with respect to its phase coordinate. -/
theorem phaseInvariant_hasDerivAt_general {theta : ℝ → ℝ} {c x d : ℝ} (hx : 0<x)
    (ht : HasDerivAt theta d x) :
    HasDerivAt (phaseInvariant c theta)
      (phaseInvariantSlope c theta x+
        (d-(1+c/x^2*sin (theta x)^2))*(1+c*cos (2*theta x)/(2*x^2)+c*sin (2*theta x)/(2*x^3))) x := by
  -- This is an exact chain-rule identity in the actual derivative d, so the later bounded Jacobi perturbation is inserted without changing the phase.
  have hi := hasDerivAt_id x
  have h1 := (hasDerivAt_const x c).div (hi.const_mul 2) (by positivity : 2*x≠0)
  have h2 := ((ht.const_mul 2).sin.const_mul c).div ((hi.pow 2).const_mul 4) (by positivity : 4*x^2≠0)
  have h3 := ((ht.const_mul 2).cos.const_mul c).div ((hi.pow 3).const_mul 4) (by positivity : 4*x^3≠0)
  convert (((ht.sub hi).add h1).add h2).sub h3 using 1
  · rfl
  · dsimp only [phaseInvariantSlope]
    norm_num only [Pi.pow_apply,id_eq,Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one,zero_mul,zero_sub]
    simp only [Real.cos_two_mul_eq_one_sub]
    field_simp [hx.ne']
    ring

/-- The exact corrected finite phase for an actual perturbation and its actual primitive.
Use: its genuine derivative has only integrable perturbative errors, giving the printed regular-potential correction in Proposition B.1 (a).
Article: jacobi, Proposition B.1.
-/
def perturbedInvariant (c : ℝ) (theta e P : ℝ → ℝ) (x : ℝ) : ℝ :=
  phaseInvariant c theta x-P x/2+e x*sin (2*theta x)/4

/-- The literal genuine derivative remainder of the corrected finite phase.
Use: comparison with the actual Bessel invariant controls the full no-logarithm finite phase correction.
Article: jacobi, Proposition B.1.
-/
def perturbedInvariantSlope (c : ℝ) (theta e e' : ℝ → ℝ) (x : ℝ) : ℝ :=
  phaseInvariantSlope c theta x+
    c*e x*cos (2*theta x)*sin (theta x)^2/x^2+
    c*e x*sin (2*theta x)*sin (theta x)^2/(2*x^3)+
    e x^2*cos (2*theta x)*sin (theta x)^2/2+e' x*sin (2*theta x)/4

/-- The corrected finite Jacobi phase has exactly the displayed true perturbative derivative, with its entire first-order mean canceled.
Use: proves the analytic averaged correction needed for the full uniform angular expansion in Proposition B.1 (a).
Article: jacobi, Proposition B.1.
Proof: apply the proved general derivative identity to the genuine
perturbed phase. Differentiate its primitive and additional sine term.
The exact double-angle identity cancels e*(sin^2+cos(2*phase)/2-1/2),
leaving precisely the explicit inverse-square, quadratic and e' remainders. -/
theorem perturbedInvariant_hasDerivAt {theta e P e' : ℝ → ℝ} {c x : ℝ} (hx : 0<x)
    (ht : HasDerivAt theta (1+(c/x^2+e x)*sin (theta x)^2) x)
    (he : HasDerivAt e (e' x) x) (hP : HasDerivAt P (e x) x) :
    HasDerivAt (perturbedInvariant c theta e P) (perturbedInvariantSlope c theta e e' x) x := by
  have h := ((phaseInvariant_hasDerivAt_general (c := c) hx ht).sub (hP.div_const 2)).add
    ((he.mul ((ht.const_mul 2).sin)).div_const 4)
  convert h using 1
  · rfl
  · dsimp only [perturbedInvariantSlope]
    simp only [Real.cos_two_mul_eq_one_sub]
    field_simp [hx.ne']
    ring

end
end jacobi.Oscillation
