import krylov.Stability.CompactCoefficients

/-!
Article: main_krylov, lem:U(c), positive homogeneous cones.
Use: transfer actual Taylor remainders and their constants from normalized
initial gradients to all positive multiples of those gradients.
Source: mathlib's genuine iterated derivative rule for constant scalar multiplication.
-/

namespace krylov.Stability
noncomputable section
open Set
open scoped BigOperators
variable {Z F G : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Genuine finite Taylor polynomials commute with constant output scaling.
Use: homogeneous cone estimates include every actual lower-order coefficient.
Article: main_krylov, lem:U(c).
Proof: each genuine iterated derivative scales by the same constant; commute
the two real scalar factors and collect the finite physical sum. -/
theorem taylorPolynomial_const_smul (f : Z → F) (k : ℕ) (x h : Z) (c : ℝ)
    (hf : ContDiffAt ℝ k f x) :
    taylorPolynomial (fun z => c • f z) k x h=c • taylorPolynomial f k x h := by
  -- Differentiation is in the perturbation variable, so the initial-gradient scale is constant.
  rw [taylorPolynomial, taylorPolynomial, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [iteratedFDeriv_const_smul_apply' (hf.of_le (by exact_mod_cast (Finset.mem_range.mp hj).le))]
  change (j.factorial : ℝ)⁻¹ • (c • iteratedFDeriv ℝ j f x (fun _ => h))=
    c • ((j.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ j f x (fun _ => h))
  exact smul_comm _ _ _

/-- Positive homogeneity of the actual output implies positive homogeneity of its full actual Taylor remainder.
Use: the cone result concerns the true cycle map and its genuine derivatives.
Article: main_krylov, lem:U(c), Φ and its coefficients scale in g₀.
Proof: identify the two actual perturbation functions by homogeneity and
apply the proved finite Taylor scaling identity before subtracting their outputs. -/
theorem homogeneous_taylor_remainder (f : G → Z → F) (k : ℕ) (g : G) (x h : Z)
    (c : ℝ)
    (hhom : ∀ z, f (c • g) z=c • f g z) (hf : ContDiffAt ℝ k (f g) x) :
    f (c • g) (x+h)-taylorPolynomial (f (c • g)) k x h=
      c • (f g (x+h)-taylorPolynomial (f g) k x h) := by
  have he : f (c • g)=(fun z => c • f g z) := funext hhom
  rw [he, taylorPolynomial_const_smul _ k x h c hf, smul_sub]

/-- A normalized-slice remainder estimate has exactly the same constant on its actual positive homogeneous cone.
Use: no scale-dependent compactness argument is needed for larger or smaller initial gradients.
Article: main_krylov, lem:U(c), cone extension with the initial-error factor.
Proof: the actual remainder scales by c and its norm by the same positive
factor; multiply the slice estimate and reassociate the homogeneous error factor. -/
theorem homogeneous_taylor_remainder_bound (f : G → Z → F) (k : ℕ) (g : G) (x h : Z)
    (c : ℝ) (hc : 0<c) (hhom : ∀ z, f (c • g) z=c • f g z)
    (hf : ContDiffAt ℝ k (f g) x) {C e : ℝ}
    (hb : ‖f g (x+h)-taylorPolynomial (f g) k x h‖≤C*‖h‖^k*e) :
    ‖f (c • g) (x+h)-taylorPolynomial (f (c • g)) k x h‖≤C*‖h‖^k*(c*e) := by
  rw [homogeneous_taylor_remainder f k g x h c hhom hf, norm_smul, Real.norm_of_nonneg hc.le]
  exact (mul_le_mul_of_nonneg_left hb hc.le).trans_eq (by ring)

end
end krylov.Stability
