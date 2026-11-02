import jacobi.Support.EnvelopeDerivative

/-!
Article: jacobi, Appendix C.3 (polynomial and derivative envelopes).
The complete original complex wave and derivative envelope is stated
with one common positive constant, one degree threshold and the full
original index ranges. The endpoint-one assertion is independently
proved by naturalPolynomial_one_bound.
Use: the original support weights and target/support Gram limits use the full source envelope for the same actual spectral polynomials, with no unproved wave or coefficient premise.
-/
namespace jacobi.Support
noncomputable section
open Real Filter jacobi.Reference
open scoped Topology

/-- The complete original support wave and angular derivative envelopes hold together with common positive constants.
Use: the original support weights and target/support Gram limits use the full source envelope for the same actual spectral polynomials, with no unproved wave or coefficient premise.
Article: jacobi, Appendix C.3 (polynomial and derivative envelopes).
Proof: both original bounds have been proved independently for the actual same support polynomial on their full printed strips and index ranges. Sum their positive constants and intersect their genuine eventual degree thresholds. -/
theorem envelope_estimates {a b bnd:ℝ} (ha:-1<a) (hb:-1<b) (hbnd:0<bnd) :
    ∃C:ℝ,0<C ∧ ∀ᶠn:ℕ in atTop,∀m:ℕ,2*m≤n+3→
      (∀theta:ℂ,theta≠0→|theta.re|≤4*π/5→|theta.im|≤bnd/ jacobi.Jacobi.frequency a b (n+1)→
        ‖naturalWave a b ha hb n m (Complex.cos theta)‖≤
          C*min (((m:ℝ)+1)^gamma a) (‖theta‖^(-gamma a))) ∧
      (∀theta:ℂ,theta≠0→|theta.re|≤3*π/4→|theta.im|≤bnd/ jacobi.Jacobi.frequency a b (n+1)→
        ‖deriv (fun z:ℂ => naturalWave a b ha hb n m (Complex.cos z)) theta‖≤
          C* jacobi.Jacobi.frequency a b (n+1)*min (((m:ℝ)+1)^gamma a) (‖theta‖^(-gamma a))) := by
  -- Only the source constants and true degree thresholds are combined; both actual polynomial estimates are already proved in full.
  obtain ⟨A,hA,hwave⟩ := naturalWave_frequency_envelope ha hb hbnd
  obtain ⟨D,hD,hderiv⟩ := naturalWave_frequency_derivative ha hb hbnd
  refine ⟨A+D,by positivity,?_⟩
  filter_upwards [hwave,hderiv] with n hnA hnD
  intro m hm
  constructor
  · intro theta ht hre him
    exact (hnA m hm theta ht hre him).trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right hD.le) (by positivity))
  · intro theta ht hre him
    have hN := jacobi.Jacobi.frequency_pos ha hb (show 0<n+1 by omega)
    exact (hnD m hm theta ht hre him).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA.le) hN.le) (by positivity))

end
end jacobi.Support
