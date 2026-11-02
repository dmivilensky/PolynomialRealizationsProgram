import jacobi.Finite.AnalyticChart

/-!
Article: jacobi, Proposition 1.1.
Reversal is negation in the logarithmic weight chart. The actual Jacobi energy
is consequently even and analytic, and its full Frechet differential vanishes
at the unique persymmetric point. No stationarity hypothesis is introduced.
Source: the reciprocal-weight involution and the chain rule in mathlib.
Use: proves evenness of the actual fibre energy.
-/
namespace jacobi.Finite
noncomputable section
open chebyshev1 chebyshev2 Matrix Real
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} (S : Nodes (n+1))

/-- Reversal of logarithmic reconstruction is reconstruction at the negative parameter.
Use: proves evenness of the actual fibre energy.
Article: jacobi, Proposition 1.1.
Proof: the reciprocal-weight formula makes reversed probabilities proportional
to those at -ell; both sum to one, so the proportionality constant is one. -/
theorem logFiber_reverse (ell : Fin (n+1) → ℝ) :
    reverseFiber (logFiber S ell) = logFiber S (-ell) := by
  -- The two candidate probability vectors are proportional by the cofactor identity; normalization fixes the factor.
  let J := logFiber S ell
  let c := J.val.data.couplingProduct 1 n * logNormalizer S ell * logNormalizer S (-ell)
  have hw (k : Fin (n+1)) : (spectralWeights S (reverseFiber J)).val k =
      c * (logWeights S (-ell)).val k := by
    rw [spectralWeights_reverse, show spectralWeights S J = logWeights S ell from
      spectralWeights_reconstruct S (logWeights S ell)]
    change _ / ((Real.exp (ell k) * _⁻¹ / _) * _^2) =
      c * (Real.exp (-ell k) * _⁻¹ / _)
    rw [Real.exp_neg]
    dsimp [c]
    field_simp [abs_ne_zero.mpr (S.derivative_ne_zero k),
      (logNormalizer_pos S ell).ne', (logNormalizer_pos S (-ell)).ne']
    rw [sq_abs]
    exact mul_div_cancel_right₀ _ (pow_ne_zero 2 (S.derivative_ne_zero k))
  have hc : c = 1 := by
    have h := (spectralWeights S (reverseFiber J)).property.2
    simp_rw [hw] at h
    rw [← Finset.mul_sum, (logWeights S (-ell)).property.2, mul_one] at h
    exact h
  apply (weightEquiv S).injective
  change spectralWeights S (reverseFiber J) = spectralWeights S (logFiber S (-ell))
  rw [show spectralWeights S (logFiber S (-ell)) = logWeights S (-ell) from
    spectralWeights_reconstruct S (logWeights S (-ell))]
  apply Subtype.ext
  funext k
  rw [hw, hc, one_mul]

/-- The energy is even in the full logarithmic coordinate space.
Use: the common-shift redundancy is already proved, so this is evenness on the quotient too.
Article: jacobi, Proposition 1.1.
Proof: identify the negative chart matrix with the reversed matrix and reuse
energy invariance under physical reversal. -/
theorem logEnergy_even (ell : Fin (n+1) → ℝ) : logEnergy S (-ell) = logEnergy S ell := by
  have h := congrArg (fun J : Fiber (n+1) S.polynomial => J.val.energy) (logFiber_reverse S ell)
  exact h.symm.trans (reverse_energy _)

/-- The article's canonical point is the actual zero-parameter reconstruction.
Use: identifies the vanishing differential with criticality of J*_p itself.
Article: jacobi, Proposition 1.1.
Proof: Substitute the identity between zero-parameter and reciprocal-derivative weights. -/
theorem logFiber_zero : logFiber S 0 = persymmetricFiber S := by
  unfold logFiber persymmetricFiber
  rw [logWeights_zero]

/-- An even differentiable real function has zero full differential at the origin.
Use: the analytic Jacobi energy satisfies these hypotheses without extra assumptions.
Article: jacobi, Proposition 1.1.
Source: the Frechet chain rule and uniqueness of derivatives in mathlib.
Proof: differentiating f(-x)=f(x) at zero identifies the differential with its
negative, and hence every value of that real linear map is zero. -/
theorem fderiv_even_zero {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (f : D → ℝ) (hd : DifferentiableAt ℝ f 0) (he : ∀ x, f (-x) = f x) :
    fderiv ℝ f 0 = 0 := by
  -- Apply the chain rule to negation, then compare the two derivatives of the same even function.
  have hf : HasFDerivAt f (fderiv ℝ f 0) (-(0 : D)) := by simpa only [neg_zero] using hd.hasFDerivAt
  have hneg := hf.comp 0 ((hasFDerivAt_id (𝕜 := ℝ) (0 : D)).neg)
  have heq : (f ∘ fun x : D => -x) = f := funext he
  rw [heq] at hneg
  have h := hd.hasFDerivAt.unique hneg
  ext x
  have hx := congrArg (fun L : D →L[ℝ] ℝ => L x) h
  change fderiv ℝ f 0 x = fderiv ℝ f 0 (-x) at hx
  rw [map_neg] at hx
  change fderiv ℝ f 0 x = 0
  linarith

/-- The unique persymmetric fibre point is a critical point of the actual Green energy.
Use: the finite stationary candidate for the persymmetric continuum limit.
Article: jacobi, Proposition 1.1.
Proof: the proved energy is analytic and even in the proved logarithmic chart;
its Frechet differential at the origin therefore vanishes. -/
theorem persymmetric_critical : fderiv ℝ (logEnergy S) 0 = 0 :=
  fderiv_even_zero _ (logEnergy_analytic S 0).differentiableAt (logEnergy_even S)

end
end jacobi.Finite
