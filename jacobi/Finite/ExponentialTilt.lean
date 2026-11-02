import jacobi.Finite.ResolventFlow

/-!
Differentiation of positive finite exponential tilts.
These formulas differentiate the literal spectral probabilities used by
the global resolvent flow; no ODE or prescribed derivative is assumed.
Use: ResolventLax differentiates weighted polynomial evaluations and
identifies the tangent matrix through orthogonality of different degrees.
Article: jacobi, Proposition 5.5, Equation (5.11).
Article role: the global positive-weight construction and its exact resolvent Lax equation.
-/
namespace jacobi.Finite
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Real
open scoped BigOperators
variable {n : ℕ}

/-- The positive partition sum for a finite exponential tilt.
Article: jacobi, Proposition 5.5, Equation (5.11).
-/
def tiltNormalizer (w : WeightSimplex (n+1)) (v : Fin (n+1) → ℝ) (t : ℝ) : ℝ :=
  ∑ k,w.val k*exp (t*v k)

/-- The normalized tilted probability at one original support node.
Article: jacobi, Proposition 5.5, Equation (5.11).
-/
def tiltWeight (w : WeightSimplex (n+1)) (v : Fin (n+1) → ℝ) (t : ℝ)
    (k : Fin (n+1)) : ℝ := w.val k*exp (t*v k)/tiltNormalizer w v t

/-- The partition sum is positive at every real time, including negative
times. This is the denominator needed in all derivative identities.
Article: jacobi, Proposition 5.5, Equation (5.11).
-/
theorem tiltNormalizer_pos (w : WeightSimplex (n+1)) (v : Fin (n+1) → ℝ) (t : ℝ) :
    0<tiltNormalizer w v t :=
  Finset.sum_pos (fun k _ => mul_pos (w.property.1 k) (exp_pos _)) Finset.univ_nonempty

/-- Every tilted probability remains strictly positive.
Article: jacobi, Proposition 5.5, Equation (5.11).
-/
theorem tiltWeight_pos (w : WeightSimplex (n+1)) (v : Fin (n+1) → ℝ) (t : ℝ)
    (k : Fin (n+1)) : 0<tiltWeight w v t k :=
  div_pos (mul_pos (w.property.1 k) (exp_pos _)) (tiltNormalizer_pos w v t)

/-- Differentiate the actual finite partition sum term by term.
Article: jacobi, Proposition 5.5, Equation (5.11).
-/
theorem tiltNormalizer_hasDerivAt (w : WeightSimplex (n+1)) (v : Fin (n+1) → ℝ)
    (t : ℝ) : HasDerivAt (tiltNormalizer w v)
      (∑ k,w.val k*exp (t*v k)*v k) t := by
  have h (k : Fin (n+1)) : HasDerivAt (fun s => w.val k*exp (s*v k))
      (w.val k*exp (t*v k)*v k) t := by
    simpa only [Function.comp_def,id_eq,one_mul,mul_assoc] using
      (((hasDerivAt_exp (t*v k)).comp t ((hasDerivAt_id t).mul_const (v k))).const_mul (w.val k))
  change HasDerivAt (fun s => ∑ k,w.val k*exp (s*v k)) _ t
  exact HasDerivAt.fun_sum (u := Finset.univ) (fun k _ => h k)

/-- The derivative of a tilted probability is its value times the
centered logarithmic velocity. This formula includes normalization.
Article: jacobi, Proposition 5.5, Equation (5.11).
-/
theorem tiltWeight_hasDerivAt (w : WeightSimplex (n+1)) (v : Fin (n+1) → ℝ)
    (t : ℝ) (k : Fin (n+1)) : HasDerivAt (fun s => tiltWeight w v s k)
      ((v k-∑ j,tiltWeight w v t j*v j)*tiltWeight w v t k) t := by
  have hn : HasDerivAt (fun s => w.val k*exp (s*v k))
      (w.val k*exp (t*v k)*v k) t := by
    simpa only [Function.comp_def,id_eq,one_mul,mul_assoc] using
      (((hasDerivAt_exp (t*v k)).comp t ((hasDerivAt_id t).mul_const (v k))).const_mul (w.val k))
  convert hn.div (tiltNormalizer_hasDerivAt w v t) (tiltNormalizer_pos w v t).ne' using 1
  · rfl
  · simp only [tiltWeight,div_mul_eq_mul_div,← Finset.sum_div]
    field_simp [(tiltNormalizer_pos w v t).ne']

/-- Square-root probabilities have half the centered logarithmic
velocity. They are the weight factors in the actual orthonormal eigenbasis.
Article: jacobi, Proposition 5.5, Equation (5.11).
-/
theorem tiltWeight_sqrt_hasDerivAt (w : WeightSimplex (n+1)) (v : Fin (n+1) → ℝ)
    (t : ℝ) (k : Fin (n+1)) : HasDerivAt (fun s => sqrt (tiltWeight w v s k))
      (((v k-∑ j,tiltWeight w v t j*v j)/2)*sqrt (tiltWeight w v t k)) t := by
  convert (tiltWeight_hasDerivAt w v t k).sqrt (tiltWeight_pos w v t k).ne' using 1
  have hp := sqrt_pos.mpr (tiltWeight_pos w v t k)
  have hs := sq_sqrt (tiltWeight_pos w v t k).le
  field_simp [hp.ne']
  rw [hs]

/-- The literal probabilities of the reconstructed resolvent flow are
the exponential tilt differentiated above.
Article: jacobi, Proposition 5.5, Equation (5.11).
-/
theorem resolventWeights_eq_tilt (S : Nodes (n+1)) (w : WeightSimplex (n+1))
    (t : ℝ) (k : Fin (n+1)) :
    (resolventWeights S w t).val k=tiltWeight w (resolventVelocity S) t k :=
  resolventWeights_formula S w t k

end
end jacobi.Finite
