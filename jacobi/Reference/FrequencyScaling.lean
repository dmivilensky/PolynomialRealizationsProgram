import jacobi.Reference.WaveAnalytic

/-!
Article: jacobi, Lemma C.1.
The actual reference hypergeometric coefficients have a uniform majorant
when their spatial argument is of order |omega|^-2. This controls the
true initial data at t of order |omega|^-1 before propagation by the
reference differential equation.
Use: bounds the original reference coefficients uniformly in arbitrarily large complex frequencies.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Complex Polynomial
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- A rising factorial with an initial norm bounded by K*R has the actual scaled positive rising-factorial majorant.
Use: bounds the original reference coefficients uniformly in arbitrarily large complex frequencies.
Article: jacobi, Lemma C.1.
Proof: each integer next factor satisfies K*R+n<=(K+n)*R when R>=1.
Multiply this by the genuine induction bound, preserving the original
terminating factors whenever they occur. -/
theorem pochhammer_norm_scaled {u : ℂ} {K R : ℝ} (hK : 0<K) (hR : 1≤R)
    (hu : ‖u‖≤K*R) (n : ℕ) :
    ‖(ascPochhammer ℂ n).eval u‖≤R^n*(ascPochhammer ℝ n).eval K := by
  -- No asymptotic expansion is supplied: this is an exact bound on every original finite product.
  have hRp : 0<R := lt_of_lt_of_le zero_lt_one hR
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_eval,ascPochhammer_succ_eval,norm_mul,pow_succ]
    have hn : 0≤(n:ℝ) := Nat.cast_nonneg n
    have hf : ‖u+(n:ℂ)‖≤R*(K+n) := by
      have hh := norm_add_le u (n:ℂ)
      rw [Complex.norm_natCast] at hh
      nlinarith [mul_le_mul_of_nonneg_left hR hn]
    have hh := mul_le_mul ih hf (norm_nonneg _) (mul_nonneg (pow_nonneg hRp.le n) (ascPochhammer_pos n K hK).le)
    convert hh using 1
    ring

/-- The actual ordinary hypergeometric coefficients have a scaled majorant with one fixed positive numerator parameter.
Use: turns the true reference series at |x|=O(|omega|^-2) into one genuine fixed convergent 2F1 majorant.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Proof: the two genuine numerator rising factorials have the proved
scaled bounds. Their actual denominator is shared by the original and
majorizing community series. Factor out exactly R^(2*n). -/
theorem hypergeometric_coefficient_scaled {u v c : ℂ} {K R : ℝ}
    (hK : 0<K) (hR : 1≤R) (hu : ‖u‖≤K*R) (hv : ‖v‖≤K*R) (n : ℕ) :
    ‖ordinaryHypergeometricCoefficient u v c n‖≤
      R^(2*n)*‖ordinaryHypergeometricCoefficient (K:ℂ) (K:ℂ) c n‖ := by
  -- The actual denominator is kept throughout; no zero-factor cancellation is needed.
  have hp := pochhammer_norm_scaled hK hR hu n
  have hq := pochhammer_norm_scaled hK hR hv n
  have hkp : 0<(ascPochhammer ℝ n).eval K := ascPochhammer_pos n K hK
  have hreal : ‖(ascPochhammer ℂ n).eval (K:ℂ)‖=(ascPochhammer ℝ n).eval K := by
    rw [Hypergeometric.pochhammer_ofReal,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hkp]
  unfold ordinaryHypergeometricCoefficient
  simp only [norm_mul,norm_inv,hreal]
  have hh := mul_le_mul hp hq (norm_nonneg _) (by positivity : 0≤R^n*(ascPochhammer ℝ n).eval K)
  have hh' := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (norm_nonneg (n.factorial:ℂ)))
  have hh'' := mul_le_mul_of_nonneg_right hh' (inv_nonneg.mpr (norm_nonneg ((ascPochhammer ℂ n).eval c)))
  rw [show 2*n=n+n by omega,pow_add]
  convert hh'' using 1 <;> ring

/-- The fixed positive comparison parameter for the original reference frequency coefficients.
Use: a single genuine positive-parameter 2F1 series controls every original frequency with norm at least one.
Article: jacobi, Appendix C.1 (negative-energy bounds).
-/
def frequencyMajorant (a : ℝ) : ℝ := |gamma a|+1/Real.pi+1

/-- Both original affine numerator parameters have norms bounded by the fixed majorant times the actual frequency norm.
Use: discharges the true frequency parameter premises of the scaled coefficient estimate.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Proof: use the complex triangle inequality, the genuine positive pi denominator and norm(omega)>=1. -/
theorem frequency_parameters_scaled (a : ℝ) {omega : ℂ} (homega : 1≤‖omega‖) :
    0<frequencyMajorant a ∧
      ‖(gamma a:ℂ)-omega/(Real.pi:ℂ)‖≤frequencyMajorant a*‖omega‖ ∧
      ‖(gamma a:ℂ)+omega/(Real.pi:ℂ)‖≤frequencyMajorant a*‖omega‖ := by
  -- The comparison parameter depends only on the original real order, never on the frequency.
  have hd : ‖omega/(Real.pi:ℂ)‖=‖omega‖/Real.pi := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  have hm := norm_sub_le (gamma a:ℂ) (omega/(Real.pi:ℂ))
  have hp := norm_add_le (gamma a:ℂ) (omega/(Real.pi:ℂ))
  rw [Complex.norm_real,Real.norm_eq_abs,hd] at hm hp
  have hh := mul_le_mul_of_nonneg_left homega (abs_nonneg (gamma a))
  dsimp [frequencyMajorant]
  refine ⟨by positivity,?_,?_⟩ <;> simp only [div_eq_mul_inv] at hm hp ⊢ <;> nlinarith

/-- Every actual original reference frequency coefficient has the fixed scaled 2F1 majorant.
Use: proves the genuine small-scale core and initial-state bounds for the high-frequency ODE estimate.
Article: jacobi, Lemma C.1.
Proof: apply the proved genuine scaled coefficient theorem to the actual source affine parameters and the explicit positive comparison parameter. -/
theorem frequencyCoefficient_scaled (a : ℝ) {omega : ℂ} (homega : 1≤‖omega‖) (n : ℕ) :
    ‖frequencyCoefficient a n omega‖≤‖omega‖^(2*n)*
      ‖ordinaryHypergeometricCoefficient (frequencyMajorant a:ℂ) (frequencyMajorant a:ℂ) ((gamma a:ℂ)+1/2) n‖ := by
  obtain ⟨hK,hm,hp⟩ := frequency_parameters_scaled a homega
  exact hypergeometric_coefficient_scaled hK homega hm hp n

end
end jacobi.Reference
