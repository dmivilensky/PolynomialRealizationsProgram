import nesterov.Stationary.Normalized
import nesterov.Spectral.Feasibility
import polyak.Waves.Mixture

/-!
The spectral program of an actual finite-memory method, with both polynomial
amplitudes retained. The values at query zeros and common zeros are defined
by polynomial evaluation, without cancellation of common factors.
-/
namespace nesterov.StationaryMethod
noncomputable section
open scoped BigOperators
variable (M : nesterov.StationaryMethod)

/-- Evaluation of a real polynomial on the full radius-exp(t) half-circle. -/
def circlePolynomial (q : Polynomial ℝ) (t : ℝ) :
    C(nesterov.Spectral.Frequency,ℂ) :=
  ⟨fun c=>(q.map Complex.ofRealHom).eval (polyak.Waves.z t (Real.arccos c)), by
    unfold polyak.Waves.z
    fun_prop⟩

@[simp] theorem circlePolynomial_apply (q : Polynomial ℝ) (t : ℝ)
    (c : nesterov.Spectral.Frequency) :
    circlePolynomial q t c=(q.map Complex.ofRealHom).eval
      (polyak.Waves.z t (Real.arccos c)) := rfl

/-- The article's pair (u(z),p(z)), on z=exp(t+iω), ω∈[0,π]. -/
def symbolPair (μ L t : ℝ) : nesterov.Spectral.SymbolPair where
  u:=circlePolynomial M.queryPolynomial t
  p:=circlePolynomial (M.normalizedPolynomial μ L) t

@[simp] theorem symbolPair_u (μ L t : ℝ) (c : nesterov.Spectral.Frequency) :
    (M.symbolPair μ L t).u c=(M.queryPolynomial.map Complex.ofRealHom).eval
      (polyak.Waves.z t (Real.arccos c)) := rfl

@[simp] theorem symbolPair_p (μ L t : ℝ) (c : nesterov.Spectral.Frequency) :
    (M.symbolPair μ L t).p c=((M.normalizedPolynomial μ L).map Complex.ofRealHom).eval
      (polyak.Waves.z t (Real.arccos c)) := rfl

/-- Both amplitudes depend jointly continuously on the exponent and frequency. -/
theorem continuous_symbolPair_u (μ L : ℝ) :
    Continuous (fun x : ℝ×nesterov.Spectral.Frequency=>(M.symbolPair μ L x.1).u x.2) := by
  simp only [symbolPair_u]
  unfold polyak.Waves.z
  fun_prop

theorem continuous_symbolPair_p (μ L : ℝ) :
    Continuous (fun x : ℝ×nesterov.Spectral.Frequency=>(M.symbolPair μ L x.1).p x.2) := by
  simp only [symbolPair_p]
  unfold polyak.Waves.z
  fun_prop

/-- A root of the middle-curvature characteristic polynomial is a zero of p. -/
theorem normalizedPolynomial_root_iff {μ L : ℝ} (hμL : μ<L) (z : ℂ) :
    ((M.normalizedPolynomial μ L).map Complex.ofRealHom).eval z=0 ↔
      M.characteristic ((L+μ)/2) z=0 := by
  rw [M.normalizedPolynomial_characteristic]
  have hd : L-μ≠0 := sub_ne_zero.mpr hμL.ne'
  have htwo : (2:ℝ)≠0 := by norm_num
  have hc : (-(2/(L-μ):ℝ):ℂ)≠0 :=
    by simpa only [Complex.ofReal_neg] using
      Complex.ofReal_ne_zero.mpr (neg_ne_zero.mpr (div_ne_zero htwo hd))
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h0|hr
    · exact False.elim (hc (by simpa using h0))
    · exact hr
  · intro h
    rw [h,mul_zero]

end
end nesterov.StationaryMethod
