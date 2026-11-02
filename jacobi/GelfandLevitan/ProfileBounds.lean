import jacobi.GelfandLevitan.Profiles
import jacobi.Bessel.McMahonAlgebra

/-!
Article: jacobi, Theorem 2.1.
The constructed transformed solution has the original inverse-index
decay, while the true reference norming integral has its matching
squared power. Their powers cancel exactly. The already proved actual
rho bound then bounds the original continuous profiles uniformly.
The finite-prefix absorption lemma from the Bessel analysis applies
with exponent zero, so no numerical prefix verification is required.
Use: finite-prefix absorption gives the full source uniform Phi_k bound and the summable Lambda-weighted profile series.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The true original continuous spectral profiles have one uniform norm bound for every sufficiently large actual spectral index.
Use: finite-prefix absorption gives the full source uniform Phi_k bound and the summable Lambda-weighted profile series.
Article: jacobi, Theorem 2.1.
Proof: the actual transformed spectral amplitude is at most C*p with
p=(k+1)^(-gamma). The true reference norm is at least c*p^2 and the
original rho is uniformly bounded. Its genuine normalized squared
solution is therefore bounded by the single constant R*C^2/c. -/
theorem spectralProfile_tail_bound (a : ℝ) (ha : -1<a) :
    ∃ D:ℝ,0<D ∧ ∀ᶠ k:ℕ in atTop,‖spectralProfile a ha k‖≤D := by
  -- The matching original reference norming power cancels the actual transformed solution power, rather than introducing an assumed normalized-profile bound.
  obtain ⟨C,hC,hU⟩ := transformedSolution_spectral_bound a ha
  obtain ⟨_,R,_,_,hR,_,hRatio⟩ := normingRatio_bounds ha
  obtain ⟨c,_,hc,_,hNorm⟩ := norming_bounds ha
  refine ⟨R*C^2/c,by positivity,?_⟩
  filter_upwards [hU] with k hk
  apply ((spectralProfile a ha k).norm_le (by positivity)).mpr
  intro t
  let p := (k+1:ℝ)^(-gamma a)
  let x := realTransformedSolution a ha (jacobi.Bessel.sigma a ha k) (physicalFold t)
  have hp : 0<p := Real.rpow_pos_of_pos (by positivity) _
  have hpsq : p^2=1/(k+1:ℝ)^(2*gamma a) := by
    dsimp [p]
    rw [Real.rpow_neg (by positivity : 0≤(k+1:ℝ)),show 2*gamma a=gamma a*2 by ring,
      Real.rpow_mul (by positivity : 0≤(k+1:ℝ)),Real.rpow_two,inv_pow,one_div]
  have hN : c*p^2≤norming a k := by
    rw [hpsq]
    simpa only [mul_one_div] using (hNorm k).1
  have hx : |x|≤C*p := by
    change |(transformedSolution a ha (physicalFold t) (jacobi.Bessel.sigma a ha k:ℂ)).re|≤C*p
    exact (Complex.abs_re_le_norm
      (transformedSolution a ha (physicalFold t) (jacobi.Bessel.sigma a ha k:ℂ))).trans (hk _)
  have hx2 : x^2≤(C*p)^2 := by
    obtain ⟨hlo,hhi⟩ := abs_le.mp hx
    have hh := mul_nonneg (sub_nonneg.mpr hhi) (show 0≤C*p+x by linarith)
    nlinarith
  have hnum : normingRatio a ha k*x^2≤R*(C*p)^2 :=
    mul_le_mul (hRatio k).2.1 hx2 (sq_nonneg _) hR.le
  have hvalue : spectralProfile a ha k t=(normingRatio a ha k/norming a k)*x^2 := rfl
  rw [hvalue,Real.norm_eq_abs]
  rw [abs_of_nonneg (mul_nonneg
    (div_pos (normingRatio_properties ha k).2 (norming_pos ha k)).le (sq_nonneg _)),div_mul_eq_mul_div]
  have hh := div_le_div₀ (show 0≤R*(C*p)^2 by positivity) hnum (mul_pos hc (sq_pos_of_pos hp)) hN
  exact hh.trans_eq (by field_simp [hc.ne',hp.ne'])

/-- One positive constant bounds every actual original continuous spectral profile in the uniform norm, including every small spectral index.
Use: the original summable Bessel Lambda sequence dominates the entire persymmetric profile series in the genuine continuous-function norm.
Article: jacobi, Theorem 2.1.
Proof: use the actual tail estimate and the previously proved finite-prefix inverse-power absorption lemma with exponent zero. It absorbs the genuine finite continuous-function norms, without a finite numerical certificate. -/
theorem spectralProfile_uniform_bound (a : ℝ) (ha : -1<a) :
    ∃ D:ℝ,0<D ∧ ∀ k:ℕ,‖spectralProfile a ha k‖≤D := by
  obtain ⟨C,_,hTail⟩ := spectralProfile_tail_bound a ha
  have he : ∀ᶠ k:ℕ in atTop,|‖spectralProfile a ha k‖|≤C/(k+1:ℝ)^0 := by
    simpa only [abs_norm,pow_zero,div_one] using hTail
  obtain ⟨D,hD,hAll⟩ := jacobi.Bessel.inversePower_bound_all 0 he
  exact ⟨D,hD,fun k => by simpa only [abs_norm,pow_zero,div_one] using hAll k⟩

end
end jacobi.GelfandLevitan
