import jacobi.Bessel.McMahon

/-!
Article: jacobi, Proposition B.1.
The actual squared edge spectrum differs from the explicit shifted phase
squares by a uniform inverse-square error. This is the precise spectral
input used by the later reference operator and norming-ratio estimates.
Use: multiplication of the original cubic McMahon remainder by the leading phase yields a quadratic spectral remainder.
-/
namespace jacobi.Bessel
noncomputable section
open Real Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual leading Bessel phases have a uniform linear upper bound.
Use: multiplication of the original cubic McMahon remainder by the leading phase yields a quadratic spectral remainder.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: bound the fixed phase offset by |alpha|+2 and use positivity of the original index. -/
theorem phaseGrid_upper (a : ℝ) (k : ℕ) :
    phaseGrid a k≤(Real.pi*(|a|+2))*(k+1:ℝ) := by
  have hk : (0:ℝ)≤k := Nat.cast_nonneg k
  have hh : (k:ℝ)+a/2+3/4≤(|a|+2)*(k+1:ℝ) := by
    nlinarith [le_abs_self a,abs_nonneg a,mul_nonneg (abs_nonneg a) hk]
  unfold phaseGrid
  nlinarith [mul_le_mul_of_nonneg_left hh Real.pi_pos.le]

/-- Squaring a genuine cubic corrected zero estimate yields an explicit quadratic shifted-square estimate.
Use: applies the actual McMahon bound to the original spectral zeros sigma_k, with no separate spectral asymptotic hypothesis.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: expand x^2-v^2-c as 2*v*(x-v-c/(2*v))+(x-v)^2.
Bound the first term by the cubic error times the linear phase and the
second by the square of the proved leading inverse-linear error. -/
theorem squared_correction_bound {x v t L A C c : ℝ} (ht : 0<t) (hv : 0<v)
    (hL : 0≤L) (hA : 0≤A) (hvl : v≤L*t)
    (hfirst : |x-v|≤A/t) (hmc : |x-v-c/(2*v)|≤C/t^3) :
    |x^2-(v^2+c)|≤(2*L*C+A^2)/t^2 := by
  -- The exact square expansion retains the correction c and makes the cubic-to-quadratic loss explicit.
  have hid : x^2-(v^2+c)=2*v*(x-v-c/(2*v))+(x-v)^2 := by
    field_simp [hv.ne']
    ring
  have hs : (x-v)^2≤(A/t)^2 := by
    have h := (sq_le_sq₀ (abs_nonneg (x-v)) (by positivity : 0≤A/t)).mpr hfirst
    simpa only [sq_abs] using h
  rw [hid]
  calc
    _ ≤ |2*v*(x-v-c/(2*v))|+|(x-v)^2| := abs_add_le _ _
    _ = 2*v*|x-v-c/(2*v)|+(x-v)^2 := by
      rw [abs_mul,abs_of_pos (by positivity : 0<2*v),abs_of_nonneg (sq_nonneg (x-v))]
    _ ≤ 2*(L*t)*(C/t^3)+(A/t)^2 := by
      exact add_le_add (mul_le_mul (by linarith : 2*v≤2*(L*t)) hmc (abs_nonneg _) (by positivity)) hs
    _ = _ := by field_simp [ht.ne']

/-- The original Bessel edge spectrum satisfies the full uniform quadratic McMahon remainder for its explicit reference spectrum.
Use: provides the unconditional spectral perturbation estimate for the continuum reference construction, norming products and both-edge Jacobi bounds.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: combine the proved original cubic McMahon bound, the genuine
leading inverse-index bound and the explicit linear phase bound, then
apply the exact scalar square expansion at every actual source index. -/
theorem mcmahon_squared {a : ℝ} (ha : -1<a) :
    ∃ C : ℝ,0<C ∧ ∀ k,
      |sigma a ha k-((phaseGrid a k)^2+(1/4-a^2))|≤C/(k+1:ℝ)^2 := by
  -- Every estimate here concerns the same actual exhaustive zero enumeration; no reference-spectrum closeness is assumed.
  obtain ⟨A,hA,hfirst⟩ := positiveZero_phase_bound ha
  obtain ⟨C,hC,hmc⟩ := mcmahon ha
  let L := Real.pi*(|a|+2)
  refine ⟨2*L*C+A^2,by dsimp [L]; positivity,?_⟩
  intro k
  rw [← (positiveZero_properties ha k).2]
  exact squared_correction_bound (by positivity) (phaseGrid_pos ha k)
    (by dsimp [L]; positivity) hA.le (phaseGrid_upper a k) (hfirst k) (hmc k)

end
end jacobi.Bessel
