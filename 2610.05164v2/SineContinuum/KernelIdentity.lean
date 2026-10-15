import «2610.05164v2».SineContinuum.Density
import «2610.05164v2».Continuum.ExponentialFeature

/-!
Article: 2610.05164v2, Lemma 5.
Concrete sine features in the already constructed 2606.16671v2I Hilbert space.
Use: `«2610.05164v2».SineContinuum.sineFeature_inner` feeds
`«2610.05164v2».SineContinuum.green_mercer_hasSum` (green mercer has Sum).
Proof chain: `«2610.05164v2».SineContinuum.green_mercer_uniform` — 2610.05164v2, Lemma 5; Legendre
operator, nonlogarithmic realization and continuum sine spectrum.
-/
namespace «2610.05164v2».SineContinuum
noncomputable section
open Set Real «2610.05164v2».Continuum
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/--
Exact identity `exp (2*X t)=l t/r t`.

Use: `«2610.05164v2».SineContinuum.ordered_kernel` rewrites with this identity to establish
exact identity `sqrt (SineJacobi.phi t)*sqrt (SineJacobi.phi s)*exp (X t-X s)=l t*r s`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.sine_kernel_eigenvalue`.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.X_log_ratio`,
`«2610.05164v2».SineContinuum.l_positive`, `«2610.05164v2».SineContinuum.r_positive` with the
arguments shown in the proof.
-/
theorem exp_twice_X {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) : exp (2*X t)=l t/r t := by
  rw [X_log_ratio ht]
  rw [show (2:ℝ)*(1/2*log (l t/r t))=log (l t/r t) by ring]
  exact exp_log (div_pos (l_positive ht) (r_positive ht))

/--
Exact identity `sqrt (SineJacobi.phi t)*sqrt (SineJacobi.phi s)*exp (X t-X s)=l t*r s`.

Use: `«2610.05164v2».SineContinuum.exponential_kernel` rewrites with this identity to establish
exact identity `sqrt (SineJacobi.phi t)*sqrt (SineJacobi.phi s)*exp (-|X t-X s|)=2*green t s`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.sine_kernel_eigenvalue`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem ordered_kernel {t s : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) (hs : s ∈ Ioo (0:ℝ) 1) :
    sqrt (SineJacobi.phi t)*sqrt (SineJacobi.phi s)*exp (X t-X s)=l t*r s := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hsq : (sqrt (SineJacobi.phi t)*sqrt (SineJacobi.phi s)*exp (X t-X s))^2=(l t*r s)^2 := by
    rw [mul_pow,mul_pow,sq_sqrt (SineJacobi.phi_pos ht).le,sq_sqrt (SineJacobi.phi_pos hs).le,
      ← exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    rw [show 2*(X t-X s)=2*X t-2*X s by ring,exp_sub,exp_twice_X ht,exp_twice_X hs,
      phi_product,phi_product]
    field_simp [(l_positive hs).ne',(r_positive ht).ne',(r_positive hs).ne']
  have hl : 0 ≤ sqrt (SineJacobi.phi t)*sqrt (SineJacobi.phi s)*exp (X t-X s) := by positivity
  have hr : 0 ≤ l t*r s := mul_nonneg (l_positive ht).le (r_positive hs).le
  nlinarith

/--
The literal transformed exponential kernel is exactly twice the continuous Green kernel,
including its off-diagonal entries.

Exact identity `sqrt (SineJacobi.phi t)*sqrt (SineJacobi.phi s)*exp (-|X t-X s|)=2*green t s`.

Use: `«2610.05164v2».SineContinuum.sineFeature_inner` uses this identity to establish exact
identity `inner ℝ (sineFeature t) (sineFeature s)=2*green t s`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.sine_kernel_eigenvalue`.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.X_strictMono`,
`«2610.05164v2».SineContinuum.ordered_kernel` with the arguments shown in the proof.
-/
theorem exponential_kernel {t s : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) (hs : s ∈ Ioo (0:ℝ) 1) :
    sqrt (SineJacobi.phi t)*sqrt (SineJacobi.phi s)*exp (-|X t-X s|)=2*green t s := by
  -- Use the identities/estimates `«2610.05164v2».SineContinuum.X_strictMono`,
  -- `«2610.05164v2».SineContinuum.ordered_kernel` with the arguments shown in the proof.
  rcases le_total t s with h | h
  · have hX := X_strictMono.monotoneOn ht hs h
    rw [abs_of_nonpos (sub_nonpos.mpr hX),neg_neg,ordered_kernel ht hs]
    simp only [green,min_eq_left h,max_eq_right h]
    ring
  · have hX := X_strictMono.monotoneOn hs ht h
    rw [abs_of_nonneg (sub_nonneg.mpr hX)]
    rw [show -(X t-X s)=X s-X t by ring]
    rw [mul_comm (sqrt (SineJacobi.phi t)) (sqrt (SineJacobi.phi s)),ordered_kernel hs ht]
    simp only [green,min_eq_right h,max_eq_left h]
    ring

/--
Concrete sine features in the already constructed 2610.05164v2 Hilbert space.

Use: `«2610.05164v2».SineContinuum.sineFeature_inner` rewrites with this definition to
establish exact identity `inner ℝ (sineFeature t) (sineFeature s)=2*green t s`.

Article: 2610.05164v2, Lemma 5 via `«2610.05164v2».SineContinuum.green_mercer_uniform`.
-/
def sineFeature (t : ℝ) : FeatureSpace := sqrt (SineJacobi.phi t) • feature (X t)

/--
Exact identity `inner ℝ (sineFeature t) (sineFeature s)=2*green t s`.

Use: `«2610.05164v2».SineContinuum.green_mercer_hasSum` rewrites with this identity to
establish the value of a convergent infinite sum: `HasSum (fun j => upsilon j t*upsilon j s/mu
j) (green t s)`.

Article: 2610.05164v2, Lemma 5 via `«2610.05164v2».SineContinuum.green_mercer_uniform`.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.feature_inner`,
`«2610.05164v2».SineContinuum.exponential_kernel` with the arguments shown in the proof.
-/
theorem sineFeature_inner {t s : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) (hs : s ∈ Ioo (0:ℝ) 1) :
    inner ℝ (sineFeature t) (sineFeature s)=2*green t s := by
  rw [sineFeature,sineFeature,real_inner_smul_left,real_inner_smul_right,feature_inner]
  have h := exponential_kernel ht hs
  nlinarith [h]

/--
Exact identity `‖sineFeature t‖=sqrt (SineJacobi.phi t)`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Lemma 5.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.feature_norm` with the arguments
shown in the proof.
-/
theorem sineFeature_norm (t : ℝ) : ‖sineFeature t‖=sqrt (SineJacobi.phi t) := by rw [sineFeature,norm_smul,feature_norm,mul_one,Real.norm_of_nonneg (sqrt_nonneg _)]

end
end «2610.05164v2».SineContinuum
