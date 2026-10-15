import «2610.05164v2».Comparison.SymmetricTrace
import «2610.05164v2».Calibration.ChainRule

/-!
Article: 2610.05164v2, Theorem 3.4.
Square energy expressed using the opposite causal filter, through actual total derivatives.
Use: `«2610.05164v2».Comparison.causal_square_right_mass` feeds
`«2610.05164v2».Comparison.Profile.traceG_zero` (trace G zero).
Proof chain: `«2610.05164v2».Comparison.Profile.signed_trace_comparison` — 2610.05164v2, Theorem
3.4; Signed determinant and square-trace comparisons.
-/
namespace «2610.05164v2».Comparison
noncomputable section
open Set MeasureTheory Filter Real «2610.05164v2».Filters «2610.05164v2».Calibration
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/--
Defines `rightCausal` of type `ℝ` by `causal 2 (reflected m) (-x)`.

Use: `«2610.05164v2».Comparison.causal_opposite_density_mass` uses this definition to establish
exact identity `(∫ x, m x*causal 2 m x)=(∫ x, m x*rightCausal m x)`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.
-/
def rightCausal (m : ℝ → ℝ) (x : ℝ) : ℝ := causal 2 (reflected m) (-x)

variable {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x) (hc : Continuous m)
include hm hn hc

omit hn in
/--
The actual derivative at the stated point: `HasDerivAt (rightCausal m) (-m x+2*rightCausal m x)
x`.

Use: `«2610.05164v2».Comparison.causal_opposite_density_mass` uses this derivative formula to
establish exact identity `(∫ x, m x*causal 2 m x)=(∫ x, m x*rightCausal m x)`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.causal_hasDerivAt`,
`«2610.05164v2».Filters.reflected_integrable`, `«2610.05164v2».Filters.reflected_continuous`
with the arguments shown in the proof.
-/
theorem rightCausal_derivative (x : ℝ) :
    HasDerivAt (rightCausal m) (-m x+2*rightCausal m x) x := by
  -- Use the identities/estimates `«2610.05164v2».Filters.causal_hasDerivAt`,
  -- `«2610.05164v2».Filters.reflected_integrable`,
  -- `«2610.05164v2».Filters.reflected_continuous` with the arguments shown in the proof.
  have h := (causal_hasDerivAt (reflected_integrable hm) (reflected_continuous hc)
    (by norm_num : (0:ℝ) ≤ 2) (-x)).comp x (hasDerivAt_neg x)
  convert h using 1
  · rfl
  · simp only [reflected,neg_neg]
    dsimp only [rightCausal]
    ring

omit hn in
/--
Smoothness to the stated order: `ContDiff ℝ 1 (rightCausal m)`.

Use: `«2610.05164v2».Comparison.causal_opposite_density_mass` uses this assertion to establish
exact identity `(∫ x, m x*causal 2 m x)=(∫ x, m x*rightCausal m x)`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.causal_c1`,
`«2610.05164v2».Filters.reflected_integrable`, `«2610.05164v2».Filters.reflected_continuous`
with the arguments shown in the proof.
-/
theorem rightCausal_c1 : ContDiff ℝ 1 (rightCausal m) :=
  (causal_c1 (reflected_integrable hm) (reflected_continuous hc)
    (by norm_num : (0:ℝ) ≤ 2)).comp contDiff_neg

omit hn hc in
/--
Convergence along the specified source filter to the specified limit: `Tendsto (rightCausal m)
atBot (𝓝 0) ∧ Tendsto (rightCausal m) atTop (𝓝 0)`.

Use: `«2610.05164v2».Comparison.causal_opposite_density_mass` uses this limit to establish
exact identity `(∫ x, m x*causal 2 m x)=(∫ x, m x*rightCausal m x)`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.causal_tendsto_atTop`,
`«2610.05164v2».Filters.reflected_integrable`, `«2610.05164v2».Filters.causal_tendsto_atBot`
with the arguments shown in the proof.
-/
theorem rightCausal_limits : Tendsto (rightCausal m) atBot (𝓝 0) ∧ Tendsto (rightCausal m) atTop (𝓝 0) :=
  ⟨(causal_tendsto_atTop (by norm_num : (0:ℝ) < 2) (reflected_integrable hm)).comp tendsto_neg_atBot_atTop,
   (causal_tendsto_atBot (by norm_num : (0:ℝ) ≤ 2) (reflected_integrable hm)).comp tendsto_neg_atTop_atBot⟩

omit hc in
/--
Integrability of the displayed function: `Integrable (fun x => m x*causal 2 m x)`.

Use: `«2610.05164v2».Comparison.causal_opposite_density_mass` uses this integrability result to
establish exact identity `(∫ x, m x*causal 2 m x)=(∫ x, m x*rightCausal m x)`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.causal_continuous`,
`«2610.05164v2».Filters.causal_nonneg`, `«2610.05164v2».Filters.causal_le_mass` with the
arguments shown in the proof.
-/
theorem density_mul_causal_integrable : Integrable (fun x => m x*causal 2 m x) := by
  apply hm.mul_bdd (c := ∫ x, m x)
    (causal_continuous (by norm_num : (0:ℝ) ≤ 2) hm).aestronglyMeasurable
  exact Eventually.of_forall (fun x => by
    rw [Real.norm_of_nonneg (causal_nonneg (Eventually.of_forall hn) x)]
    exact causal_le_mass (by norm_num : (0:ℝ) ≤ 2) hm (Eventually.of_forall hn) x)

omit hc in
/--
Integrability of the displayed function: `Integrable (fun x => m x*rightCausal m x)`.

Use: `«2610.05164v2».Comparison.causal_opposite_density_mass` uses this integrability result to
establish exact identity `(∫ x, m x*causal 2 m x)=(∫ x, m x*rightCausal m x)`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».Filters.causal_continuous`,
`«2610.05164v2».Filters.reflected_integrable`, `«2610.05164v2».Filters.causal_nonneg` with the
arguments shown in the proof.
-/
theorem density_mul_rightCausal_integrable : Integrable (fun x => m x*rightCausal m x) := by
  apply hm.mul_bdd (c := ∫ x, reflected m x)
    ((causal_continuous (by norm_num : (0:ℝ) ≤ 2) (reflected_integrable hm)).comp continuous_neg).aestronglyMeasurable
  exact Eventually.of_forall (fun x => by
    simp only [Function.comp_apply]
    rw [Real.norm_of_nonneg (causal_nonneg (Eventually.of_forall (reflected_nonneg hn)) (-x))]
    exact causal_le_mass (by norm_num : (0:ℝ) ≤ 2) (reflected_integrable hm)
      (Eventually.of_forall (reflected_nonneg hn)) (-x))

/--
Exact identity `(∫ x, (causal 2 m x)^2)=(1/2:ℝ)*(∫ x, m x*causal 2 m x)`.

Use: `«2610.05164v2».Comparison.causal_square_right_mass` rewrites with this identity to
establish exact identity `(∫ x, (causal 2 m x)^2)=(1/2:ℝ)*(∫ x, m x*rightCausal m x)`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the proved fundamental theorem of calculus with its explicit integrability and
endpoint hypotheses.
-/
theorem causal_square_density_mass :
    (∫ x, (causal 2 m x)^2)=(1/2:ℝ)*(∫ x, m x*causal 2 m x) := by
  -- Use the proved fundamental theorem of calculus with its explicit integrability and
  -- endpoint hypotheses.
  let D : ℝ → ℝ := fun x => 2*(m x*causal 2 m x)-4*(causal 2 m x)^2
  -- Establish hi as the integrability justification for the later integral estimates or
  -- changes of order.
  have hi : Integrable D := ((density_mul_causal_integrable hm hn).const_mul 2).sub
    ((causal_square_integrable hm hn).const_mul 4)
  have hd : ∀ᵐ x, HasDerivAt (fun x => (causal 2 m x)^2) (D x) x :=
    Eventually.of_forall (fun x => by
      convert (causal_hasDerivAt hm hc (by norm_num : (0:ℝ) ≤ 2) x).pow 2 using 1
      dsimp [D]
      ring)
  have h := integral_derivative_eq_limits
    (fun a b => ((causal_c1 hm hc (by norm_num : (0:ℝ) ≤ 2)).pow 2).contDiffOn.absolutelyContinuousOnInterval
      (a := a) (b := b)) hd hi
    (by simpa using (causal_tendsto_atBot (by norm_num : (0:ℝ) ≤ 2) hm).pow 2)
    (by simpa using (causal_tendsto_atTop (by norm_num : (0:ℝ) < 2) hm).pow 2)
  have he : (∫ x, D x)=2*(∫ x, m x*causal 2 m x)-4*(∫ x, (causal 2 m x)^2) := by
    change (∫ x, 2*(m x*causal 2 m x)-4*(causal 2 m x)^2)=_
    rw [integral_sub ((density_mul_causal_integrable hm hn).const_mul 2)
      ((causal_square_integrable hm hn).const_mul 4),integral_const_mul,integral_const_mul]
  rw [he] at h
  linarith

/--
Exact identity `(∫ x, m x*causal 2 m x)=(∫ x, m x*rightCausal m x)`.

Use: `«2610.05164v2».Comparison.causal_square_right_mass` rewrites with this identity to
establish exact identity `(∫ x, (causal 2 m x)^2)=(1/2:ℝ)*(∫ x, m x*rightCausal m x)`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the proved fundamental theorem of calculus with its explicit integrability and
endpoint hypotheses.
-/
theorem causal_opposite_density_mass :
    (∫ x, m x*causal 2 m x)=(∫ x, m x*rightCausal m x) := by
  -- Use the proved fundamental theorem of calculus with its explicit integrability and
  -- endpoint hypotheses.
  let D : ℝ → ℝ := fun x => m x*rightCausal m x-m x*causal 2 m x
  -- Establish hi as the integrability justification for the later integral estimates or
  -- changes of order.
  have hi : Integrable D := (density_mul_rightCausal_integrable hm hn).sub (density_mul_causal_integrable hm hn)
  have hd : ∀ᵐ x, HasDerivAt (fun x => causal 2 m x*rightCausal m x) (D x) x :=
    Eventually.of_forall (fun x => by
      convert (causal_hasDerivAt hm hc (by norm_num : (0:ℝ) ≤ 2) x).mul
        (rightCausal_derivative hm hc x) using 1
      dsimp [D]
      ring)
  have h := integral_derivative_eq_limits
    (fun a b => ((causal_c1 hm hc (by norm_num : (0:ℝ) ≤ 2)).mul
      (rightCausal_c1 hm hc)).contDiffOn.absolutelyContinuousOnInterval (a := a) (b := b)) hd hi
    (by simpa using (causal_tendsto_atBot (by norm_num : (0:ℝ) ≤ 2) hm).mul (rightCausal_limits hm).1)
    (by simpa using (causal_tendsto_atTop (by norm_num : (0:ℝ) < 2) hm).mul (rightCausal_limits hm).2)
  have he : (∫ x, D x)=(∫ x, m x*rightCausal m x)-(∫ x, m x*causal 2 m x) :=
    integral_sub (density_mul_rightCausal_integrable hm hn) (density_mul_causal_integrable hm hn)
  rw [he] at h
  linarith

/--
Exact identity `(∫ x, (causal 2 m x)^2)=(1/2:ℝ)*(∫ x, m x*rightCausal m x)`.

Use: `«2610.05164v2».Comparison.Profile.traceG_zero` uses this identity to establish exact
identity `P.traceG hκ 0=(∫ x, (linear ((P.speedData hκ).density_integrable hκ) ((P.speedData
hκ).density_nonneg hκ) x)^2)`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».Comparison.causal_square_density_mass`,
`«2610.05164v2».Comparison.causal_opposite_density_mass` with the arguments shown in the proof.
-/
theorem causal_square_right_mass :
    (∫ x, (causal 2 m x)^2)=(1/2:ℝ)*(∫ x, m x*rightCausal m x) := by rw [causal_square_density_mass hm hn hc,causal_opposite_density_mass hm hn hc]

end
end «2610.05164v2».Comparison
