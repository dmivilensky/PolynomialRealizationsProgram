import chebyshev2.SineContinuum.ClosedProfiles
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
Article: chebyshev2, Proposition 2.
Definition 2's sine density and its positive square root.
Use: `chebyshev2.SineContinuum.energy` feeds
`chebyshev2.LocalObstruction.densityEnergy_sine` (density Energy sine).
-/
namespace chebyshev2.SineContinuum
noncomputable section
open Set Real MeasureTheory
set_option backward.isDefEq.respectTransparency false

/--
Exact identity `X '' Ioo (0:ℝ) 1=univ`.

Use: `chebyshev2.SineContinuum.coordinate_integrable_iff` rewrites with this identity to
establish integrability of the displayed function: `Integrable g ↔ IntegrableOn (fun t =>
(SineJacobi.phi t)⁻¹*g (X t)) (Ioo (0:ℝ) 1)`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.energy`.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.X_surjective` with the
arguments shown in the proof.
-/
theorem X_image_univ : X '' Ioo (0:ℝ) 1=univ :=
  eq_univ_iff_forall.mpr (fun x => X_surjective (mem_univ x))

/--
The change of variables in Definition 2 on the entire real line.

Exact identity `(∫ x, g x)=∫ t in Ioo (0:ℝ) 1, (SineJacobi.phi t)⁻¹*g (X t)`.

Use: `chebyshev2.SineContinuum.energy` rewrites with this identity to establish exact
identity `(∫ x, m x*sqrt (m x))=SineJacobi.energy`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.energy`.

Proof: Use the proved fundamental theorem of calculus with its explicit integrability and
endpoint hypotheses.
-/
theorem coordinate_integral (g : ℝ → ℝ) :
    (∫ x, g x)=∫ t in Ioo (0:ℝ) 1, (SineJacobi.phi t)⁻¹*g (X t) := by
  have h := integral_image_eq_integral_deriv_smul_of_monotoneOn measurableSet_Ioo
    (fun _ ht => (X_derivative ht).hasDerivWithinAt) X_strictMono.monotoneOn g
  rw [X_image_univ,setIntegral_univ] at h
  simpa only [smul_eq_mul] using h

/--
Integrability of the displayed function: `Integrable g ↔ IntegrableOn (fun t => (SineJacobi.phi
t)⁻¹*g (X t)) (Ioo (0:ℝ) 1)`.

Use: `chebyshev2.SineContinuum.energy_integrable` uses this integrability result to
establish integrability of the displayed function: `Integrable (fun x => m x*sqrt (m x))`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.X_derivative`,
`chebyshev2.SineContinuum.X_strictMono`, `chebyshev2.SineContinuum.X_image_univ` with
the arguments shown in the proof.
-/
theorem coordinate_integrable_iff (g : ℝ → ℝ) :
    Integrable g ↔ IntegrableOn (fun t => (SineJacobi.phi t)⁻¹*g (X t)) (Ioo (0:ℝ) 1) := by
  have h := integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn measurableSet_Ioo
    (fun _ ht => (X_derivative ht).hasDerivWithinAt) X_strictMono.monotoneOn g
  rw [X_image_univ,integrableOn_univ] at h
  simpa only [smul_eq_mul] using h

/--
Definition 2's sine density and its positive square root.

Use: `chebyshev2.SineContinuum.m` uses this definition in the displayed construction of
`m`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Definition 2.
-/
def n (x : ℝ) : ℝ := SineJacobi.phi (T x)
/--
Defines `m` of type `ℝ` by `n x^2`.

Use:
`_private.chebyshev2.SineContinuum.Density.0.chebyshev2.SineContinuum.integrand_energy`
uses this definition to establish the identity `(SineJacobi.phi t)⁻¹*(m (X t)*sqrt (m (X
t)))=SineJacobi.phi t^2`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.
-/
def m (x : ℝ) : ℝ := n x^2

/--
The stated quantitative bound `0 < n x`.

Use: `chebyshev2.SineContinuum.m_positive` uses this bound to establish the stated
quantitative bound `0 < m x`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.

Proof: Use the identities/estimates `chebyshev2.SineJacobi.phi_pos`,
`chebyshev2.SineContinuum.T_mem` with the arguments shown in the proof.
-/
theorem n_positive (x : ℝ) : 0 < n x := SineJacobi.phi_pos (T_mem x)
/--
The stated quantitative bound `0 < m x`.

Use: `chebyshev2.LocalObstruction.sineGreenScale_formula` rewrites with this bound to
establish the identity stated in that declaration.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.n_positive` with the
arguments shown in the proof.
-/
theorem m_positive (x : ℝ) : 0 < m x := sq_pos_of_pos (n_positive x)
/--
Exact identity `sqrt (m x)=n x`.

Use:
`_private.chebyshev2.SineContinuum.Density.0.chebyshev2.SineContinuum.integrand_energy`
rewrites with this identity to establish the identity `(SineJacobi.phi t)⁻¹*(m (X t)*sqrt (m
(X t)))=SineJacobi.phi t^2`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sqrt_mass`.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.n_positive` with the
arguments shown in the proof.
-/
theorem sqrt_m (x : ℝ) : sqrt (m x)=n x := sqrt_sq (n_positive x).le

/--
Continuity of the displayed function: `Continuous n`.

Use: `chebyshev2.SineContinuum.m_continuous` uses this continuity result to establish
continuity of the displayed function: `Continuous m`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.phi_continuousOn`,
`chebyshev2.SineContinuum.T_continuous`, `chebyshev2.SineContinuum.T_mem` with the
arguments shown in the proof.
-/
theorem n_continuous : Continuous n := phi_continuousOn.comp_continuous T_continuous
  (fun x => ⟨(T_mem x).1.le,(T_mem x).2.le⟩)
/--
Continuity of the displayed function: `Continuous m`.

Use: `chebyshev2.LocalObstruction.curveDensity_uniform_small` uses this continuity result
to prove the eventual or almost-everywhere assertion `∀ᶠ t in 𝓝 (0:ℝ), ∀
x, |curveDensity h w t x-m x|<ε`.

Article: chebyshev2, Theorem 6.1 via
`chebyshev2.LocalObstruction.groundObservationWitness`.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.n_continuous` with the
arguments shown in the proof.
-/
theorem m_continuous : Continuous m := n_continuous.pow 2

/--
Exact identity `n (X t)=SineJacobi.phi t`.

Use:
`_private.chebyshev2.SineContinuum.Density.0.chebyshev2.SineContinuum.integrand_energy`
rewrites with this identity to establish the identity `(SineJacobi.phi t)⁻¹*(m (X t)*sqrt (m
(X t)))=SineJacobi.phi t^2`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.n_theta`.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.T_X` with the arguments shown
in the proof.
-/
theorem n_X {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) : n (X t)=SineJacobi.phi t := by rw [n,T_X ht]
/--
Exact identity `m (X t)=SineJacobi.phi t^2`.

Use:
`_private.chebyshev2.SineContinuum.Density.0.chebyshev2.SineContinuum.integrand_energy`
rewrites with this identity to establish the identity `(SineJacobi.phi t)⁻¹*(m (X t)*sqrt (m
(X t)))=SineJacobi.phi t^2`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.energy`.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.n_X` with the arguments shown
in the proof.
-/
theorem m_X {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) : m (X t)=SineJacobi.phi t^2 := by rw [m,n_X ht]

/--
Exact identity `n (-x)=n x`.

Use: `chebyshev2.SineContinuum.m_even` rewrites with this identity to establish exact
identity `m (-x)=m x`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.n_theta`.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.T_reflect`,
`chebyshev2.SineContinuum.phi_reflect` with the arguments shown in the proof.
-/
theorem n_even (x : ℝ) : n (-x)=n x := by rw [n,T_reflect,phi_reflect]; rfl
/--
Exact identity `m (-x)=m x`.

Use: `chebyshev2.LocalObstruction.sineGreenScale_formula` rewrites with this identity to
establish the identity stated in that declaration.

Article: chebyshev2, Theorem 6.1 via
`chebyshev2.LocalObstruction.groundObservationWitness`.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.n_even` with the arguments
shown in the proof.
-/
theorem m_even (x : ℝ) : m (-x)=m x := by rw [m,n_even]; rfl

/--
Exact identity `(SineJacobi.phi t)⁻¹*n (X t)=1`.

Use: `chebyshev2.SineContinuum.n_integrable` uses this identity to establish integrability
of the displayed function: `Integrable n`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sqrt_mass`.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.n_X`,
`chebyshev2.SineJacobi.phi_pos` with the arguments shown in the proof.
-/
private theorem integrand_n {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    (SineJacobi.phi t)⁻¹*n (X t)=1 := by rw [n_X ht,inv_mul_cancel₀ (SineJacobi.phi_pos ht).ne']
/--
Exact identity `(SineJacobi.phi t)⁻¹*m (X t)=SineJacobi.phi t`.

Use: `chebyshev2.SineContinuum.m_integrable` uses this identity to establish integrability
of the displayed function: `Integrable m`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.mass`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
private theorem integrand_m {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    (SineJacobi.phi t)⁻¹*m (X t)=SineJacobi.phi t := by
  rw [m_X ht]
  field_simp
/--
Exact identity `(SineJacobi.phi t)⁻¹*(m (X t)*sqrt (m (X t)))=SineJacobi.phi t^2`.

Use: `chebyshev2.SineContinuum.energy` uses this identity to establish the identity `(∫
x, m x*sqrt (m x))=SineJacobi.energy`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.energy`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
private theorem integrand_energy {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    (SineJacobi.phi t)⁻¹*(m (X t)*sqrt (m (X t)))=SineJacobi.phi t^2 := by
  rw [sqrt_m,m_X ht,n_X ht]
  field_simp

/--
Integrability of the displayed function: `Integrable n`.

Use: `chebyshev2.LocalObstruction.curveAmplitude_integrable` uses this integrability result
to establish integrability of the displayed function: `Integrable (curveAmplitude h w t)`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.coordinate_integrable_iff`,
`_private.chebyshev2.SineContinuum.Density.0.chebyshev2.SineContinuum.integrand_n` with
the arguments shown in the proof.
-/
theorem n_integrable : Integrable n := by
  apply (coordinate_integrable_iff n).mpr
  have hi : IntegrableOn (fun _ : ℝ => (1:ℝ)) (Ioo (0:ℝ) 1) :=
    integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  apply IntegrableOn.congr_fun hi _ measurableSet_Ioo
  intro t ht
  exact (integrand_n ht).symm

/--
Integrability of the displayed function: `Integrable m`.

Use: `chebyshev2.LocalObstruction.curveDensity_integrable` uses this integrability result
to establish integrability of the displayed function: `Integrable (curveDensity h w t)`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.coordinate_integrable_iff`,
`chebyshev2.SineContinuum.phi_continuousOn`,
`_private.chebyshev2.SineContinuum.Density.0.chebyshev2.SineContinuum.integrand_m` with
the arguments shown in the proof.
-/
theorem m_integrable : Integrable m := by
  apply (coordinate_integrable_iff m).mpr
  have hi : IntegrableOn SineJacobi.phi (Icc (0:ℝ) 1) := phi_continuousOn.integrableOn_compact isCompact_Icc
  apply IntegrableOn.congr_fun (hi.mono_set Ioo_subset_Icc_self) _ measurableSet_Ioo
  intro t ht
  exact (integrand_m ht).symm

/--
Integrability of the displayed function: `Integrable (fun x => m x*sqrt (m x))`.

Use: `chebyshev2.LocalObstruction.sine_cube_integrable` uses this integrability result to
establish integrability of the displayed function: `Integrable (fun x => n x^3)`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.coordinate_integrable_iff`,
`chebyshev2.SineContinuum.phi_continuousOn`,
`_private.chebyshev2.SineContinuum.Density.0.chebyshev2.SineContinuum.integrand_energy`
with the arguments shown in the proof.
-/
theorem energy_integrable : Integrable (fun x => m x*sqrt (m x)) := by
  apply (coordinate_integrable_iff _).mpr
  have hi : IntegrableOn (fun t => SineJacobi.phi t^2) (Icc (0:ℝ) 1) :=
    (phi_continuousOn.pow 2).integrableOn_compact isCompact_Icc
  apply IntegrableOn.congr_fun (hi.mono_set Ioo_subset_Icc_self) _ measurableSet_Ioo
  intro t ht
  exact (integrand_energy ht).symm

/--
Exact identity `(∫ x, sqrt (m x))=1`.

Use: `chebyshev2.LocalObstruction.curveAmplitude_mass` uses this identity to establish
exact identity `(∫ x, curveAmplitude h w t x)=1`.

Article: chebyshev2, Proposition 2.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.sqrt_m`,
`chebyshev2.SineContinuum.coordinate_integral`,
`_private.chebyshev2.SineContinuum.Density.0.chebyshev2.SineContinuum.integrand_n` with
the arguments shown in the proof.
-/
theorem sqrt_mass : (∫ x, sqrt (m x))=1 := by
  simp only [sqrt_m]
  rw [coordinate_integral n]
  have he : (∫ t in Ioo (0:ℝ) 1, (SineJacobi.phi t)⁻¹*n (X t))=∫ _t in Ioo (0:ℝ) 1, (1:ℝ) :=
    setIntegral_congr_fun measurableSet_Ioo (fun _ ht => integrand_n ht)
  rw [he]
  norm_num

/--
Exact identity `(∫ x, m x)=1`.

Use: `chebyshev2.LocalObstruction.curveDensity_mass` uses this identity to establish
establishes the stated eventual or almost-everywhere assertion `∀ᶠ t in 𝓝 (0:ℝ), (∫ x,
curveDensity h w t x)=1`.

Article: chebyshev2, Proposition 2.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.coordinate_integral`,
`_private.chebyshev2.SineContinuum.Density.0.chebyshev2.SineContinuum.integrand_m`,
`chebyshev2.SineJacobi.phi_integral` with the arguments shown in the proof.
-/
theorem mass : (∫ x, m x)=1 := by
  rw [coordinate_integral m]
  have he : (∫ t in Ioo (0:ℝ) 1, (SineJacobi.phi t)⁻¹*m (X t))=∫ t in Ioo (0:ℝ) 1, SineJacobi.phi t :=
    setIntegral_congr_fun measurableSet_Ioo (fun _ ht => integrand_m ht)
  rw [he,← integral_Icc_eq_integral_Ioo,integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),SineJacobi.phi_integral]

/--
Exact identity `(∫ x, m x*sqrt (m x))=SineJacobi.energy`.

Use: `chebyshev2.LocalObstruction.densityEnergy_sine` uses this identity to establish exact
identity `densityEnergy m=chebyshev2.SineJacobi.energy`.

Article: chebyshev2, Proposition 2.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.coordinate_integral`,
`_private.chebyshev2.SineContinuum.Density.0.chebyshev2.SineContinuum.integrand_energy`
with the arguments shown in the proof.
-/
theorem energy : (∫ x, m x*sqrt (m x))=SineJacobi.energy := by
  rw [coordinate_integral]
  have he : (∫ t in Ioo (0:ℝ) 1, (SineJacobi.phi t)⁻¹*(m (X t)*sqrt (m (X t))))=
      ∫ t in Ioo (0:ℝ) 1, SineJacobi.phi t^2 :=
    setIntegral_congr_fun measurableSet_Ioo (fun _ ht => integrand_energy ht)
  rw [he,← integral_Icc_eq_integral_Ioo,integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
  rfl

end
end chebyshev2.SineContinuum
