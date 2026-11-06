import nesterov.Flow.Kernel
import nesterov.Flow.Extension
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
Article: Appendix B, Equations (cspiral), (cvalue), and Lemma `creduce`.
Use: actual smooth curves in finite-dimensional real Hilbert space, with
their forced gradients and exact decay.  Complex coordinates represent the
orthogonal real two-dimensional planes.
-/

noncomputable section

namespace nesterov.Flow

open scoped InnerProductSpace

def spiralExponent (c γ : ℝ) : ℂ := -(c : ℂ) + (γ : ℂ) * Complex.I

def scalarSpiral (c γ t : ℝ) : ℂ := Complex.exp (spiralExponent c γ * (t : ℂ))

def spiralMultiplier (θ m c γ : ℝ) : ℂ :=
  -(spiralExponent c γ) ^ 2 - (θ : ℂ) * spiralExponent c γ - (m : ℂ)

theorem spiralMultiplier_eq (θ m c γ : ℝ) :
    spiralMultiplier θ m c γ = ((γ ^ 2 - delta θ m c : ℝ) : ℂ) +
      (((2 * c - θ) * γ : ℝ) : ℂ) * Complex.I := by
  dsimp [spiralMultiplier, spiralExponent, delta]
  apply Complex.ext <;> simp [pow_two] <;> ring

theorem hasDerivAt_scalarSpiral (c γ t : ℝ) :
    HasDerivAt (scalarSpiral c γ) (spiralExponent c γ * scalarSpiral c γ t) t := by
  have hh := (((hasDerivAt_id t).ofReal_comp).const_mul (spiralExponent c γ)).cexp
  convert hh using 1
  · dsimp [scalarSpiral]
    rfl
  · dsimp [scalarSpiral]
    simp only [mul_one]
    ring

theorem scalarSpiral_norm (c γ t : ℝ) : ‖scalarSpiral c γ t‖ = Real.exp (-c * t) := by
  simp [scalarSpiral, Complex.norm_exp, spiralExponent]

theorem scalarSpiral_norm_sq (c γ t : ℝ) :
    ‖scalarSpiral c γ t‖ ^ 2 = Real.exp (-2 * c * t) := by
  rw [scalarSpiral_norm, pow_two, ← Real.exp_add]
  congr 1
  ring

theorem scalarSpiral_add (c γ t q : ℝ) :
    scalarSpiral c γ (t + q) = scalarSpiral c γ q * scalarSpiral c γ t := by
  dsimp [scalarSpiral]
  rw [Complex.ofReal_add, mul_add, Complex.exp_add]
  ring

theorem scalarSpiral_zero (c γ : ℝ) : scalarSpiral c γ 0 = 1 := by
  simp [scalarSpiral]

theorem real_inner_complex_mul (u w z : ℂ) :
    ⟪w * u, z * u⟫_ℝ = ‖u‖ ^ 2 * ⟪w, z⟫_ℝ := by
  simp only [real_inner_eq_re_inner, RCLike.inner_apply]
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply]
  ring

theorem scalarSpiral_re (c γ t : ℝ) :
    (scalarSpiral c γ t).re = Real.exp (-c * t) * Real.cos (γ * t) := by
  simp [scalarSpiral, Complex.exp_re, spiralExponent]

theorem scalarSpiral_im (c γ t : ℝ) :
    (scalarSpiral c γ t).im = Real.exp (-c * t) * Real.sin (γ * t) := by
  simp [scalarSpiral, Complex.exp_im, spiralExponent]

theorem scalarSpiral_forced_inner (θ m c γ q : ℝ) :
    ⟪spiralMultiplier θ m c γ, scalarSpiral c γ q - 1⟫_ℝ =
      (γ ^ 2 - delta θ m c) * (Real.exp (-c * q) * Real.cos (γ * q) - 1) +
        (2 * c - θ) * γ * Real.exp (-c * q) * Real.sin (γ * q) := by
  rw [spiralMultiplier_eq]
  simp only [real_inner_eq_re_inner, RCLike.inner_apply]
  simp [pow_two, scalarSpiral_re, scalarSpiral_im]
  ring

theorem scalarSpiral_velocity_inner (θ m c γ t : ℝ) :
    ⟪spiralMultiplier θ m c γ * scalarSpiral c γ t,
      spiralExponent c γ * scalarSpiral c γ t⟫_ℝ =
      Real.exp (-2 * c * t) * (c * delta θ m c + (c - θ) * γ ^ 2) := by
  rw [real_inner_complex_mul, scalarSpiral_norm_sq, spiralMultiplier_eq]
  simp only [real_inner_eq_re_inner, RCLike.inner_apply]
  simp [spiralExponent, pow_two]
  ring

theorem scalarSpiral_ode (θ m c γ t : ℝ) :
    spiralExponent c γ ^ 2 * scalarSpiral c γ t +
      (θ : ℂ) * (spiralExponent c γ * scalarSpiral c γ t) +
      (m : ℂ) * scalarSpiral c γ t +
      spiralMultiplier θ m c γ * scalarSpiral c γ t = 0 := by
  dsimp [spiralMultiplier]
  ring

theorem hasDerivAt_scalarSpiral_velocity (c γ t : ℝ) :
    HasDerivAt (fun s => spiralExponent c γ * scalarSpiral c γ s)
      (spiralExponent c γ ^ 2 * scalarSpiral c γ t) t := by
  convert (hasDerivAt_scalarSpiral c γ t).const_mul (spiralExponent c γ) using 1
  ring

variable {J : Type*} [Fintype J]

/-- Equation (cspiral), the sum of orthogonal spirals. -/
def Spectrum.orbit (ν : Spectrum J) (c t : ℝ) : EuclideanSpace ℂ J :=
  WithLp.toLp 2 (fun j => (Real.sqrt (ν.weight j) : ℂ) * scalarSpiral c (ν.frequency j) t)

def Spectrum.velocity (ν : Spectrum J) (c t : ℝ) : EuclideanSpace ℂ J :=
  WithLp.toLp 2 (fun j => (Real.sqrt (ν.weight j) : ℂ) *
    (spiralExponent c (ν.frequency j) * scalarSpiral c (ν.frequency j) t))

def Spectrum.acceleration (ν : Spectrum J) (c t : ℝ) : EuclideanSpace ℂ J :=
  WithLp.toLp 2 (fun j => (Real.sqrt (ν.weight j) : ℂ) *
    (spiralExponent c (ν.frequency j) ^ 2 * scalarSpiral c (ν.frequency j) t))

def Spectrum.forcedGradient (ν : Spectrum J) (θ m c t : ℝ) : EuclideanSpace ℂ J :=
  WithLp.toLp 2 (fun j => spiralMultiplier θ m c (ν.frequency j) *
    ((Real.sqrt (ν.weight j) : ℂ) * scalarSpiral c (ν.frequency j) t))

/-- Equation (cvalue), the value of the convex remainder along the orbit. -/
def Spectrum.orbitValue (ν : Spectrum J) (θ m c t : ℝ) : ℝ :=
  Real.exp (-2 * c * t) * ∑ j, ν.weight j * atomValue θ m c (ν.frequency j)

theorem Spectrum.hasDerivAt_orbit (ν : Spectrum J) (c t : ℝ) :
    HasDerivAt (ν.orbit c) (ν.velocity c t) t := by
  have hh : HasDerivAt
      (fun s j => (Real.sqrt (ν.weight j) : ℂ) * scalarSpiral c (ν.frequency j) s)
      (fun j => (Real.sqrt (ν.weight j) : ℂ) *
        (spiralExponent c (ν.frequency j) * scalarSpiral c (ν.frequency j) t)) t := by
    exact hasDerivAt_pi.mpr fun j =>
      (hasDerivAt_scalarSpiral c (ν.frequency j) t).const_mul _
  exact ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : J => ℂ)).symm.hasFDerivAt).comp_hasDerivAt t hh

theorem Spectrum.hasDerivAt_velocity (ν : Spectrum J) (c t : ℝ) :
    HasDerivAt (ν.velocity c) (ν.acceleration c t) t := by
  have hh : HasDerivAt
      (fun s j => (Real.sqrt (ν.weight j) : ℂ) *
        (spiralExponent c (ν.frequency j) * scalarSpiral c (ν.frequency j) s))
      (fun j => (Real.sqrt (ν.weight j) : ℂ) *
        (spiralExponent c (ν.frequency j) ^ 2 * scalarSpiral c (ν.frequency j) t)) t := by
    exact hasDerivAt_pi.mpr fun j =>
      (hasDerivAt_scalarSpiral_velocity c (ν.frequency j) t).const_mul _
  exact ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : J => ℂ)).symm.hasFDerivAt).comp_hasDerivAt t hh

theorem Spectrum.orbit_ode (ν : Spectrum J) (θ m c t : ℝ) :
    ν.acceleration c t + θ • ν.velocity c t + m • ν.orbit c t +
      ν.forcedGradient θ m c t = 0 := by
  apply (WithLp.ext_iff 2).mpr
  funext j
  change (Real.sqrt (ν.weight j) : ℂ) *
    (spiralExponent c (ν.frequency j) ^ 2 * scalarSpiral c (ν.frequency j) t) +
      (θ : ℂ) * ((Real.sqrt (ν.weight j) : ℂ) *
        (spiralExponent c (ν.frequency j) * scalarSpiral c (ν.frequency j) t)) +
      (m : ℂ) * ((Real.sqrt (ν.weight j) : ℂ) * scalarSpiral c (ν.frequency j) t) +
      spiralMultiplier θ m c (ν.frequency j) *
        ((Real.sqrt (ν.weight j) : ℂ) * scalarSpiral c (ν.frequency j) t) = 0
  linear_combination (Real.sqrt (ν.weight j) : ℂ) * scalarSpiral_ode θ m c (ν.frequency j) t

theorem Spectrum.orbit_norm_sq (ν : Spectrum J) (c t : ℝ) :
    ‖ν.orbit c t‖ ^ 2 = Real.exp (-2 * c * t) := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Spectrum.orbit, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (ν.weight_nonneg _), scalarSpiral_norm_sq]
  rw [← Finset.sum_mul, ν.weight_sum, one_mul]

theorem Spectrum.orbit_norm (ν : Spectrum J) (c t : ℝ) :
    ‖ν.orbit c t‖ = Real.exp (-c * t) := by
  have hs := ν.orbit_norm_sq c t
  have he : Real.exp (-c * t) ^ 2 = Real.exp (-2 * c * t) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  exact (sq_eq_sq₀ (norm_nonneg _) (Real.exp_pos _).le).mp (hs.trans he.symm)

theorem Spectrum.velocity_norm_sq (ν : Spectrum J) (c t : ℝ) :
    ‖ν.velocity c t‖ ^ 2 = Real.exp (-2 * c * t) *
      ∑ j, ν.weight j * (c ^ 2 + ν.frequency j ^ 2) := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Spectrum.velocity, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (ν.weight_nonneg _), scalarSpiral_norm_sq]
  have hz (γ : ℝ) : ‖spiralExponent c γ‖ ^ 2 = c ^ 2 + γ ^ 2 := by
    rw [Complex.sq_norm]
    simp [spiralExponent, Complex.normSq_apply]
    ring
  simp_rw [hz]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

end nesterov.Flow
