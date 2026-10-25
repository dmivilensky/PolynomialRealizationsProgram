import chebyshev2.Filters.FredholmJost
import chebyshev2.Filters.NonlinearEnergy
import chebyshev2.Filters.Relaxation
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
Article: chebyshev2, Proposition 3.
The growing right-hand Jost coefficient is literally the Fredholm determinant, with the decaying
coefficient given by its original integral.
Use: `chebyshev2.Filters.nonlinear_square_mass` feeds
`chebyshev2.Calibration.Data.calibrationFilter_square_mass` (Equation (14), with the actual
Fredholm logarithm at the moving scale).
Proof chain: `chebyshev2.Calibration.Data.energy_ge_spectral_bound` — chebyshev2, Theorem 3.5;
Pointwise cubic-conjugate criterion, gauge invariance and regular price.
-/
namespace chebyshev2.Filters
noncomputable section
open Set MeasureTheory Real Filter chebyshev2.Continuum chebyshev2.Sobolev
open scoped Topology BoundedContinuousFunction
set_option backward.isDefEq.respectTransparency false

/--
The actual continuous Riccati filter, with its usual uniform norm.

Use: `chebyshev2.Filters.nonlinear_derivative_L1_spectral` uses this definition to
establish the stated quantitative bound `(∫ x, ‖s*m x-2*nonlinear s m x-(nonlinear s m x)^2‖) ≤
s*(∫ x, m x)+(2+‖nonlinearBounded hm hn hs‖)*logDeterminant (kernelEigenvalue hm hn) s`.

Article: chebyshev2, Proposition 3.
-/
def nonlinearBounded {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (nonlinear s m) (nonlinear_continuous hm hn hs)
    (s*∫ t, m t) (fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (nonlinear_bounds hm hn hs x).1]
      exact nonlinear_uniform_bound hm hn hs x)

/--
Exact identity `nonlinearBounded hm hn hs x=nonlinear s m x`.

Use: registered as a simplification rule for the displayed expression. The rule remains
available even when kernel reduction eliminates an explicit reference to this lemma.

Article: chebyshev2, Proposition 3.

Proof: The identity follows by unfolding the definitions; no estimate or limiting argument is
involved.
-/
@[simp] theorem nonlinearBounded_apply {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) (x : ℝ) : nonlinearBounded hm hn hs x=nonlinear s m x := rfl

/--
Proposition 3(ii)'s printed L1 derivative estimate, with the actual uniform norm and the actual
spectral observation H_m(s).

The stated quantitative bound `(∫ x, ‖s*m x-2*nonlinear s m x-(nonlinear s m x)^2‖) ≤ s*(∫ x, m
x)+(2+‖nonlinearBounded hm hn hs‖)*logDeterminant (kernelEigenvalue hm hn) s`.

Use: a standalone supporting bound for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Proposition 3.

Proof: Use the identities/estimates `chebyshev2.Filters.nonlinear_derivative_L1`,
`chebyshev2.Filters.log_transmission_eq_logDeterminant` with the arguments shown in the
proof.
-/
theorem nonlinear_derivative_L1_spectral {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) :
    (∫ x, ‖s*m x-2*nonlinear s m x-(nonlinear s m x)^2‖) ≤
      s*(∫ x, m x)+(2+‖nonlinearBounded hm hn hs‖)*logDeterminant (kernelEigenvalue hm hn) s := by
  -- Use the identities/estimates `chebyshev2.Filters.nonlinear_derivative_L1`,
  -- `chebyshev2.Filters.log_transmission_eq_logDeterminant` with the arguments shown in
  -- the proof.
  have h := nonlinear_derivative_L1 hm hn hs
    (fun x => (nonlinearBounded hm hn hs).apply_le_norm x)
  rwa [log_transmission_eq_logDeterminant hm hn hs] at h

/--
Integrated Riccati equation. This also supplies the square observation used by calibration
after rescaling the filter.

Exact identity `(∫ x, (nonlinear s m x)^2)=s*(∫ x, m x)-2*logDeterminant (kernelEigenvalue hm
hn) s`.

Use: `chebyshev2.Calibration.Data.calibrationFilter_square_mass` rewrites with this
identity to establish the identity stated in that declaration.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the proved fundamental theorem of calculus with its explicit integrability and
endpoint hypotheses.
-/
theorem nonlinear_square_mass {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) :
    (∫ x, (nonlinear s m x)^2)=s*(∫ x, m x)-2*logDeterminant (kernelEigenvalue hm hn) s := by
  -- Use the proved fundamental theorem of calculus with its explicit integrability and
  -- endpoint hypotheses.
  have h := locallyAC_integral_derivative_zero (nonlinear_integrable hm hn hs)
    (nonlinear_derivative_integrable hm hn hs) (nonlinear_locallyAC hm hn hs)
    (nonlinear_derivative hm hn hs)
  rw [integral_sub (f := fun x => s*m x-2*nonlinear s m x)
      ((hm.const_mul s).sub ((nonlinear_integrable hm hn hs).const_mul 2))
      (nonlinear_square_integrable hm hn hs),
    integral_sub (hm.const_mul s) ((nonlinear_integrable hm hn hs).const_mul 2),
    integral_const_mul,integral_const_mul,nonlinear_mass_eq_logDeterminant hm hn hs] at h
  linarith

/--
Convergence along the specified source filter to the specified limit: `Tendsto (jost s m) atTop
(𝓝 (exp (logDeterminant (kernelEigenvalue hm hn) s)))`.

Use: a standalone supporting limit for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Proposition 3.

Proof: Use the identities/estimates `chebyshev2.Continuum.fredholmDeterminant_eq_exp`,
`chebyshev2.Continuum.PositiveSpectralData.eigenvalue_summable`,
`chebyshev2.Continuum.PositiveSpectralData.eigenvalue_nonneg` with the arguments shown in
the proof.
-/
theorem jost_right_limit_exp_logDeterminant {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) : Tendsto (jost s m) atTop
      (𝓝 (exp (logDeterminant (kernelEigenvalue hm hn) s))) := by
  rw [← fredholmDeterminant_eq_exp (a := kernelEigenvalue hm hn)
    (kernelSpectralData hm hn).eigenvalue_summable (kernelSpectralData hm hn).eigenvalue_nonneg hs]
  exact jost_right_limit_fredholm hm hn hs

/--
The growing right-hand Jost coefficient is literally the Fredholm determinant, with the
decaying coefficient given by its original integral.

Exact identity `exp x*jost s m x=fredholmDeterminant (kernelEigenvalue hm hn) s*exp x- (s/2*(∫
t, exp (2*t)*(m t*jost s m t)))*exp (-x)`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Proposition 3.

Proof: Use the identities/estimates
`chebyshev2.Filters.transmission_eq_fredholmDeterminant`,
`chebyshev2.Filters.jost_right_of_density_zero` with the arguments shown in the proof.
-/
theorem jost_right_of_density_zero_fredholm {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) (x : ℝ) (hz : ∀ t, x < t → m t=0) :
    exp x*jost s m x=fredholmDeterminant (kernelEigenvalue hm hn) s*exp x-
      (s/2*(∫ t, exp (2*t)*(m t*jost s m t)))*exp (-x) := by
  rw [← transmission_eq_fredholmDeterminant hm hn hs]
  exact jost_right_of_density_zero hm hn hs x hz

/--
Exact identity `m.H s=∫ x, nonlinear s m.value x`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Proposition 3.

Proof: Use the identities/estimates `chebyshev2.Filters.nonlinear_mass_eq_logDeterminant`
with the arguments shown in the proof.
-/
theorem CompactDensity.H_eq_filter_mass (m : CompactDensity) {s : ℝ} (hs : 0 ≤ s) :
    m.H s=∫ x, nonlinear s m.value x :=
  (nonlinear_mass_eq_logDeterminant m.integrable m.nonneg hs).symm

end
end chebyshev2.Filters
