import jacobi.Oscillation.Restoring

/-!
Article: jacobi, Proposition B.1.
The original value/slope state is normalized by its actual positive
amplitude. Its true derivatives give a literal rotating unit frame and
the exact phase speed. These identities precede, rather than assume,
existence of a continuous Pruefer angle.
Use: proves the actual normalized cosine derivative without any phase hypothesis.
-/
namespace jacobi.Oscillation
noncomputable section
open Real Set MeasureTheory
set_option backward.isDefEq.respectTransparency false

/-- Exact scalar quotient algebra for the cosine coordinate of a restoring state.
Use: proves the actual normalized cosine derivative without any phase hypothesis.
Article: jacobi, Proposition B.1.
Proof: clear only the nonzero actual amplitude and use its exact energy-square identity. -/
theorem cosine_quotient_algebra {f g q r : ℝ} (hr : r≠0) (he : r^2=f^2+g^2) :
    ((-q*f)*r-g*((1-q)*f*g/r))/r^2= -((g^2+q*f^2)/r^2)*(f/r) := by
  field_simp [hr]
  linear_combination -q*f*he

/-- Exact scalar quotient algebra for the sine coordinate of a restoring state.
Use: proves the actual normalized sine derivative before any angle is introduced.
Article: jacobi, Proposition B.1.
Proof: clear the genuine nonzero amplitude denominator and use the original state-energy identity. -/
theorem sine_quotient_algebra {f g q r : ℝ} (hr : r≠0) (he : r^2=f^2+g^2) :
    (g*r-f*((1-q)*f*g/r))/r^2=((g^2+q*f^2)/r^2)*(g/r) := by
  field_simp [hr]
  linear_combination g*he

namespace RestoringSolution
variable {I : Set ℝ} (S : RestoringSolution I)

/-- The literal normalized slope coordinate of the original restoring state.
Use: becomes the cosine coordinate of the genuine continuous Pruefer phase.
Article: jacobi, Proposition B.1.
-/
def unitCos (x : ℝ) : ℝ := S.slope x/S.amplitude x

/-- The literal normalized value coordinate of the original restoring state.
Use: becomes the sine coordinate and retains exactly the original solution zero set.
Article: jacobi, Proposition B.1.
-/
def unitSin (x : ℝ) : ℝ := S.value x/S.amplitude x

/-- The actual normalized-state rotation speed, defined directly from the original solution and coefficient.
Use: its genuine integral constructs the continuous phase and its quantitative asymptotic remainder.
Article: jacobi, Proposition B.1.
-/
def phaseDensity (x : ℝ) : ℝ :=
  (S.slope x^2+S.potential x*S.value x^2)/S.amplitude x^2

/-- The actual normalized original state lies on the unit circle at every physical point.
Use: fixes the phase normalization and controls every phase-speed remainder uniformly.
Article: jacobi, Proposition B.1.
Proof: the actual amplitude is nonzero and its square is the original state energy. -/
theorem unit_circle {x : ℝ} (hx : x∈I) : S.unitCos x^2+S.unitSin x^2=1 := by
  unfold unitCos unitSin
  rw [div_pow,div_pow,← add_div,S.amplitude_sq hx]
  have he := S.energy_pos hx
  change 0<S.value x^2+S.slope x^2 at he
  rw [add_comm (S.slope x^2),div_self he.ne']

/-- The actual normalized cosine coordinate has the exact rotating-frame derivative.
Use: proves the genuine phase representation through elementary rotation, without a chosen angle branch.
Article: jacobi, Proposition B.1.
Proof: differentiate the original slope divided by its true positive
amplitude; apply the exact quotient algebra already proved from the original energy. -/
theorem unitCos_hasDerivAt {x : ℝ} (hx : x∈I) :
    HasDerivAt S.unitCos (-S.phaseDensity x*S.unitSin x) x := by
  convert (S.second x hx).div (S.amplitude_hasDerivAt hx) (S.amplitude_pos hx).ne' using 1
  · rfl
  · exact (cosine_quotient_algebra (S.amplitude_pos hx).ne' (S.amplitude_sq hx)).symm

/-- The actual normalized sine coordinate has the exact rotating-frame derivative.
Use: the true phase has precisely the original solution zeros and the original differential equation.
Article: jacobi, Proposition B.1.
Proof: differentiate the original solution value divided by its actual
amplitude and use the proved exact original-state quotient identity. -/
theorem unitSin_hasDerivAt {x : ℝ} (hx : x∈I) :
    HasDerivAt S.unitSin (S.phaseDensity x*S.unitCos x) x := by
  convert (S.first x hx).div (S.amplitude_hasDerivAt hx) (S.amplitude_pos hx).ne' using 1
  · rfl
  · exact (sine_quotient_algebra (S.amplitude_pos hx).ne' (S.amplitude_sq hx)).symm

/-- The actual phase speed has its exact perturbation-of-one form.
Use: the Bessel inverse-square coefficient and the Jacobi bounded remainder give the literal integrable phase perturbations.
Article: jacobi, Proposition B.1.
Proof: express the speed through the two original normalized coordinates and use their proved unit-circle identity. -/
theorem phaseDensity_eq {x : ℝ} (hx : x∈I) :
    S.phaseDensity x=1+(S.potential x-1)*S.unitSin x^2 := by
  have he := S.unit_circle hx
  unfold unitCos unitSin at he
  unfold phaseDensity unitSin
  rw [div_pow,div_pow] at he
  rw [div_pow]
  have hr : S.amplitude x^2≠0 := pow_ne_zero 2 (S.amplitude_pos hx).ne'
  field_simp [hr] at he ⊢
  linear_combination he

/-- A positive lower restoring bound gives the same lower bound for the true phase speed, capped at one.
Use: establishes strict phase monotonicity on every physical comparison interval used in McMahon and Jacobi zero estimates.
Article: jacobi, Proposition B.1.
Proof: multiply by the actual positive state energy. The two residual
coefficients 1-c and q-c are nonnegative and multiply genuine squares. -/
theorem phaseDensity_lower {x c : ℝ} (hx : x∈I) (hc : c≤1) (hq : c≤S.potential x) :
    c≤S.phaseDensity x := by
  apply (le_div_iff₀ (sq_pos_of_pos (S.amplitude_pos hx))).mpr
  rw [S.amplitude_sq hx]
  nlinarith [mul_nonneg (sub_nonneg.mpr hc) (sq_nonneg (S.slope x)),
    mul_nonneg (sub_nonneg.mpr hq) (sq_nonneg (S.value x))]

end RestoringSolution
end
end jacobi.Oscillation
