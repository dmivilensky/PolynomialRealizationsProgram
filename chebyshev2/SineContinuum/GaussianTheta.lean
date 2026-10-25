import chebyshev2.SineContinuum.ThetaSeries
import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds

/-!
Article: chebyshev2, Proposition 2.
The literal sigma_1 series is the half-characteristic Gaussian theta constant.
Use: `chebyshev2.SineContinuum.thetaTwo_sigma₁` feeds `chebyshev2.SineContinuum.n_theta`
(Proposition 2, equation (10): the actual sine density has the literal theta formula).
Proof chain: `chebyshev2.LocalObstruction.sine_green_scale_tail` — chebyshev2, Theorem 6.1; No
locally sharp C1 bound from finitely many spectral observations.
-/
namespace chebyshev2.SineContinuum
noncomputable section
open Real
set_option backward.isDefEq.respectTransparency false

/--
Defines `gaussianThetaTerm` of type `ℝ` by `exp (-π*((j:ℝ)+a)^2*v)`.

Use: `chebyshev2.SineContinuum.gaussianTheta` uses this definition in the displayed
construction of `gaussianTheta`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.n_theta`.
-/
def gaussianThetaTerm (a v : ℝ) (j : ℤ) : ℝ := exp (-π*((j:ℝ)+a)^2*v)
/--
Defines `gaussianTheta` of type `ℝ` by `∑' j : ℤ, gaussianThetaTerm a v j`.

Use: `chebyshev2.SineContinuum.gaussianTheta_add_one` uses this definition to establish
exact identity `gaussianTheta (a+1) v = gaussianTheta a v`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.n_theta`.
-/
def gaussianTheta (a v : ℝ) : ℝ := ∑' j : ℤ, gaussianThetaTerm a v j

/--
Summability for every real characteristic, from mathlib's Gaussian theta bounds.

Summability of the displayed sequence: `Summable (gaussianThetaTerm a v)`.

Use: `chebyshev2.SineContinuum.gaussianTheta_positive` uses this summability result to
establish the stated quantitative bound `0 < gaussianTheta a v`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.n_theta`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem gaussianTheta_summable (a : ℝ) {v : ℝ} (hv : 0 < v) :
    Summable (gaussianThetaTerm a v) := by
  have h := HurwitzKernelBounds.summable_f_int 0 a hv
  convert h using 1
  funext j
  simp [HurwitzKernelBounds.f_int,gaussianThetaTerm]

/--
The stated quantitative bound `0 < gaussianTheta a v`.

Use: `chebyshev2.SineContinuum.thetaFour_positive` uses this bound to establish the stated
quantitative bound `0 < thetaFour v`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.n_theta`.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.gaussianTheta_summable` with
the arguments shown in the proof.
-/
theorem gaussianTheta_positive (a : ℝ) {v : ℝ} (hv : 0 < v) : 0 < gaussianTheta a v :=
  (exp_pos _).trans_le ((gaussianTheta_summable a hv).le_tsum 0 (fun _ _ => (exp_pos _).le))

/--
Integer translation does not change a Gaussian characteristic.

Exact identity `gaussianTheta (a+1) v = gaussianTheta a v`.

Use: `chebyshev2.SineContinuum.thetaFour_inversion` uses this identity to establish exact
identity `thetaFour v = (sqrt v)⁻¹*thetaTwo v⁻¹`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.n_theta`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem gaussianTheta_add_one (a v : ℝ) : gaussianTheta (a+1) v = gaussianTheta a v := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  unfold gaussianTheta
  rw [← (Equiv.addRight (1:ℤ)).tsum_eq (fun j => gaussianThetaTerm a v j)]
  apply tsum_congr
  intro j
  unfold gaussianThetaTerm
  simp only [Equiv.coe_addRight]
  congr 1
  push_cast
  ring

/--
The two unsigned classical theta constants; theta_4 is represented by sigma_2.

Use: `chebyshev2.SineContinuum.thetaFour_duplication` rewrites with this definition to
establish exact identity `thetaFour v^2 = thetaThree (2*v)^2-thetaTwo (2*v)^2`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.n_theta`.
-/
def thetaThree (v : ℝ) : ℝ := gaussianTheta 0 v
/--
Defines `thetaTwo` of type `ℝ` by `gaussianTheta (1/2) v`.

Use: `chebyshev2.SineContinuum.thetaTwo_sigma₁` uses this definition to establish exact
identity `thetaTwo v = 2*exp (-π*v/4)*sigma₁ (exp (-π*v))`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.n_theta`.
-/
def thetaTwo (v : ℝ) : ℝ := gaussianTheta (1/2) v

/--
The literal sigma_1 series is the half-characteristic Gaussian theta constant.

Exact identity `thetaTwo v = 2*exp (-π*v/4)*sigma₁ (exp (-π*v))`.

Use: `chebyshev2.SineContinuum.n_theta` rewrites with this identity to establish exact
identity `n x = thetaDensity x`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.n_theta`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem thetaTwo_sigma₁ {v : ℝ} (hv : 0 < v) :
    thetaTwo v = 2*exp (-π*v/4)*sigma₁ (exp (-π*v)) := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  have hq : exp (-π*v) < 1 := exp_lt_one_iff.mpr (by nlinarith [pi_pos,hv])
  have hs : HasSum (fun j : ℕ => exp (-π*v/4)*exp (-π*v)^(j*(j+1)))
      (exp (-π*v/4)*sigma₁ (exp (-π*v))) :=
    (sigma₁_summable (exp_pos _).le hq).hasSum.mul_left (exp (-π*v/4))
  have ht (j : ℕ) : exp (-π*v/4)*exp (-π*v)^(j*(j+1)) =
      gaussianThetaTerm (1/2) v (j:ℤ) := by
    rw [← exp_nat_mul,← exp_add]
    unfold gaussianThetaTerm
    congr 1
    push_cast
    ring
  have hnat : HasSum (fun j : ℕ => gaussianThetaTerm (1/2) v (j:ℤ))
      (exp (-π*v/4)*sigma₁ (exp (-π*v))) := by
    simpa only [ht] using hs
  have hneg (j : ℕ) : gaussianThetaTerm (1/2) v (Int.negSucc j) =
      gaussianThetaTerm (1/2) v (j:ℤ) := by
    unfold gaussianThetaTerm
    congr 1
    push_cast
    ring
  have h := hnat.int_rec hnat
  have he : (fun j : ℤ => Int.rec (fun n => gaussianThetaTerm (1/2) v (n:ℤ))
        (fun n => gaussianThetaTerm (1/2) v (n:ℤ)) j) = gaussianThetaTerm (1/2) v := by
    funext j
    cases j with
    | ofNat j => rfl
    | negSucc j => exact (hneg j).symm
  rw [he] at h
  change (∑' j : ℤ, gaussianThetaTerm (1/2) v j) = _
  rw [h.tsum_eq]
  ring

end
end chebyshev2.SineContinuum
