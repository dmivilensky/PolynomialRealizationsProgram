import jacobi.Reference.WaveEquation
import jacobi.Reference.Endpoint
import Mathlib.Analysis.RCLike.Sqrt

/-!
Article: jacobi, Appendix C.1 (selected endpoint branch).
The original hypergeometric reference solution is defined at every
complex energy by its frequency square root. The already proved even
frequency identity makes it independent of the choice of root. Its
genuine original equation and selected normalized endpoint branch are
proved for every complex energy, and its reference spectral values are
exactly the complete original Gegenbauer system.
Use: supplies the original reference functions at the genuine Bessel energies in the GL kernel and at arbitrary energy in the transformed equation.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Complex Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual source reference solution at an arbitrary complex energy, in its printed hypergeometric representation.
Use: supplies the original reference functions at the genuine Bessel energies in the GL kernel and at arbitrary energy in the transformed equation.
Article: jacobi, Appendix C.1 (selected endpoint branch).
-/
def solution (a : ℝ) (z : ℂ) (t : ℝ) : ℂ := wave a (Complex.sqrt (z-(jacobi.Jacobi.endpointCorrection a:ℂ))) t

/-- The true first spatial derivative of the actual reference solution at arbitrary complex energy.
Use: fixes the original reference midpoint derivative and Green boundary terms for the GL construction.
Article: jacobi, Appendix C.1 (selected endpoint branch).
-/
def solutionSlope (a : ℝ) (z : ℂ) (t : ℝ) : ℂ := waveSlope a (Complex.sqrt (z-(jacobi.Jacobi.endpointCorrection a:ℂ))) t

/-- The true second spatial derivative of the actual reference solution at arbitrary complex energy.
Use: identifies the original reference differential equation with actual derivatives of its defined functions.
Article: jacobi, Lemma C.1.
-/
def solutionAcceleration (a : ℝ) (z : ℂ) (t : ℝ) : ℂ := waveAcceleration a (Complex.sqrt (z-(jacobi.Jacobi.endpointCorrection a:ℂ))) t

/-- The actual frequency square root has exactly its prescribed original energy square.
Use: discharges the spectral substitution in the genuine reference differential equation.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Proof: the community complex power theorem gives (z^(1/2))^2=z even at zero. -/
theorem frequency_square (z : ℂ) : (Complex.sqrt z)^2=z := by
  exact Complex.cpow_nat_inv_pow z (by norm_num : (2:ℕ)≠0)

/-- The actual source reference wave depends only on its complex frequency square.
Use: the reference spectral function is independent of an artificial root branch choice.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Proof: equal frequency squares give equal or opposite roots; the actual original wave is even. -/
theorem wave_eq_of_square_eq (a : ℝ) {u v : ℂ} (h : u^2=v^2) (t : ℝ) : wave a u t=wave a v t := by
  have hp : (u-v)*(u+v)=0 := by linear_combination h
  rcases mul_eq_zero.mp hp with hu | hv
  · rw [sub_eq_zero.mp hu]
  · rw [eq_neg_of_add_eq_zero_left hv,wave_even]

/-- Every original complex frequency with the prescribed square gives exactly the actual reference spectral function.
Use: evaluates the source function at the genuine reference and Bessel energies without additional square-root restrictions.
Article: jacobi, Appendix C.1 (selected endpoint branch).
Proof: compare the prescribed square with the actual square-root square and use the proved original frequency-square invariance. -/
theorem solution_eq_wave (a : ℝ) {z omega : ℂ} (h : omega^2=z-(jacobi.Jacobi.endpointCorrection a:ℂ)) (t : ℝ) :
    solution a z t=wave a omega t :=
  wave_eq_of_square_eq a ((frequency_square _).trans h.symm) t

/-- The explicit actual reference spatial slope is genuinely the first ordinary derivative for every complex energy.
Use: supplies actual boundary derivatives to all original reference and transformed Green identities.
Article: jacobi, Appendix C.1 (selected endpoint branch).
Proof: the complex energy square root is constant with respect to the physical spatial variable; apply the proved original wave derivative. -/
theorem solution_hasDerivAt (a : ℝ) (z : ℂ) {t : ℝ} (ht : t∈Ioo 0 1) :
    HasDerivAt (solution a z) (solutionSlope a z t) t := wave_hasDerivAt _ _ ht

/-- The explicit actual reference acceleration is genuinely the derivative of its actual spatial slope for every complex energy.
Use: the original reference Schrodinger equation has genuine second ordinary derivatives.
Article: jacobi, Appendix C.1 (selected endpoint branch).
Proof: instantiate the proved true complex-frequency spatial second derivative. -/
theorem solutionSlope_hasDerivAt (a : ℝ) (z : ℂ) {t : ℝ} (ht : t∈Ioo 0 1) :
    HasDerivAt (solutionSlope a z) (solutionAcceleration a z t) t := waveSlope_hasDerivAt _ _ ht

/-- The actual source reference spectral function solves the exact original Schrodinger equation for every complex energy.
Use: supplies the unconditional original reference equation in the genuine GL construction and transformed equation of Proposition C.2.
Article: jacobi, Lemma C.1.
Proof: substitute the true complex square-root frequency into the proved actual wave equation and use its exact energy square. -/
theorem solution_equation {a : ℝ} (ha : -1<a) (z : ℂ) {t : ℝ} (ht : t∈Ioo 0 1) :
    -solutionAcceleration a z t+(potential a t:ℂ)*solution a z t=z*solution a z t := by
  have h := wave_equation ha (Complex.sqrt (z-(jacobi.Jacobi.endpointCorrection a:ℂ))) ht
  rw [frequency_square] at h
  simpa only [solutionAcceleration,solution,add_sub_cancel] using h

/-- The actual arbitrary-energy source function specializes exactly to the genuine complete reference Gegenbauer eigenfunctions.
Use: the source f(t,tau_k), its norming integrals and its complete Hilbert basis are the same original objects.
Article: jacobi, Lemma C.1.
Proof: choose the original positive reference frequency pi*(k+gamma), whose square is the true reference eigenvalue minus its fixed shift, and apply the proved terminating hypergeometric identity. -/
theorem solution_at_eigenvalue (a : ℝ) (k : ℕ) (t : ℝ) : solution a (eigenvalue a k:ℂ) t=(eigenfunction a k t:ℂ) := by
  rw [solution_eq_wave a (omega := ((Real.pi*((k:ℝ)+gamma a):ℝ):ℂ)) (by
    unfold eigenvalue
    push_cast
    ring),wave_at_reference]

end
end jacobi.Reference
