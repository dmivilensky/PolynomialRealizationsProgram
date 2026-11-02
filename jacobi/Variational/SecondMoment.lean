import jacobi.Variational.Problem
import Mathlib.MeasureTheory.Integral.Prod

/-!
Article: jacobi, Appendix D.1 (moment and top-eigenvalue variations).
The quadratic form below is the literal exponential-kernel double integral,
including signed perturbations. Absolute convergence licenses every use of
Fubini and bilinearity. The final expansion concerns the actual kernel spectrum,
and its remainder has the printed quadratic L1 bound.
Use: polarization and the exact first variation of G_2.
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Real
set_option backward.isDefEq.respectTransparency false

/-- The signed bilinear form associated with the second spectral moment.
Use: polarization and the exact first variation of G_2.
Article: jacobi, Appendix D.1 (moment and top-eigenvalue variations).
-/
def secondPairing (m q : ℝ → ℝ) : ℝ :=
  ∫ z : ℝ × ℝ, m z.1*q z.2*exp (-2*|z.1-z.2|) ∂volume.prod volume

/-- The exponential kernel never enlarges the independent-coordinate L1 majorant.
Use: absolute convergence, Fubini and the quadratic remainder bound.
Article: jacobi, Appendix D.1 (moment and top-eigenvalue variations).
Proof: exp(-2|x-y|) lies between zero and one. -/
theorem second_integrand_bound (m q : ℝ → ℝ) (z : ℝ × ℝ) :
    |m z.1*q z.2*exp (-2*|z.1-z.2|)| ≤ |m z.1| * |q z.2| := by
  rw [abs_mul, abs_mul, abs_of_pos (exp_pos _)]
  exact mul_le_of_le_one_right (by positivity) (exp_le_one_iff.mpr (by linarith [abs_nonneg (z.1-z.2)]))

/-- All signed pairings of measurable L1 densities are absolutely convergent.
Use: supplies the hypotheses of the Fubini and Bochner linearity theorems below.
Article: jacobi, Appendix D.1 (moment multipliers and clipped profiles).
Proof: dominate by |m(x)| |q(y)|, whose product integral is finite. -/
theorem second_integrand_integrable {m q : ℝ → ℝ} (hm : Integrable m) (hq : Integrable q)
    (hmm : Measurable m) (hqm : Measurable q) :
    Integrable (fun z : ℝ × ℝ => m z.1*q z.2*exp (-2*|z.1-z.2|)) (volume.prod volume) := by
  apply (hm.abs.mul_prod hq.abs).mono'
  · exact (((hmm.comp measurable_fst).mul (hqm.comp measurable_snd)).mul
      (((continuous_abs.measurable.comp (measurable_fst.sub measurable_snd)).const_mul (-2)).exp)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun z => by
      simpa only [Real.norm_eq_abs] using second_integrand_bound m q z

/-- The product-space pairing is the convolution form used for the gradient.
Use: identifies the linear term in the spectral expansion with integral 2W_2 q.
Article: jacobi, Appendix D.1 (moment and top-eigenvalue variations).
Proof: absolute convergence gives Fubini; the fixed density factor leaves the inner integral. -/
theorem secondPairing_iterated {m q : ℝ → ℝ} (hm : Integrable m) (hq : Integrable q)
    (hmm : Measurable m) (hqm : Measurable q) :
    secondPairing m q = ∫ x, m x*(∫ y, q y*exp (-2*|x-y|)) := by
  rw [secondPairing, integral_prod _ (second_integrand_integrable hm hq hmm hqm)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    rw [← integral_const_mul]
    congr 1
    funext y
    ring

/-- Symmetry of the signed second-moment pairing.
Use: combines the two cross terms in the exact quadratic expansion.
Article: jacobi, Appendix D.1 (moment and top-eigenvalue variations).
Proof: Fubini swaps the two coordinates and |x-y|=|y-x|. -/
theorem secondPairing_symm {m q : ℝ → ℝ} (hm : Integrable m) (hq : Integrable q)
    (hmm : Measurable m) (hqm : Measurable q) : secondPairing m q = secondPairing q m := by
  rw [secondPairing, integral_prod _ (second_integrand_integrable hm hq hmm hqm),
    integral_integral_swap (second_integrand_integrable hm hq hmm hqm),
    secondPairing, integral_prod _ (second_integrand_integrable hq hm hqm hmm)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => integral_congr_ae
    (Filter.Eventually.of_forall fun y => by dsimp only; rw [abs_sub_comm, mul_comm (m y) (q x)])

/-- Subtraction is linear in the first coordinate of the signed pairing.
Use: expands a perturbation q-m without imposing positivity on that perturbation.
Article: jacobi, Appendix D.1 (moment and top-eigenvalue variations).
Proof: distribute the scalar integrand and use absolute integrability. -/
theorem secondPairing_sub_left {m q p : ℝ → ℝ}
    (hm : Integrable m) (hq : Integrable q) (hp : Integrable p)
    (hmm : Measurable m) (hqm : Measurable q) (hpm : Measurable p) :
    secondPairing (m-q) p = secondPairing m p-secondPairing q p := by
  -- Expand the signed product on the product space, where both terms are integrable.
  unfold secondPairing
  have he : (fun z : ℝ × ℝ => (m-q) z.1*p z.2*exp (-2*|z.1-z.2|)) =
      (fun z => m z.1*p z.2*exp (-2*|z.1-z.2|))-
        (fun z => q z.1*p z.2*exp (-2*|z.1-z.2|)) := by
    funext z
    simp only [Pi.sub_apply]
    ring
  rw [he]
  exact integral_sub (second_integrand_integrable hm hp hmm hpm)
    (second_integrand_integrable hq hp hqm hpm)

/-- Subtraction is linear in the second coordinate as well.
Use: polarizes the signed remainder around an arbitrary density.
Article: jacobi, Appendix D.1 (moment and top-eigenvalue variations).
Proof: symmetry reduces the assertion to first-coordinate linearity. -/
theorem secondPairing_sub_right {m q p : ℝ → ℝ}
    (hm : Integrable m) (hq : Integrable q) (hp : Integrable p)
    (hmm : Measurable m) (hqm : Measurable q) (hpm : Measurable p) :
    secondPairing m (q-p) = secondPairing m q-secondPairing m p := by
  rw [secondPairing_symm hm (hq.sub hp) hmm (hqm.sub hpm),
    secondPairing_sub_left hq hp hm hqm hpm hmm,
    secondPairing_symm hq hm hqm hmm, secondPairing_symm hp hm hpm hmm]

/-- The bilinear form is bounded by the product of the two actual L1 norms.
Use: bounds the first-variation remainder, uniformly for all signed perturbations.
Article: jacobi, Appendix D.1 (moment and top-eigenvalue variations).
Proof: bound the norm of the integral, then integrate the independent-coordinate majorant. -/
theorem abs_secondPairing_le {m q : ℝ → ℝ} (hm : Integrable m) (hq : Integrable q)
    (hmm : Measurable m) (hqm : Measurable q) :
    |secondPairing m q| ≤ (∫ x, |m x|)*(∫ x, |q x|) := by
  -- The product majorant is integrable before either coordinate is integrated out.
  have hi := second_integrand_integrable hm hq hmm hqm
  calc
    _ ≤ ∫ z : ℝ × ℝ, ‖m z.1*q z.2*exp (-2*|z.1-z.2|)‖ ∂volume.prod volume :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ z : ℝ × ℝ, |m z.1| * |q z.2| ∂volume.prod volume := by
      apply integral_mono_ae hi.norm (hm.abs.mul_prod hq.abs)
      exact Filter.Eventually.of_forall fun z => by
        simpa only [Real.norm_eq_abs] using second_integrand_bound m q z
    _ = _ := by simpa using integral_prod_mul (fun x : ℝ => |m x|) (fun x : ℝ => |q x|)

/-- The pairing of a density with itself is its actual second spectral moment.
Use: ensures the variation theorem applies to the genuine observation G_2.
Article: jacobi, Appendix D.1 (moment and top-eigenvalue variations).
Proof: reuse the proved kernel spectral moment identity and Fubini. -/
theorem L1Source.secondPairing_self (m : L1Source) : secondPairing m.value m.value = observe m .second := by
  rw [secondPairing, integral_prod _
    (second_integrand_integrable m.integrable m.integrable m.measurable m.measurable)]
  exact (chebyshev2.Continuum.kernelEigenvalue_square_integral m.integrable m.nonneg).symm

/-- Exact first variation with its actual signed quadratic remainder.
Use: the i=2 part of the multiplier rule's spectral expansion.
Article: jacobi, Appendix D.1 (moment and top-eigenvalue variations).
Proof: polarize the signed bilinear form and identify both diagonal pairings spectrally. -/
theorem second_expansion (m q : L1Source) :
    observe q .second-observe m .second-2*secondPairing m.value (q.value-m.value) =
      secondPairing (q.value-m.value) (q.value-m.value) := by
  rw [secondPairing_sub_left q.integrable m.integrable (q.integrable.sub m.integrable)
      q.measurable m.measurable (q.measurable.sub m.measurable),
    secondPairing_sub_right q.integrable q.integrable m.integrable q.measurable q.measurable m.measurable,
    secondPairing_sub_right m.integrable q.integrable m.integrable m.measurable q.measurable m.measurable,
    secondPairing_symm q.integrable m.integrable q.measurable m.measurable,
    m.secondPairing_self, q.secondPairing_self]
  ring

/-- The exact second-moment remainder is quadratically small in L1.
Use: the proved remainder estimate required for constraint qualification.
Article: jacobi, Appendix D.1 (moment and top-eigenvalue variations).
Proof: apply the signed bilinear norm bound to the exact expansion. -/
theorem second_expansion_remainder (m q : L1Source) :
    |observe q .second-observe m .second-2*secondPairing m.value (q.value-m.value)| ≤
      (∫ x, |q.value x-m.value x|)^2 := by
  rw [second_expansion, pow_two]
  exact abs_secondPairing_le (q.integrable.sub m.integrable) (q.integrable.sub m.integrable)
    (q.measurable.sub m.measurable) (q.measurable.sub m.measurable)

end
end jacobi.Variational
