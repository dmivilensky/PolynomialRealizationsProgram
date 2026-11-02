import jacobi.Hankel.Potential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
Article: jacobi, Lemma E.1.
Use: tailPrimitive_hasDerivAt differentiates the exact Fourier tails occurring in outgoingIntegral.
-/
namespace jacobi.Hankel
noncomputable section
open Set MeasureTheory
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The genuine complex improper integral beyond the current real point.
Use: tailPrimitive_hasDerivAt differentiates the exact Fourier tails occurring in outgoingIntegral.
Article: jacobi, Lemma E.1.
-/
def tailPrimitive (g : ℝ → ℂ) (x : ℝ) : ℂ := ∫ y in Ioi x,g y

/-- The actual improper tail has derivative minus its integrand at every continuity point.
Use: the exact outgoing Fourier-tail formula yields a genuine spatial derivative and then the original inverse-square ODE, rather than a formal differentiation of an unevaluated improper integral.
Article: jacobi, Lemma E.1.
Proof: split the genuine integrable tail at zero and subtract the finite interval integral. The latter has the community FTC derivative with all measurability and integrability hypotheses discharged. -/
theorem tailPrimitive_hasDerivAt {g : ℝ → ℂ} (hg : Integrable g)
    (hm : StronglyMeasurable g) {x : ℝ} (hc : ContinuousAt g x) :
    HasDerivAt (tailPrimitive g) (-g x) x := by
  -- The fixed-base interval representation avoids any exchange of a derivative and an improper limit.
  have he : tailPrimitive g = fun z => (∫ y in Ioi (0:ℝ),g y)-∫ y in (0:ℝ)..z,g y := by
    funext z
    have h := intervalIntegral.integral_Ioi_sub_Ioi'
      (hg.integrableOn (s := Ioi 0)) (hg.integrableOn (s := Ioi z))
    exact eq_sub_iff_add_eq.mpr (by
      change tailPrimitive g z+(∫ y in (0:ℝ)..z,g y)=(∫ y in Ioi (0:ℝ),g y)
      rw [← h]
      simp [tailPrimitive])
  rw [he]
  convert! (hasDerivAt_const x (∫ y in Ioi (0:ℝ),g y)).sub
    (intervalIntegral.integral_hasDerivAt_right hg.intervalIntegrable
      hm.stronglyMeasurableAtFilter hc) using 1
  simp only [zero_sub]

end
end jacobi.Hankel
