import chebyshev2.Calculus.CubicRemoval
import chebyshev2.Calculus.DefectOrder

/-!
Article: chebyshev2, Lemma 16.
The three normalized F.1 defect equations share the same exact smooth cubic removal.
Use: `chebyshev2.Calculus.regular_defect_cubic_quotient` feeds
`chebyshev2.DualCertificate.NormalizedCalibration.linearDefect_cubic_quotient` (linear Defect
cubic quotient).
Proof chain: `chebyshev2.DualCertificate.NormalizedCalibration.R_smooth` — chebyshev2, Lemma
16; Actual normalized coefficients, smooth endpoint quotients, state faces and centering.
Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral remainder
and implicit-function calculus. The needed form is proved here.
-/
namespace chebyshev2.Calculus
noncomputable section
open Set Real
open scoped ContDiff
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/--
Defines `defectRHS` of type `ℝ` by `p t*((1+a)*t^6-2*(1+a*t^3)*w t+a*(w t)^2)`.

Use: `chebyshev2.Calculus.regular_defect_cubic_quotient` rewrites with this definition to
establish constructs witnesses with the exact properties `∃ g : ℝ → ℝ, ContDiffOn ℝ ∞ g (Icc
(0:ℝ) 1) ∧ ∀ t ∈ Icc (0:ℝ) 1, w t=t^3*g t`.

Article: chebyshev2, Lemma 16 via
`chebyshev2.DualCertificate.NormalizedCalibration.defect_order_seven`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.
-/
def defectRHS (p w : ℝ → ℝ) (a t : ℝ) : ℝ :=
  p t*((1+a)*t^6-2*(1+a*t^3)*w t+a*(w t)^2)

/--
Constructs witnesses with the exact properties `∃ g : ℝ → ℝ, ContDiffOn ℝ ∞ g (Icc (0:ℝ) 1) ∧ ∀
t ∈ Icc (0:ℝ) 1, w t=t^3*g t`.

Use: `chebyshev2.DualCertificate.NormalizedCalibration.defect_cubic_quotient` uses this
identity to construct witnesses satisfying `∃ g : ℝ → ℝ, ContDiffOn ℝ
∞ g (Icc (0:ℝ) 1) ∧ ∀ t ∈ Icc (0:ℝ) 1, N.defect hκ s t=t^3*g t`.

Article: chebyshev2, Lemma 16 via
`chebyshev2.DualCertificate.NormalizedCalibration.R_smooth`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Use the identities/estimates `chebyshev2.Calculus.smooth_cubic_quotient` with the
arguments shown in the proof.
-/
theorem regular_defect_cubic_quotient {p w : ℝ → ℝ} {a : ℝ}
    (hp : ContDiffOn ℝ ∞ p (Icc (0:ℝ) 1)) (hw : ContDiffOn ℝ ∞ w (Icc (0:ℝ) 1))
    (hzero : w 0=0)
    (hd : ∀ t ∈ Icc (0:ℝ) 1, HasDerivWithinAt w (defectRHS p w a t) (Icc (0:ℝ) 1) t) :
    ∃ g : ℝ → ℝ, ContDiffOn ℝ ∞ g (Icc (0:ℝ) 1) ∧ ∀ t ∈ Icc (0:ℝ) 1, w t=t^3*g t := by
  -- Use the identities/estimates `chebyshev2.Calculus.smooth_cubic_quotient` with the
  -- arguments shown in the proof.
  have hz : defectRHS p w a 0=0 := by simp [defectRHS,hzero]
  have hfirst : derivWithin w (Icc (0:ℝ) 1) 0=0 :=
    ((hd 0 (by norm_num)).derivWithin (uniqueDiffOn_Icc (by norm_num : (0:ℝ)<1) 0 (by norm_num))).trans hz
  have hp₀ := (hp.differentiableOn (by simp) 0 (show (0:ℝ) ∈ Icc 0 1 by norm_num)).hasDerivWithinAt
  have hw₀ := hd 0 (show (0:ℝ) ∈ Icc 0 1 by norm_num)
  rw [hz] at hw₀
  have ht := hasDerivWithinAt_id (0:ℝ) (Icc (0:ℝ) 1)
  have hb := (((ht.pow 6).const_mul (1+a)).sub
    ((((ht.pow 3).const_mul a).const_add 1).const_mul 2 |>.mul hw₀)).add
      ((hw₀.pow 2).const_mul a)
  have hprod := hp₀.mul hb
  have hzeroRHS : HasDerivWithinAt (defectRHS p w a) 0 (Icc (0:ℝ) 1) 0 := by
    convert! hprod using 1
    simp [hzero]
  have heq : EqOn (derivWithin w (Icc (0:ℝ) 1)) (defectRHS p w a) (Icc (0:ℝ) 1) := by
    intro t ht
    exact (hd t ht).derivWithin (uniqueDiffOn_Icc (by norm_num : (0:ℝ)<1) t ht)
  have hsecond : iteratedDerivWithin 2 w (Icc (0:ℝ) 1) 0=0 := by
    rw [show (2:ℕ)=1+1 by rfl,iteratedDerivWithin_succ,iteratedDerivWithin_one,
      derivWithin_congr heq (heq (by norm_num : (0:ℝ) ∈ Icc 0 1))]
    exact hzeroRHS.derivWithin (uniqueDiffOn_Icc (by norm_num : (0:ℝ)<1) 0 (by norm_num))
  exact smooth_cubic_quotient (by norm_num : (0:ℝ)<1) hw hzero hfirst hsecond

end
end chebyshev2.Calculus
