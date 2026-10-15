import «2610.05164v2».Calculus.ClosedInterval
import Mathlib.Analysis.ODE.PicardLindelof

/-!
Article: 2610.05164v2, Lemma 16.
Closed-interval smoothness for the regularized filter ODEs of F.1.
Use: `«2610.05164v2».Calculus.regular_filter_smooth` feeds
`«2610.05164v2».DualCertificate.NormalizedCalibration.filter_smooth` (filter smooth).
Proof chain: `«2610.05164v2».DualCertificate.NormalizedCalibration.defect_order_seven` —
2610.05164v2, Lemma 16; Actual normalized coefficients, smooth endpoint quotients, state faces and
centering.
Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral remainder
and implicit-function calculus. The needed form is proved here.
-/
namespace «2610.05164v2».Calculus
noncomputable section
open Set Real
open scoped ContDiff
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

 /--
Smoothness to the stated order: `ContDiffOn ℝ ∞ f (Icc (0:ℝ) 1)`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.filter_smooth` uses this assertion
to establish smoothness to the stated order: `ContDiffOn ℝ ∞ (N.filter hκ s) (Icc (0:ℝ) 1)`.

Article: 2610.05164v2, Lemma 16 via
`«2610.05164v2».DualCertificate.NormalizedCalibration.defect_order_seven`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Use the identities/estimates
`«2610.05164v2».Calculus.hasDerivWithinAt_Icc_of_continuous_derivative` with the arguments
shown in the proof.
-/
theorem regular_filter_smooth {p z f : ℝ → ℝ} {s a : ℝ}
    (hp : ContDiffOn ℝ ∞ p (Icc (0:ℝ) 1)) (hz : ContDiffOn ℝ ∞ z (Icc (0:ℝ) 1))
    (hf : ContinuousOn f (Icc (0:ℝ) 1))
    (hd : ∀ t ∈ Ioo (0:ℝ) 1,
      HasDerivAt f (p t*(s*(t*z t)^2-2*f t-a*(f t)^2)) t) :
    ContDiffOn ℝ ∞ f (Icc (0:ℝ) 1) := by
  -- Use the identities/estimates
  -- `«2610.05164v2».Calculus.hasDerivWithinAt_Icc_of_continuous_derivative` with the arguments
  -- shown in the proof.
  let F := fun t y => p t*(s*(t*z t)^2-2*y-a*y^2)
  have hclosed : ∀ t ∈ Icc (0:ℝ) 1, HasDerivWithinAt f (F t (f t)) (Icc (0:ℝ) 1) t :=
    hasDerivWithinAt_Icc_of_continuous_derivative (by norm_num) hf
      (hp.continuousOn.mul (((continuousOn_const.mul ((continuousOn_id.mul hz.continuousOn).pow 2)).sub
        (continuousOn_const.mul hf)).sub (continuousOn_const.mul (hf.pow 2)))) hd
  have hmaps : MapsTo Prod.fst (Icc (0:ℝ) 1 ×ˢ (univ : Set ℝ)) (Icc (0:ℝ) 1) := fun _ hp => hp.1
  have hP := hp.comp contDiffOn_fst hmaps
  have hZ := hz.comp contDiffOn_fst hmaps
  apply ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt (f := F) (u := univ) _
    hclosed (fun _ _ => mem_univ _)
  exact hP.mul (((contDiffOn_const.mul ((contDiffOn_fst.mul hZ).pow 2)).sub
    (contDiffOn_const.mul contDiffOn_snd)).sub (contDiffOn_const.mul (contDiffOn_snd.pow 2)))

end
end «2610.05164v2».Calculus
