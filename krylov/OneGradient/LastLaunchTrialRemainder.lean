import krylov.Stability.C1VanishingProduct
import krylov.Correction.PairingOrders
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Calculus
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), genuine incoming last-pivot remainder.
Use: derive the unmeasured last-direction coefficient from the actual
evaluated trial, retaining its true virtual gradient and actual curvature.
Source: exact real line-error algebra and primitive-C1 vanishing products.
-/

namespace krylov.OneGradient
noncomputable section
open Filter Topology Asymptotics krylov.Stability krylov.Correction
open scoped InnerProductSpace
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The actual last relative trial error expressed directly in the real
descent pairing and actual measured curvature. It is an analysis quantity;
the unknown operator never enters the history-only choice of trial.
Use: no hypothetical exact-search gradient replaces the actual launch.
Article: main_krylov, thm:local(a), actual relative last-pivot error. -/
def lastLaunchTrialError (tau : ℝ) (d gv : E) (A : E →L[ℝ] E) : ℝ :=
  1+tau*inner ℝ d (A d)/inner ℝ d gv

/-- The actual final evaluated gradient's last-direction coordinate has
the true relative-trial-error coefficient with a quadratic remainder,
from primitive C-one data and the derived quadratic launch defect.
Use: closes the last row of the original incoming-gradient expansion;
the leading trial error remains its actual measured scalar.
Article: main_krylov, thm:local(a), genuine incoming last-pivot coefficient.
Proof: actual reference calibration makes the real relative error zero.
Its C-one chart and the true descent-pairing variation are first order.
Their product, the actual quadratic launch defect, and freezing the left
direction against the genuine zero incoming gradient all cost quadratic
order. The exact denominator identity identifies the real last row. -/
theorem lastLaunch_trial_row_remainder
    (G gv d : X → E) (tau : X → ℝ) (A : X → E →L[ℝ] E)
    (hG : ContDiffAt ℝ 1 G 0) (hgv : ContDiffAt ℝ 1 gv 0) (hd : ContDiffAt ℝ 1 d 0)
    (htau : ContDiffAt ℝ 1 tau 0) (hA : ContDiffAt ℝ 1 A 0)
    (hG0 : G 0=0) (hden : inner ℝ (d 0) (gv 0)≠0)
    (hcal : inner ℝ (d 0) (gv 0)+tau 0*inner ℝ (d 0) (A 0 (d 0))=0)
    (hdefect : (fun z => G z-gv z-tau z • A z (d z)) =O[𝓝 0] (fun z => ‖z‖^2)) :
    (fun z => inner ℝ (d 0) (G z)-lastLaunchTrialError (tau z) (d z) (gv z) (A z)*inner ℝ (d 0) (gv 0))
      =O[𝓝 0] (fun z => ‖z‖^2) := by
  let c := fun z => inner ℝ (d z) (gv z)
  let eps := fun z => lastLaunchTrialError (tau z) (d z) (gv z) (A z)
  have hc : ContDiffAt ℝ 1 c 0 := hd.inner ℝ hgv
  have heps : ContDiffAt ℝ 1 eps 0 := contDiffAt_const.add
    ((htau.mul (hd.inner ℝ (hA.clm_apply hd))).div hc hden)
  have heps0 : eps 0=0 := by
    have he : tau 0*inner ℝ (d 0) (A 0 (d 0))= -c 0 := by dsimp only [c];linarith
    dsimp only [eps,lastLaunchTrialError]
    rw [he,neg_div,div_self hden,add_neg_cancel]
  have heb : eps =O[𝓝 0] (fun z => ‖z‖) := by
    simpa only [heps0,sub_zero] using (heps.differentiableAt (by norm_num)).isBigO_sub.norm_right
  have hcb : (fun z => c z-c 0) =O[𝓝 0] (fun z => ‖z‖) := by
    simpa only [sub_zero] using (hc.differentiableAt (by norm_num)).isBigO_sub.norm_right
  have hprod : (fun z => eps z*(c z-c 0)) =O[𝓝 0] (fun z => ‖z‖^2) := by simpa only [← sq] using heb.mul hcb
  have hdb : d =O[𝓝 0] (fun _ => (1 : ℝ)) := hd.continuousAt.tendsto.isBigO_one ℝ
  have herror : (fun z => inner ℝ (d z) (G z-gv z-tau z • A z (d z))) =O[𝓝 0] (fun z => ‖z‖^2) := by
    simpa only [one_mul] using inner_order _ _ _ _ hdb hdefect
  have hdd : (fun z => d z-d 0) =O[𝓝 0] (fun z => ‖z‖) := by
    simpa only [sub_zero] using (hd.differentiableAt (by norm_num)).isBigO_sub.norm_right
  have hgb : G =O[𝓝 0] (fun z => ‖z‖) := by
    simpa only [hG0,sub_zero] using (hG.differentiableAt (by norm_num)).isBigO_sub.norm_right
  have hleft : (fun z => inner ℝ (d z) (G z)-inner ℝ (d 0) (G z)) =O[𝓝 0] (fun z => ‖z‖^2) := by
    simpa only [inner_sub_left,← sq] using inner_order _ _ _ _ hdd hgb
  apply ((hprod.add herror).sub hleft).congr' ?_ EventuallyEq.rfl
  filter_upwards [hc.continuousAt.eventually_ne hden] with z hz
  have he : eps z*c z=c z+tau z*inner ℝ (d z) (A z (d z)) := by
    change (1+tau z*inner ℝ (d z) (A z (d z))/c z)*c z=c z+tau z*inner ℝ (d z) (A z (d z))
    rw [add_mul,one_mul,div_mul_cancel₀ _ hz]
  simp only [inner_sub_right,real_inner_smul_right]
  change eps z*(c z-c 0)+(inner ℝ (d z) (G z)-c z-tau z*inner ℝ (d z) (A z (d z)))-
    (inner ℝ (d z) (G z)-inner ℝ (d 0) (G z))=inner ℝ (d 0) (G z)-eps z*c 0
  nlinarith [he]

end
end krylov.OneGradient
