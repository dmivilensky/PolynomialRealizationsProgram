import krylov.OneGradient.LastLaunchAlgebra
import krylov.OneGradient.LastLaunchOldRemainder
import krylov.OneGradient.LastLaunchTrialRemainder
import krylov.OneGradient.LastLaunchDefect
import krylov.Stability.ContDiffVirtual
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), actual primitive observed final-launch rows.
Use: derive both incoming-gradient leading coordinate equations from the
literal observed model/conjugacy program, with every local domain derived.
Source: real primitive solve calculus, genuine calibrated reference data,
exact last-launch normal equations and quadratic vanishing products.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix Filter Topology Asymptotics krylov.Methods krylov.Stability
open scoped InnerProductSpace Matrix.Norms.Elementwise
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] {p : ℕ}

/-- The actual finite observed virtual-launch program has the genuine
old-direction drift rows and the true last relative-trial-error row with
quadratic remainders from primitive C-one observations. All correction,
direction, trajectory, normal-equation and eventual inverse premises are
derived; the actual increments and native replay images are retained.
Use: a shared primitive-data theorem for the S and D native incoming
gradient; no incoming-gradient jet or desired output estimate is assumed.
Article: main_krylov, thm:local(a), real complete final-launch coordinate calculus.
Proof: the real reference projected gradient makes the actual model
weights zero. Primitive finite solves derive every true C-one field and
both eventual inverse domains. The exact normal/conjugacy equations give
the old-row theorem; the actual quadratic correction-image defect and
genuine reference calibration give the last-row theorem. -/
theorem lastLaunch_primitive_rows
    (s y : X → Fin p → E) (G : X → E) (tau : X → ℝ)
    (A : X → E →L[ℝ] E) (B : X → Fin p → E →L[ℝ] E)
    (hs : ∀ i,ContDiffAt ℝ 1 (fun z => s z i) 0)
    (hy : ∀ i,ContDiffAt ℝ 1 (fun z => y z i) 0)
    (hG : ContDiffAt ℝ 1 G 0) (htau : ContDiffAt ℝ 1 tau 0) (hA : ContDiffAt ℝ 1 A 0)
    (hB : ∀ i,ContDiffAt ℝ 1 (fun z => B z i) 0)
    (hAzero : ∀ i,A 0=B 0 i) (hy0 : ∀ i,y 0 i=A 0 (s 0 i))
    (hAsym : (A 0).toLinearMap.IsSymmetric) (hsym : ∀ z i,(B z i).toLinearMap.IsSymmetric)
    (hMdom : (pairModel (s 0) (y 0)).det≠0) (hCdom : (crossGram (y 0) (s 0)).det≠0)
    (horth : coordinates (s 0) (G 0)=0)
    (hcal : G 0+tau 0 • A 0 (conjugacyDirection (s 0) (y 0) (G 0))=0)
    (hdescent : inner ℝ (conjugacyDirection (s 0) (y 0) (G 0)) (G 0)≠0)
    (herror : ∀ i,(fun z => y z i-B z i (s z i)) =O[𝓝 0] (fun z => ‖z‖^2)) :
    let M := fun z => pairModel (s z) (y z)
    let w := fun z => modelCoefficients (s z) (M z) (G z)
    let gv := fun z => G z+combine (y z) (w z)
    let d := fun z => conjugacyDirection (s z) (y z) (gv z)
    let next := fun z => G z+A z (combine (s z) (w z)+tau z • d z)
    (∀ i : Fin p,(fun z => inner ℝ (s 0 i) (next z)-
      tau 0*inner ℝ (s 0 i) ((A z-B z i) (d 0))) =O[𝓝 0] (fun z => ‖z‖^2)) ∧
      (fun z => inner ℝ (d 0) (next z)-lastLaunchTrialError (tau z) (d z) (gv z) (A z)*inner ℝ (d 0) (gv 0))
        =O[𝓝 0] (fun z => ‖z‖^2) := by
  let M := fun z => pairModel (s z) (y z)
  let C := fun z => crossGram (y z) (s z)
  let w := fun z => modelCoefficients (s z) (M z) (G z)
  let gv := fun z => G z+combine (y z) (w z)
  let d := fun z => conjugacyDirection (s z) (y z) (gv z)
  let next := fun z => G z+A z (combine (s z) (w z)+tau z • d z)
  have hM (i j : Fin p) : ContDiffAt ℝ 1 (fun z => M z i j) 0 := (hs (max i j)).inner ℝ (hy (min i j))
  have hw (i : Fin p) : ContDiffAt ℝ 1 (fun z => w z i) 0 :=
    contDiff_modelCoefficients s M G 0 hs hM hG hMdom i
  have hw0 : w 0=0 := modelCoefficients_zero (s 0) (M 0) (G 0) horth
  have hgv0 : gv 0=G 0 := by simp only [gv,hw0,combine,Pi.zero_apply,zero_smul,Finset.sum_const_zero,add_zero]
  have hd0 : d 0=conjugacyDirection (s 0) (y 0) (G 0) := by dsimp only [d];rw [hgv0]
  have hblock := contDiff_virtualBlock s y G 0 hs hy hG hMdom hCdom
  have hgv : ContDiffAt ℝ 1 gv 0 := hblock.2.1
  have hd : ContDiffAt ℝ 1 d 0 := hblock.2.2
  have hnext : ContDiffAt ℝ 1 next 0 := hG.add
    (hA.clm_apply (hblock.1.add (htau.smul hd)))
  have hnext0 : next 0=0 := by
    dsimp only [next]
    rw [hw0]
    simp only [combine,Pi.zero_apply,zero_smul,Finset.sum_const_zero,zero_add,map_smul,hd0]
    exact hcal
  have hMmatrix : ContinuousAt M 0 :=
    (contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr (fun j => hM i j)).continuousAt
  have hCmatrix : ContinuousAt C 0 :=
    (contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr (fun j => (hy i).inner ℝ (hs j))).continuousAt
  have hMunits : ∀ᶠ z in 𝓝 (0 : X),IsUnit (M z).det :=
    ((continuous_id.matrix_det.continuousAt.comp hMmatrix).eventually_ne hMdom).mono (fun _ hz => isUnit_iff_ne_zero.mpr hz)
  have hCunits : ∀ᶠ z in 𝓝 (0 : X),IsUnit (C z).det :=
    ((continuous_id.matrix_det.continuousAt.comp hCmatrix).eventually_ne hCdom).mono (fun _ hz => isUnit_iff_ne_zero.mpr hz)
  have hrow : ∀ᶠ z in 𝓝 (0 : X),coordinates (s z) (next z)=
      (crossGram (s z) (fun j => A z (s z j))-M z)*ᵥw z+tau z • coordinates (s z) (A z (d z)) :=
    hMunits.mono (fun z hz => lastLaunch_old_coordinates (s z) (M z) hz (G z) (d z) (A z) (tau z))
  have hconj : ∀ᶠ z in 𝓝 (0 : X),∀ i,inner ℝ (y z i) (d z)=0 := by
    filter_upwards [hCunits] with z hz i
    exact congrFun (conjugacyDirection_conjugate (s z) (y z) (gv z) hz) i
  have hM0 : M 0=crossGram (s 0) (fun j => A 0 (s 0 j)) := by
    have hy' : y 0=fun i => A 0 (s 0 i) := funext hy0
    dsimp only [M]
    rw [hy',pairModel_quadratic (s 0) (A 0) hAsym]
    rfl
  have hdefect : (fun z => next z-gv z-tau z • A z (d z)) =O[𝓝 0] (fun z => ‖z‖^2) := by
    have h := lastLaunch_correction_image_quadratic s y w A hs hy hw hA hw0 hy0
    apply h.congr_left
    intro z
    exact (lastLaunch_exact_defect (s z) (y z) (w z) (G z) (d z) (tau z) (A z)).symm
  refine ⟨fun i => lastLaunch_old_row_remainder s y M w next d tau A B hs hM hw hnext hd htau hA hB
    hAzero hw0 hnext0 hM0 hrow hconj hsym herror i,?_⟩
  apply lastLaunch_trial_row_remainder next gv d tau A hnext hgv hd htau hA hnext0
  · rw [hd0,hgv0]
    exact hdescent
  · have he := congrArg (fun v => inner ℝ (d 0) v) hcal
    rw [inner_add_right,real_inner_smul_right,inner_zero_right,← hd0,← hgv0] at he
    exact he
  · exact hdefect

end
end krylov.OneGradient
