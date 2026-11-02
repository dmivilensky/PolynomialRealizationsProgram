import krylov.OneGradient.LaunchModelRegularity
import krylov.LinearAlgebra.InverseComparison
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), genuine full replay-model comparison.
Use: quadratic native direction-image errors give quadratic true inverse
model errors on the actual full recorded basis, before acting on a gradient.
Source: actual latest observed matrix, real full-basis inverse congruence,
finite spectral matrix calculus and the genuine resolvent identity.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix Filter Topology Asymptotics krylov.Secant krylov.Stability krylov.LinearAlgebra
open scoped Matrix.Norms.L2Operator
variable {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The actual ambient full observed model built from genuine physical
columns and replayed observed image columns, in chronological order.
Use: the native direction basis retains its true replay observations.
Article: main_krylov, thm:local(a), true full direction observed model. -/
def replayLaunchModel (S Y : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  inverseCongruence S (latest (Sᵀ*Y))

/-- Primitive smooth actual columns and replay images give a smooth
genuine full observed model on the true full-column inverse domain.
Use: no inverse-model smoothness is assumed for the native direction solve.
Article: main_krylov, thm:local(a), actual replay-model regularity.
Proof: finite selected latest entries are smooth compressed entries.
Actual basis inversion and transposition preserve primitive smoothness;
their real inverse congruence is exactly the observed ambient model. -/
theorem replayLaunchModel_contDiff
    (S Y : X → Matrix (Fin n) (Fin n) ℝ)
    (hS : ContDiffAt ℝ 1 S 0) (hY : ContDiffAt ℝ 1 Y 0) (hu : IsUnit (S 0).det) :
    ContDiffAt ℝ 1 (fun z => replayLaunchModel (S z) (Y z)) 0 := by
  let L := (Matrix.transposeLinearEquiv (R := ℝ) (m := Fin n) (n := Fin n) (α := ℝ)).toContinuousLinearEquiv
  have hSt : ContDiffAt ℝ 1 (fun z => (S z)ᵀ) 0 := L.toContinuousLinearMap.contDiff.contDiffAt.comp 0 hS
  have hC := hSt.mul hY
  have hM : ContDiffAt ℝ 1 (fun z => latest ((S z)ᵀ*Y z)) 0 := by
    apply contDiff_spectral_matrix
    intro i j
    have he := (matrixEntryEquiv n n).toContinuousLinearMap.contDiff.contDiffAt.comp 0 hC
    exact contDiffAt_pi.mp he (min i j,max i j)
  have hi := contDiff_spectral_inverse S 0 hS hu
  have hit : ContDiffAt ℝ 1 (fun z => ((S z)⁻¹)ᵀ) 0 := L.toContinuousLinearMap.contDiff.contDiffAt.comp 0 hi
  simpa only [replayLaunchModel,inverseCongruence,Matrix.transpose_nonsing_inv] using (hit.mul hM).mul hi

/-- Quadratic actual replay-image errors give quadratic actual full
inverse-model errors, on the same genuine moving physical basis. Both
model inverse domains are derived from the true common positive reference.
Use: native direction replay affects a vanishing incoming gradient only
at cubic order, with no exact replay-image assumption on varying data.
Article: main_krylov, thm:local(a), full replay inverse comparison.
Proof: the true compressed model difference is the selected latest part
of Sᵀ times the actual image error. Bounded actual basis inverses transfer
its quadratic order to the real ambient models. Primitive continuity and
the genuine common positive reference allow the exact resolvent estimate. -/
theorem replay_launch_inverse_quadratic
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (S Y : X → Matrix (Fin n) (Fin n) ℝ)
    (hS : ContDiffAt ℝ 1 S 0) (hY : ContDiffAt ℝ 1 Y 0) (hu : IsUnit (S 0).det)
    (A : X → ℕ → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ k,ContDiffAt ℝ 1 (fun z => A z k) 0) (hA0 : ∀ k,A 0 k=base)
    (hY0 : Y 0=pairImages (S 0) (A 0))
    (herror : (fun z => Y z-pairImages (S z) (A z)) =O[𝓝 0] (fun z => ‖z‖^2)) :
    (fun z => (replayLaunchModel (S z) (Y z))⁻¹-(launchObservedModel (S z) (A z))⁻¹)
      =O[𝓝 0] (fun z => ‖z‖^2) := by
  let J := fun z => replayLaunchModel (S z) (Y z)
  let K := fun z => launchObservedModel (S z) (A z)
  let L := (Matrix.transposeLinearEquiv (R := ℝ) (m := Fin n) (n := Fin n) (α := ℝ)).toContinuousLinearEquiv
  have hSt : ContDiffAt ℝ 1 (fun z => (S z)ᵀ) 0 := L.toContinuousLinearMap.contDiff.contDiffAt.comp 0 hS
  have hi := contDiff_spectral_inverse S 0 hS hu
  have hit : ContDiffAt ℝ 1 (fun z => ((S z)⁻¹)ᵀ) 0 := L.toContinuousLinearMap.contDiff.contDiffAt.comp 0 hi
  have hraw : (fun z => (S z)ᵀ*(Y z-pairImages (S z) (A z))) =O[𝓝 0] (fun z => ‖z‖^2) := by
    simpa only [one_mul] using matrix_mul_bigO _ _ _ _ (hSt.continuousAt.tendsto.isBigO_one ℝ) herror
  have hselected : (fun z => latest ((S z)ᵀ*(Y z-pairImages (S z) (A z)))) =O[𝓝 0] (fun z => ‖z‖^2) := by
    apply (matrix_bigO_iff_entry _ _).mpr
    intro i j
    exact (matrix_bigO_iff_entry _ _).mp hraw (min i j) (max i j)
  have hleft := matrix_mul_bigO _ _ _ _ (hit.continuousAt.tendsto.isBigO_one ℝ) hselected
  have hfull := matrix_mul_bigO _ _ _ _ hleft (hi.continuousAt.tendsto.isBigO_one ℝ)
  have hdiff : (fun z => J z-K z) =O[𝓝 0] (fun z => ‖z‖^2) := by
    have hh : (fun z => ((S z)⁻¹)ᵀ*latest ((S z)ᵀ*(Y z-pairImages (S z) (A z)))*(S z)⁻¹)
        =O[𝓝 0] (fun z => ‖z‖^2) := by simpa only [one_mul,mul_one] using hfull
    apply hh.congr_left
    intro z
    have he : latest ((S z)ᵀ*(Y z-pairImages (S z) (A z)))=
        latest ((S z)ᵀ*Y z)-latest ((S z)ᵀ*pairImages (S z) (A z)) := by
      ext i j
      simp only [Matrix.mul_sub,latest,Matrix.sub_apply]
    rw [he,Matrix.mul_sub,Matrix.sub_mul]
    simp only [J,K,replayLaunchModel,launchObservedModel,inverseCongruence,Matrix.transpose_nonsing_inv]
  have hK0 : K 0=base := by
    rw [show K 0=launchObservedModel (S 0) (A 0) from rfl,
      show A 0=(fun _ => base) from funext hA0]
    exact launch_model_reference base (S 0) hb.isHermitian.isSymm hu
  have hJ0 : J 0=base := by
    change replayLaunchModel (S 0) (Y 0)=base
    rw [hY0]
    exact hK0
  have hJ : ContDiffAt ℝ 1 J 0 := replayLaunchModel_contDiff S Y hS hY hu
  have hK : ContDiffAt ℝ 1 K 0 := (launch_model_contDiff S hS hu A hA).2
  apply matrix_inverse_difference_order J K base (isUnit_iff_ne_zero.mpr hb.det_pos.ne') (fun z => ‖z‖^2)
    (by simpa only [hJ0] using hJ.continuousAt.tendsto)
    (by simpa only [hK0] using hK.continuousAt.tendsto) hdiff

end
end krylov.OneGradient
