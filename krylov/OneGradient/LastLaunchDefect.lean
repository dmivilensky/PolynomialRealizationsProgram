import krylov.Stability.ContDiffSolve
import krylov.Correction.PairingOrders
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), genuine final-launch correction defect.
Use: actual vanishing virtual weights make the difference between the
evaluated launch and its virtual-gradient trial only quadratic.
Source: exact actual finite correction/image combinations and two true
primitive-C1 first-order vanishing factors per chronological summand.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix Filter Topology Asymptotics krylov.Methods
open scoped BigOperators
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] {p : ℕ}

/-- The genuine correction-image mismatch is quadratic when its true
computed coefficients vanish at the calibrated reference, from only
primitive C-one actual vectors, images and current segment operator.
Use: no desired incoming-gradient or output expansion is assumed.
Article: main_krylov, thm:local(a), actual last-launch middle term.
Proof: every actual image mismatch vanishes at the true quadratic
reference, and every actual virtual coefficient also vanishes. Their
real differentiability bounds give a quadratic product; sum the true
finite chronological terms and commute the actual operator through them. -/
theorem lastLaunch_correction_image_quadratic
    (s y : X → Fin p → E) (w : X → Fin p → ℝ) (A : X → E →L[ℝ] E)
    (hs : ∀ i,ContDiffAt ℝ 1 (fun z => s z i) 0)
    (hy : ∀ i,ContDiffAt ℝ 1 (fun z => y z i) 0)
    (hw : ∀ i,ContDiffAt ℝ 1 (fun z => w z i) 0) (hA : ContDiffAt ℝ 1 A 0)
    (hw0 : w 0=0) (hy0 : ∀ i,y 0 i=A 0 (s 0 i)) :
    (fun z => A z (combine (s z) (w z))-combine (y z) (w z)) =O[𝓝 0] (fun z => ‖z‖^2) := by
  have hprod (i : Fin p) : (fun z => w z i • (A z (s z i)-y z i)) =O[𝓝 0] (fun z => ‖z‖^2) := by
    have hw' : (fun z => w z i) =O[𝓝 0] (fun z => ‖z‖) := by
      simpa only [hw0,Pi.zero_apply,sub_zero] using ((hw i).differentiableAt (by norm_num)).isBigO_sub.norm_right
    have hF := (hA.clm_apply (hs i)).sub (hy i)
    have hF' : (fun z => A z (s z i)-y z i) =O[𝓝 0] (fun z => ‖z‖) := by
      simpa only [hy0 i,sub_self,sub_zero] using (hF.differentiableAt (by norm_num)).isBigO_sub.norm_right
    simpa only [smul_eq_mul,← sq] using hw'.smul hF'
  have hsum := IsBigO.sum (fun i (_ : i∈(Finset.univ : Finset (Fin p))) => hprod i)
  apply hsum.congr_left
  intro z
  simp only [Finset.sum_apply,combine,map_sum,map_smul,smul_sub,Finset.sum_sub_distrib]

/-- The actual evaluated virtual launch differs from its actual virtual
gradient plus trial action by exactly its true correction-image mismatch.
Use: both native S and D implementations share this literal gradient
identity, including their nonzero actual replay-image errors.
Article: main_krylov, thm:local(a), exact genuine last-launch defect.
Proof: expand the actual evaluated operator action and cancel the two
real incoming-gradient terms, retaining the native correction and images. -/
theorem lastLaunch_exact_defect (s y : Fin p → E) (w : Fin p → ℝ)
    (G d : E) (tau : ℝ) (A : E →L[ℝ] E) :
    (G+A (combine s w+tau • d))-(G+combine y w)-tau • A d=A (combine s w)-combine y w := by
  rw [map_add,map_smul]
  abel

end
end krylov.OneGradient
