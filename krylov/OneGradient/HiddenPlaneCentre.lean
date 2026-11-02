import krylov.OneGradient.HiddenPlaneObservation
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(c), actual hidden-entry centre and remainder.
Use: derive the true centre matrix budget, exact hidden rank-one residual
and its sharp half-width from the actual observed physical operator.
Source: proved original Schur interval and actual symmetric action on a
complete real orthonormal plane; singular corners are handled directly.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.LinearAlgebra
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The actual hidden entry lies within its true centred half-width,
which is between zero and one; the actual observed centre matrix is
a genuine spectral contraction, including both singular disc corners.
Use: the real centring correction has a derived inverse domain and a
sharp actual hidden remainder, without a continuous-centre assumption.
Article: main_krylov, thm:local(c), genuine centred hidden-entry radius.
Proof: actual observations give the closed unit disc and original Schur
interval. Its exact midpoint identities give the centred bound; at a
singular corner the cross coordinate vanishes and true contraction gives
the remaining diagonal bound directly. The actual centre is a proved
original planar completion at the interval midpoint. -/
theorem hiddenPlane_observed_centre
    (T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hT : T.toLinearMap.IsSymmetric) (hbound : ‖T‖≤1)
    (e h : EuclideanSpace ℝ (Fin n)) (he : ‖e‖=1) (hh : ‖h‖=1) (heh : inner ℝ e h=0) :
    let y := inner ℝ e (T e)
    let a := inner ℝ e (T h)
    let g := inner ℝ h (T h)
    0≤ hiddenPlaneHalfWidth a g ∧ hiddenPlaneHalfWidth a g≤1 ∧
      |y-hiddenPlaneCentre a g|≤ hiddenPlaneHalfWidth a g ∧
      ‖planarMatrix e h (hiddenPlaneCentre a g) a g‖≤1 := by
  let y := inner ℝ e (T e)
  let a := inner ℝ e (T h)
  let g := inner ℝ h (T h)
  have hobs := hiddenPlane_observed_interval T hT hbound e h he hh heh
  have hdisc : a^2+g^2≤1 := hobs.1
  have hd : 0≤1-g^2 := by nlinarith [sq_nonneg a]
  have hupper : hiddenPlaneHalfWidth a g≤1 := by
    unfold hiddenPlaneHalfWidth
    have hn := div_nonneg (sq_nonneg a) hd
    linarith
  have hcentre : ‖planarMatrix e h (hiddenPlaneCentre a g) a g‖≤1 := by
    have hc := hiddenPlane_completion_bound e h he hh heh a g 0 hdisc (by norm_num)
    simpa only [zero_mul,add_zero] using hc
  suffices hb : 0≤ hiddenPlaneHalfWidth a g ∧ |y-hiddenPlaneCentre a g|≤ hiddenPlaneHalfWidth a g from
    ⟨hb.1,hupper,hb.2,hcentre⟩
  by_cases hdz : 1-g^2=0
  · have haz : a=0 := by nlinarith [sq_nonneg a]
    have hy : |y|≤1 := by
      simpa only [y,he,one_pow] using contraction_quadratic_bound T hbound e
    rw [haz]
    simpa only [hiddenPlaneHalfWidth,hiddenPlaneCentre,zero_pow (by decide : 2≠0),neg_zero,
      zero_mul,zero_div,sub_zero] using And.intro zero_le_one hy
  have hdp : 0<1-g^2 := lt_of_le_of_ne hd (Ne.symm hdz)
  have hg : |g|<1 := abs_lt.mpr ⟨by nlinarith,by nlinarith⟩
  have hlo := (hobs.2 hg).1
  have hhi := (hobs.2 hg).2
  have hgp : 0<1+g := by linarith [(abs_lt.mp hg).1]
  have hgm : 0<1-g := by linarith [(abs_lt.mp hg).2]
  have hleft : hiddenPlaneCentre a g-hiddenPlaneHalfWidth a g= -1+a^2/(1+g) := by
    unfold hiddenPlaneCentre hiddenPlaneHalfWidth
    field_simp
    ring
  have hright : hiddenPlaneCentre a g+hiddenPlaneHalfWidth a g=1-a^2/(1-g) := by
    unfold hiddenPlaneCentre hiddenPlaneHalfWidth
    field_simp
    ring
  have hn : 0≤ hiddenPlaneHalfWidth a g := by
    unfold hiddenPlaneHalfWidth
    exact sub_nonneg.mpr ((div_le_one hdp).mpr (by linarith))
  exact ⟨hn,abs_le.mpr ⟨by rw [← hleft] at hlo;linarith,by rw [← hright] at hhi;linarith⟩⟩

/-- On a complete actual orthonormal plane, the difference between the
true symmetric operator and its actual observed-column centre is exactly
the original one hidden rank-one action.
Use: genuine centred output errors have precisely the sharp unknown-entry
remainder, rather than a generic norm perturbation upper estimate.
Article: main_krylov, thm:local(c), actual centred hidden-model identity.
Proof: true completeness decomposes the real two images and each physical
input; genuine symmetry fixes the shared cross coefficient. The original
planar centre action cancels both actually observed column entries. -/
theorem hiddenPlane_centre_difference
    (T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hT : T.toLinearMap.IsSymmetric) (e h : EuclideanSpace ℝ (Fin n))
    (hfull : ∀ v : EuclideanSpace ℝ (Fin n),(inner ℝ e v) • e+(inner ℝ h v) • h=v)
    (v : EuclideanSpace ℝ (Fin n)) :
    let y := inner ℝ e (T e)
    let a := inner ℝ e (T h)
    let g := inner ℝ h (T h)
    T v-Matrix.toEuclideanCLM (𝕜 := ℝ) (planarMatrix e h (hiddenPlaneCentre a g) a g) v=
      ((y-hiddenPlaneCentre a g)*inner ℝ e v) • e := by
  let y := inner ℝ e (T e)
  let a := inner ℝ e (T h)
  let g := inner ℝ h (T h)
  have hcross : inner ℝ h (T e)=a := (real_inner_comm (T e) h).trans (hT e h)
  have hTe : T e=y • e+a • h := by rw [← hfull (T e),hcross]
  have hTh : T h=a • e+g • h := (hfull (T h)).symm
  have hv : T v=(inner ℝ e v) • T e+(inner ℝ h v) • T h := by
    conv_lhs => rw [← hfull v,map_add,map_smul,map_smul]
  change T v-Matrix.toEuclideanCLM (𝕜 := ℝ) (planarMatrix e h (hiddenPlaneCentre a g) a g) v=
    ((y-hiddenPlaneCentre a g)*inner ℝ e v) • e
  rw [hv,hTe,hTh,planarMatrix_action]
  module

end
end krylov.OneGradient
