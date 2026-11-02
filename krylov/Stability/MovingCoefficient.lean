import krylov.Stability.C1CubicProduct
import Mathlib.Analysis.Calculus.ContDiff.Operations
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), genuine moving coefficient comparison.
Use: freeze primitive C-one reference frames in the actual quadratic
fresh-defect/staircase expression with a proved cubic cost.
Source: true finite observed increments, genuine vanishing-middle and
vanishing-input coefficient freezing, and actual order-product bounds.
-/

namespace krylov.Stability
noncomputable section
open Filter Topology Asymptotics
open scoped BigOperators
variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι κ : Type*}

/-- The real old-flag drift, with explicitly supplied smooth reference
coefficients and actual physical increments.
Use: one expression covers both the moving source frame and its frozen
known-reference representative, retaining the same actual increments.
Article: main_krylov, thm:local(a), moving fresh-defect expression. -/
def movingDriftCoefficient (J : Finset κ) (P : κ → X → E →L[ℝ] E)
    (R : X → E →L[ℝ] E) (D : κ → X → E →L[ℝ] E) (h : X → E) (z : X) : E :=
  ∑ j∈J,(P j z*R z) (D j z (R z (h z)))

/-- Freezing the actual C-one coefficients of a real fresh drift costs
quadratic order while retaining each actual physical increment.
Use: its later multiplication by another actual increment is cubic.
Article: main_krylov, thm:local(a), moving incoming-frame comparison.
Proof: apply the genuine vanishing-middle remainder separately to every
real old flag and actual increment, then sum the finite true remainders. -/
theorem movingDrift_freeze_quadratic (J : Finset κ) (P : κ → X → E →L[ℝ] E)
    (R : X → E →L[ℝ] E) (D : κ → X → E →L[ℝ] E) (h : X → E)
    (hP : ∀ j∈J,ContDiffAt ℝ 1 (P j) 0) (hR : ContDiffAt ℝ 1 R 0)
    (hD : ∀ j∈J,ContDiffAt ℝ 1 (D j) 0) (hzero : ∀ j∈J,D j 0=0)
    (hh : ContDiffAt ℝ 1 h 0) :
    (fun z => movingDriftCoefficient J P R D h z-
      ∑ j∈J,(P j 0*R 0) (D j z (R 0 (h 0)))) =O[𝓝 0] (fun z => ‖z‖^2) := by
  have hterms (j : κ) (hj : j∈J) := c1_vanishing_middle_remainder
    (fun z => P j z*R z) (D j) (fun z => R z (h z))
    (((hP j hj).mul hR).differentiableAt (by norm_num))
    ((hD j hj).differentiableAt (by norm_num))
    ((hR.clm_apply hh).differentiableAt (by norm_num)) (hzero j hj)
  apply (IsBigO.sum (fun j hj => hterms j hj)).congr_left
  intro z
  simp only [movingDriftCoefficient,Finset.sum_apply,Finset.sum_sub_distrib]

/-- The complete real quadratic staircase/fresh-drift expression has
a cubic coefficient-freezing remainder in the full primitive parameter.
Both increments remain actual and the true measured relative error is
retained. Smooth reference coefficients and the scale may all move.
Use: proves the original own-A0 frame transfer without a supplied output
jet or a smoothness assumption on the full actual trajectory.
Article: main_krylov, thm:local(a), genuine moving quadratic coefficient.
Proof: the real fresh drift is C-one and zero at reference. Freeze the
outer staircase coefficients by the true vanishing-input cubic theorem.
Its inner drift has a quadratic frame remainder, multiplied by a genuine
first-order physical increment. The last-pivot product uses its quadratic
vanishing-middle remainder times the real first-order measured error. -/
theorem movingQuadraticCoefficient_freeze_cubic (I : Finset ι) (J : Finset κ)
    (U V : ι → X → E →L[ℝ] E) (D : ι → X → E →L[ℝ] E)
    (P : κ → X → E →L[ℝ] E) (R : X → E →L[ℝ] E)
    (C : κ → X → E →L[ℝ] E) (F : X → E →L[ℝ] E)
    (h : X → E) (sigma eps : X → ℝ)
    (hU : ∀ i∈I,ContDiffAt ℝ 1 (U i) 0) (hV : ∀ i∈I,ContDiffAt ℝ 1 (V i) 0)
    (hD : ∀ i∈I,ContDiffAt ℝ 1 (D i) 0) (hD0 : ∀ i∈I,D i 0=0)
    (hP : ∀ j∈J,ContDiffAt ℝ 1 (P j) 0) (hR : ContDiffAt ℝ 1 R 0)
    (hC : ∀ j∈J,ContDiffAt ℝ 1 (C j) 0) (hC0 : ∀ j∈J,C j 0=0)
    (hF : ContDiffAt ℝ 1 F 0) (hF0 : F 0=0) (hh : ContDiffAt ℝ 1 h 0)
    (hsigma : ContDiffAt ℝ 1 sigma 0) (heps : ContDiffAt ℝ 1 eps 0) (heps0 : eps 0=0) :
    let f := movingDriftCoefficient J P R C h
    let f0 := fun z => ∑ j∈J,(P j 0*R 0) (C j z (R 0 (h 0)))
    (fun z => sigma z • ((∑ i∈I,U i z (D i z (V i z (f z))))-
      eps z • R z (F z (R z (h z))))-
        sigma 0 • ((∑ i∈I,U i 0 (D i z (V i 0 (f0 z))))-
          eps z • R 0 (F z (R 0 (h 0))))) =O[𝓝 0] (fun z => ‖z‖^3) := by
  let f := movingDriftCoefficient J P R C h
  let f0 := fun z => ∑ j∈J,(P j 0*R 0) (C j z (R 0 (h 0)))
  have hf : ContDiffAt ℝ 1 f 0 := by
    apply ContDiffAt.sum
    intro j hj
    exact ((hP j hj).mul hR).clm_apply ((hC j hj).clm_apply (hR.clm_apply hh))
  have hfzero : f 0=0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [hC0 j hj,zero_apply,map_zero]
  have hdiff : (fun z => f z-f0 z) =O[𝓝 0] (fun z => ‖z‖^2) :=
    movingDrift_freeze_quadratic J P R C h hP hR hC hC0 hh
  have hterm (i : ι) (hi : i∈I) :
      (fun z => sigma z • U i z (D i z (V i z (f z)))-
        sigma 0 • U i 0 (D i z (V i 0 (f0 z)))) =O[𝓝 0] (fun z => ‖z‖^3) := by
    have hfreeze := c1_vanishing_input_freeze_remainder (fun z => sigma z • U i z) (D i) (V i) f
      ((hsigma.smul (hU i hi)).differentiableAt (by norm_num))
      ((hD i hi).differentiableAt (by norm_num))
      ((hV i hi).differentiableAt (by norm_num)) (hf.differentiableAt (by norm_num)) (hD0 i hi) hfzero
    have hDb : D i =O[𝓝 0] (fun z => ‖z‖) := by
      simpa only [hD0 i hi,sub_zero] using ((hD i hi).differentiableAt (by norm_num)).isBigO_sub.norm_right
    have hvec : (fun z => D i z (V i 0 (f z-f0 z))) =O[𝓝 0] (fun z => ‖z‖^3) := by
      exact (clm_apply_bigO (D i) _ _ _ hDb ((V i 0).isBigO_comp _ (𝓝 0) |>.trans hdiff)).congr_right
        (fun z => by ring)
    have hrest := ((U i 0).isBigO_comp _ (𝓝 0) |>.trans hvec).const_smul_left (sigma 0)
    apply (hfreeze.add hrest).congr_left
    intro z
    change sigma z • U i z (D i z (V i z (f z)))-
      sigma 0 • U i 0 (D i z (V i 0 (f z)))+
      sigma 0 • U i 0 (D i z (V i 0 (f z-f0 z)))=_
    simp only [map_sub,smul_sub]
    abel
  have hsum : (fun z => sigma z • (∑ i∈I,U i z (D i z (V i z (f z))))-
      sigma 0 • (∑ i∈I,U i 0 (D i z (V i 0 (f0 z))))) =O[𝓝 0] (fun z => ‖z‖^3) := by
    apply (IsBigO.sum (fun i hi => hterm i hi)).congr_left
    intro z
    simp only [Finset.sum_apply,Finset.sum_sub_distrib,Finset.smul_sum]
  have hpivot := c1_vanishing_middle_remainder (fun z => sigma z • R z) F (fun z => R z (h z))
    ((hsigma.smul hR).differentiableAt (by norm_num)) (hF.differentiableAt (by norm_num))
    ((hR.clm_apply hh).differentiableAt (by norm_num)) hF0
  have heb : eps =O[𝓝 0] (fun z => ‖z‖) := by
    simpa only [heps0,sub_zero] using (heps.differentiableAt (by norm_num)).isBigO_sub.norm_right
  have hlast : (fun z => eps z •
      (sigma z • R z (F z (R z (h z)))-sigma 0 • R 0 (F z (R 0 (h 0)))))
        =O[𝓝 0] (fun z => ‖z‖^3) := by
    exact ((heb.smul hpivot).congr_left (fun z => rfl)).congr_right (fun z => by simp only [smul_eq_mul];ring)
  apply (hsum.sub hlast).congr_left
  intro z
  simp only [smul_sub,smul_smul]
  module

end
end krylov.Stability
