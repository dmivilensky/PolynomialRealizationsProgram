import krylov.Methods.FinalizedOutput
import krylov.Methods.ProbedStepBasis
import krylov.Methods.WindowCoordinates
import krylov.Methods.ProjectedModel

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:mu(a), actual final latest-model coordinates.
Use: identify the real appended model solve and its genuine observed image
family, with primitive-derived regularity and exact quadratic images.
Source: actual chronological pair coordinates and genuine secant defect identity.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference krylov.Stability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The genuine observed image family consists of the actual current probe and all true old chronological secants.
Use: The genuine observed image family consists of the actual current probe and all true old chronological secants.
Article: main_krylov, apB:lem:mu(a), actual final latest-model coordinates.
Proof: Read the real executed oracle transcript in the same newest-first coordinates as the actual full step basis. -/
def probedImageBasis (m : ProbedMethod E) (A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) : Fin (k+1) → E :=
  Fin.cons (probedProbe m A B g k) (fun i : Fin k => probedSecant m A B g (k-1-i.val))

/-- The actual appended latest-model correction tree equals its genuine fixed-coordinate full observed-model tree.
Use: The actual appended latest-model correction tree equals its genuine fixed-coordinate full observed-model tree.
Article: main_krylov, apB:lem:mu(a), actual final latest-model coordinates.
Proof: Identify every real current and old observed pair, then reuse physical invariance of the actual correction tree under the true finite coordinate cast. -/
theorem latestAfter_coordinates (m : ProbedMethod E) (A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) (gp : E) :
    latestAfter m (methodRun m A B g k) (probedProbe m A B g k) gp=
      repeatedModelTree (probedStepBasis m A B g k)
        (pairModel (probedStepBasis m A B g k) (probedImageBasis m A B g k)) 1 gp := by
  -- Fix the true chronological pairs before transporting the actual entire correction tree.
  let s := probedStep m A B g
  let y := probedSecant m A B g
  let d := probedDirection m A B g k
  let z := probedProbe m A B g k
  let W := (d,z)::executedPairs s y k
  have hlen : W.length=k+1 := by simp only [W,List.length_cons,executedPairs_length]
  have hU : windowSteps W=(probedStepBasis m A B g k) ∘ finCongr hlen := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · have hj : j.val<k := by simpa only [executedPairs_length] using j.isLt
      exact congrArg Prod.fst (executedPairs_get s y k j.val hj)
  have hZ : windowImages W=(probedImageBasis m A B g k) ∘ finCongr hlen := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · have hj : j.val<k := by simpa only [executedPairs_length] using j.isLt
      exact congrArg Prod.snd (executedPairs_get s y k j.val hj)
  unfold latestAfter
  rw [methodRun_pairs_executed]
  exact repeatedModelTree_window_coordinates W hlen _ _ hU hZ 1 gp

/-- The actual full observed image family is C-two on every genuine smooth source-class active prefix.
Use: The actual full observed image family is C-two on every genuine smooth source-class active prefix.
Article: main_krylov, apB:lem:mu(a), actual final latest-model coordinates.
Proof: Derive true probe and gradient-prefix regularity from the actual primitive coefficient representation; form each genuine old gradient difference. -/
theorem smoothProbed_imageBasis_regular (M : SmoothProbedClass E)
    (A B : ℝ → ℕ → E →L[ℝ] E) (g : E) (k : ℕ)
    (hA : ∀ i<k+1, ContDiffAt ℝ 2 (fun t => A t i) 0)
    (hB : ∀ i<k+1, ContDiffAt ℝ 2 (fun t => B t i) 0)
    (Q : E →L[ℝ] E) (hA0 : A 0=fun _ => Q) (hB0 : B 0=fun _ => Q)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (hpre : ∀ i<k+1, CG.gradient Q g i≠0) :
    ContDiffAt ℝ 2 (fun t => probedImageBasis M.policy (A t) (B t) g k) 0 := by
  -- Primitive smooth membership supplies the genuine probe and every shorter executed gradient prefix.
  have hs := M.smooth Q hQ hpos g (k+1) hpre
  have hG (j : ℕ) (hj : j≤k+1) : ContDiffAt ℝ 2 (fun t => probedGradient M.policy (A t) (B t) g j) 0 :=
    smoothProbed_gradient_regular M.policy M.consistent A B (fun _ => g) 0 j
      (fun i hi => hA i (hi.trans_le hj)) (fun i hi => hB i (hi.trans_le hj)) contDiffAt_const
      Q hA0 hB0 hQ hpos (fun i hi => hpre i (hi.trans_le hj)) (hs.mono M.policy hj)
  apply contDiffAt_pi.mpr
  refine Fin.cases ?_ (fun i => ?_)
  · exact (smoothProbed_fields_regular M.policy M.consistent A B (fun _ => g) 0 (k+1) hA hB contDiffAt_const
      Q hA0 hB0 hQ hpos hpre hs k (by omega)).2.1
  · exact (hG (k-1-i.val+1) (by omega)).sub (hG (k-1-i.val) (by omega))

/-- On every genuine quadratic execution the actual full observed image family is the true quadratic operator applied to the real step family.
Use: On every genuine quadratic execution the actual full observed image family is the true quadratic operator applied to the real step family.
Article: main_krylov, apB:lem:mu(a), actual final latest-model coordinates.
Proof: The real current probe has this definition, while the actual secant defect identity vanishes when the two genuine segment operators coincide. -/
theorem quadratic_imageBasis (m : ProbedMethod E) (Q : E →L[ℝ] E) (g : E) (k : ℕ) :
    probedImageBasis m (fun _ => Q) (fun _ => Q) g k=
      fun i => Q (probedStepBasis m (fun _ => Q) (fun _ => Q) g k i) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · have he := probedSecant_defect_identity m (fun _ => Q) (fun _ => Q) g (k-1-j.val)
    simp only [sub_self,_root_.zero_apply] at he
    exact sub_eq_zero.mp he
end
end krylov.Methods
