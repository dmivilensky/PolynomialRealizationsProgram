import krylov.OneGradient.RecordedProjection
import krylov.Methods.NazarethInformation
set_option autoImplicit false
/-!
Article: main_krylov, prop:classical(b), original Dixon predicted gradient.
Use: implement the actual newly returned-gradient projection with the observed
images in place of physical steps, then prove its genuine predicted CG value.
Source: main_krylov's reproduced Dixon75 Section 3 correction formulas and
the actual real recorded projection/virtual-model dictionary. -/

namespace krylov.Methods
noncomputable section
open krylov.Reference krylov.OneGradient
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The original observed gradient projection uses exactly the same real
own-newly-returned-gradient coefficients as the source point correction,
with actual measured images in place of physical steps.
Use: the predicted gradient is a genuine data-only observed vector.
Article: main_krylov, prop:classical(b), Dixon75 Section 3. -/
def recordedProjectionImage (H : History E) : E :=
  ((H.records.zip H.pairs).map (fun rp =>
    (-inner ℝ rp.2.1 rp.1.gradient/inner ℝ rp.2.1 rp.2.2) • rp.2.2)).sum

/-- The literal original predicted gradient from the actual evaluated point
and genuine full observed gradient projection.
Use: named classical directions consume this real history-only predictor.
Article: main_krylov, prop:classical(b), Dixon75 Section 3. -/
def recordedPredictedGradient (H : History E) : E := H.gradient+recordedProjectionImage H

/-- On genuine quadratic observations the actual image projection is the
true operator action on the literal original recorded point correction.
Use: the same real coefficients give the source predicted point and gradient,
without an extra matrix query or a substitute final residual numerator.
Article: main_krylov, prop:classical(b).
Proof: each real pair image is its actual quadratic action, and linearity
commutes with the identical genuinely observed finite coefficient sum. -/
theorem recorded_projection_image_quadratic (H : History E) (Q : E →L[ℝ] E)
    (hy : ∀ p∈H.pairs,p.2=Q p.1) :
    recordedProjectionImage H=Q (recordedProjectionCorrection H) := by
  rw [recordedProjectionImage,recordedProjectionCorrection,map_list_sum,List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro rp hrp
  dsimp only [Function.comp_apply]
  rw [map_smul,hy rp.2 (List.of_mem_zip hrp).2]

/-- The literal original predicted gradient equals the true CG gradient on
the real evaluated-launch transcript with arbitrary nonzero observed trials.
Use: the actual predicted-gradient classical directions have a derived true
reference input, rather than a supplied predicted-gradient correctness field.
Article: main_krylov, prop:classical(b), Dixon75 Section 3.
Proof: true quadratic secants identify the actual image projection with the
operator action of its original point correction. The proved real recorded
correction is the genuine virtual solve, whose actual predicted gradient is CG. -/
theorem evaluated_recorded_predicted_gradient (trial : History E → ℝ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hpre : ∀ j<N,CG.gradient Q g j≠0)
    (ht : ∀ j<N,trial (oneGradientRun (evaluatedLaunchMethod trial) (fun _ => Q) g j)≠0)
    (k : ℕ) (hk : k≤N) :
    recordedPredictedGradient (oneGradientRun (evaluatedLaunchMethod trial) (fun _ => Q) g k)=CG.gradient Q g k := by
  let method := evaluatedLaunchMethod trial
  let H := oneGradientRun method (fun _ => Q) g k
  have hy : ∀ p∈H.pairs,p.2=Q p.1 := oneGradientRun_pairs_quadratic method Q g k
  have hya (i : Fin H.pairs.length) : windowImages H.pairs i=Q (windowSteps H.pairs i) :=
    hy (H.pairs.get i) (List.get_mem _ i)
  change H.gradient+recordedProjectionImage H=_
  rw [recorded_projection_image_quadratic H Q hy,
    evaluated_recorded_projection trial Q hQ hpos g N hpre ht k hk,← virtualGradient_quadratic H.pairs Q _ hya]
  exact (evaluated_launch_reference trial Q hQ hpos g N hpre ht k hk).2.1

/-- The actual observed gradient projection stays in the genuine observed
span on every supplied history, including singular and incompatible data.
Use: predicted-gradient classical algorithms have actual source admissibility.
Article: main_krylov, prop:classical and def:classes(M1).
Proof: each actual zipped pair contributes only its own genuinely observed
secant difference, scaled by real already observed data; sum in the true span. -/
theorem recordedProjectionImage_mem_observedSpan (H : History E) : recordedProjectionImage H∈H.observedSpan := by
  apply list_sum_mem
  intro v hv
  obtain ⟨rp,hrp,rfl⟩ := List.mem_map.mp hv
  apply Submodule.smul_mem
  apply Submodule.subset_span
  exact Or.inl (Or.inr ⟨rp.2,(List.of_mem_zip hrp).2,rfl⟩)

/-- The literal predicted gradient is available in the genuine observed span
for every supplied complete history.
Use: both actual predicted-gradient CG and BFGS policies use available data.
Article: main_krylov, prop:classical and def:classes(M1).
Proof: add the actual current gradient and its proved observed image correction. -/
theorem recordedPredictedGradient_mem_observedSpan (H : History E) : recordedPredictedGradient H∈H.observedSpan :=
  H.observedSpan.add_mem H.gradient_mem_observedSpan (recordedProjectionImage_mem_observedSpan H)

end
end krylov.Methods
