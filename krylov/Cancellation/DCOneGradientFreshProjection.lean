import krylov.Cancellation.OneGradientFreshObstruction
import krylov.Cancellation.DCSlide
import krylov.Methods.VirtualSolve
set_option autoImplicit false
/-!
Article: main_krylov, apH:dcs2(a), actual exact fresh-only DC-slide coordinates.
Use: prove finite-variation attainability directly on every genuine independent
retained window; no small-variation or full-memory hypothesis is needed.
Source: the true observed tilted solve, actual quadratic window positivity,
and exact native fresh-prefix execution.
-/

namespace krylov.Cancellation
noncomputable section
open Matrix krylov.Methods krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- On quadratic incoming data the genuine one-gradient DC-slide next gradient
is exactly orthogonal to every actually retained independent window column.
Use: the fresh-only attaining statement derives the observed solve domain from
actual positive quadratic data rather than assuming an inverse certificate.
Article: main_krylov, apH:dcs2(a), exact unperturbed old-window cancellation.
Proof: genuine retained secants are Q times their real stored steps. Their
positive operator Gram is invertible. Multiply the original tilted direction
equations by the same nonzero estimate used by the actual evaluated step. -/
theorem dc_one_gradient_quadratic_window_orthogonal
    (memory : ℕ → ℕ) (estimate : History E → ℝ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (k : ℕ)
    (hs : LinearIndependent ℝ (windowSteps (selectedWindow memory
      (oneGradientRun (dcSlideOneGradient memory estimate) (fun _ => Q) g k))))
    (ha : estimate (oneGradientRun (dcSlideOneGradient memory estimate) (fun _ => Q) g k)≠0) :
    let m := dcSlideOneGradient memory estimate
    let W := selectedWindow memory (oneGradientRun m (fun _ => Q) g k)
    coordinates (windowSteps W) (oneGradientGradient m (fun _ => Q) g (k+1))=0 := by
  let m := dcSlideOneGradient memory estimate
  let H := oneGradientRun m (fun _ => Q) g k
  let W := selectedWindow memory H
  let a := estimate H
  let d := deferredDirection (windowSteps W) (windowImages W) H.gradient a
  have hy (i : Fin W.length) : windowImages W i=Q (windowSteps W i) :=
    oneGradientRun_pairs_quadratic m Q g k (W.get i)
      (List.mem_of_mem_take (List.get_mem _ i))
  have hdet : IsUnit (crossGram (windowImages W) (windowSteps W)).det := by
    rw [funext hy]
    exact isUnit_iff_ne_zero.mpr (operatorGram_posDef Q hQ hpos hs).det_pos.ne'
  ext i
  have hc := deferredDirection_conjugacy (windowSteps W) (windowImages W) H.gradient a hdet i
  rw [hy i] at hc
  change inner ℝ (Q (windowSteps W i)) d= -a⁻¹*inner ℝ (windowSteps W i) H.gradient at hc
  change inner ℝ (windowSteps W i) (H.gradient+Q (a • d))=0
  have hsym : inner ℝ (Q (windowSteps W i)) d=inner ℝ (windowSteps W i) (Q d) := hQ (windowSteps W i) d
  rw [map_smul,inner_add_right,real_inner_smul_right,← hsym,hc]
  change inner ℝ (windowSteps W i) H.gradient+a*(-a⁻¹*inner ℝ (windowSteps W i) H.gradient)=0
  field_simp [show a≠0 from ha]
  ring

/-- With only the newest operator changed, actual one-gradient DC-slide leaves
exactly that fresh defect in its genuine original retained-window coordinates.
Use: this is finite-variation attainment of the irreducible fresh residual,
for either sign and every real symmetric physical perturbation.
Article: main_krylov, apH:dcs2(a), exact attaining native coordinates.
Proof: the real fresh scenario has precisely the original quadratic incoming
history and step. Its actual new gradient differs by F times that common step;
the proved original one-gradient tilted solve cancels every other window pairing. -/
theorem dc_one_gradient_newest_coordinates
    (memory : ℕ → ℕ) (estimate : History E → ℝ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (k : ℕ)
    (hs : LinearIndependent ℝ (windowSteps (selectedWindow memory
      (oneGradientRun (dcSlideOneGradient memory estimate) (fun _ => Q) g k))))
    (ha : estimate (oneGradientRun (dcSlideOneGradient memory estimate) (fun _ => Q) g k)≠0)
    (F : E →L[ℝ] E) :
    let m := dcSlideOneGradient memory estimate
    let W := selectedWindow memory (oneGradientRun m (fun _ => Q) g k)
    coordinates (windowSteps W) (oneGradientGradient m (freshOperatorPath (fun _ => Q) k F) g (k+1))=
      coordinates (windowSteps W) (F (oneGradientStep m (fun _ => Q) g k)) := by
  let m := dcSlideOneGradient memory estimate
  let W := selectedWindow memory (oneGradientRun m (fun _ => Q) g k)
  have hz := dc_one_gradient_quadratic_window_orthogonal memory estimate Q hQ hpos g k hs ha
  change coordinates (windowSteps W) (oneGradientGradient m (freshOperatorPath (fun _ => Q) k F) g (k+1))=_
  rw [one_gradient_fresh_gradient]
  ext i
  have hi := congrFun hz i
  change inner ℝ (windowSteps W i) (oneGradientGradient m (fun _ => Q) g (k+1))=0 at hi
  change inner ℝ (windowSteps W i) (oneGradientGradient m (fun _ => Q) g (k+1)+
    F (oneGradientStep m (fun _ => Q) g k))=_
  rw [inner_add_right,hi,zero_add]
  rfl

end
end krylov.Cancellation
