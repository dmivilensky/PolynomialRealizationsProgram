import krylov.Methods.VirtualTrajectory
set_option autoImplicit false
/-!
Article: main_krylov, thm:E1, genuine reference unevaluated output gradient.
Use: identify the actual semantic output gradient of full-memory XRFC with its true original CG gradient for every genuine bounded nonzero trial prefix.
Source: actual quadratic oracle telescoping, original virtual-reference point theorem and the true computed CG affine gradient identity.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The true semantic unevaluated full-memory XRFC gradient on its original quadratic reference equals the genuine measured CG gradient.
Use: The true semantic unevaluated full-memory XRFC gradient on its original quadratic reference equals the genuine measured CG gradient.
Article: main_krylov, thm:E1, genuine reference unevaluated output gradient.
Proof: Telescope the actual quadratic gradient and output correction, identify the genuine virtual reference displacement and use the original CG affine gradient identity. -/
theorem xrfc_reference_output_gradient (trial : History E → ℝ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (ht : ∀ i<N,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => Q) g i)≠0) :
    let m := xrfcMethod fullMemory trial
    m.outputGradient Q (oneGradientRun m (fun _ => Q) g N)=CG.gradient Q g N := by
  -- Evaluate the genuine quadratic gradient at the actual virtual output point using the true original oracle balance.
  let m := xrfcMethod fullMemory trial (E := E)
  let H := oneGradientRun m (fun _ => Q) g N
  have href := (xrfc_full_reference trial Q hQ hpos g N hpre ht N le_rfl).1
  have hg := oneGradientRun_quadratic_gradient m Q g N
  dsimp only at href hg ⊢
  change H.gradient+Q (m.output H)=_
  change H.gradient=g+Q H.displacement at hg
  rw [hg,add_assoc,← map_add]
  change g+Q (m.outputDisplacement H)=_
  rw [href,CG.gradient_displacement]
end
end krylov.Methods
