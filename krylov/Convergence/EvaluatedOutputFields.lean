import krylov.Convergence.EvaluatedFields
import krylov.Convergence.OneGradientOutputTaylor
import krylov.Methods.EvaluatedLaunch

/-!
Article: main_krylov, prop:EL and lem:cycle-transfer.
Use: derive C-two regularity of the genuine full semantic output from
primitive observed trial charts. Initial-gradient drift and the semantic
output operator vary jointly in their true finite coordinates.
Source: actual evaluated-launch query induction, virtual model domains and full CG termination.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set krylov.Methods krylov.Reference krylov.Functions krylov.Stability
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- The actual evaluated-launch semantic output on its genuine quadratic
reference is exactly the true CG residual. Article: prop:EL. -/
theorem evaluatedLaunch_reference_output_gradient
    (trial : History E → ℝ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v,v≠0 →0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (ht : ∀ i<N,trial (oneGradientRun (evaluatedLaunchMethod trial) (fun _=>Q) g i)≠0) :
    (evaluatedLaunchMethod trial).outputGradient Q (oneGradientRun (evaluatedLaunchMethod trial) (fun _=>Q) g N)=
      CG.gradient Q g N := by
  let m := evaluatedLaunchMethod trial
  let H := oneGradientRun m (fun _=>Q) g N
  have href := (evaluated_launch_reference trial Q hQ hpos g N hpre ht N le_rfl).1
  have hg := oneGradientRun_quadratic_gradient m Q g N
  change H.gradient+Q (m.output H)=_
  change H.gradient=g+Q H.displacement at hg
  rw [hg,add_assoc,←map_add]
  change g+Q (m.outputDisplacement H)=_
  rw [href,CG.gradient_displacement]

/-- Primitive C-two trial charts imply C-two of the complete independent
operator output at the true quadratic reference. Article: prop:EL, V1. -/
theorem evaluatedLaunchFiniteOutput_contDiffAt
    (trial : History E → ℝ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v,v≠0 →0 < inner ℝ v (Q v))
    (N : ℕ) (g : E) (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (ht : ∀ i<N,trial (oneGradientRun (evaluatedLaunchMethod trial) (fun _=>Q) g i)≠0)
    (hT : ∀ i<N,ContDiffAt ℝ 2 (trialCoordinate trial i)
      (oneGradientData (evaluatedLaunchMethod trial) (fun _=>Q) g i)) :
    ContDiffAt ℝ 2 (oneGradientFiniteOutput (evaluatedLaunchMethod trial) Q N) (g,0) := by
  let A := fun z : E × ((Fin N → E →L[ℝ] E) × (E →L[ℝ] E))=>fcFiniteOperatorPath Q N z.2.1
  have hA (i : ℕ) : ContDiffAt ℝ 2 (fun z=>A z i) (g,0) := by
    by_cases hi : i<N
    · simp only [A,fcFiniteOperatorPath,dite_eq_left hi]
      let e := ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Fin N=>E →L[ℝ] E) ⟨i,hi⟩
      exact contDiffAt_const.add (e.contDiff.contDiffAt.comp (g,0) contDiffAt_snd.fst)
    · simp only [A,fcFiniteOperatorPath,dite_eq_right hi]
      exact contDiffAt_const
  have hAz : A (g,0)=fun _=>Q := fcFiniteOperatorPath_zero Q N
  have hh := quadraticEvaluatedLaunch_output_contDiffAt trial A (fun z=>Q+z.2.2) Prod.fst (g,0)
    hA (contDiffAt_const.add contDiffAt_snd.snd) contDiffAt_fst Q hAz hQ hpos N hpre ht
    (by rw [hAz];exact hT)
  exact hh.2

/-- The complete finite semantic map is exactly the true quadratic zero
at every full-atom reference with nonzero primitive trials. Article: prop:EL. -/
theorem evaluatedLaunchFiniteOutput_reference_zero {n : ℕ}
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hcount : referenceAtomCount base hb g=n)
    (ht : ∀ i<n,trial (oneGradientRun (evaluatedLaunchMethod trial)
      (fun _=>cgOperator base) g i)≠0) :
    oneGradientFiniteOutput (evaluatedLaunchMethod trial) (cgOperator base) n (g,0)=0 := by
  have href := evaluatedLaunch_reference_output_gradient trial (cgOperator base)
    (cgOperator_positive base hb).1 (cgOperator_positive base hb).2 g n
    (fun i hi=>cg_nonstagnation base hb g i (by rw [hcount];exact hi)) ht
  have hs := cg_terminates base hb g
  rw [hcount] at hs
  simpa [oneGradientFiniteOutput,fcFiniteOperatorPath_zero,hs] using href

end
end krylov.Convergence
