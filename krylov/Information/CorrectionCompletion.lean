import krylov.Information.PhysicalRadius
import krylov.LinearAlgebra.SymmetricBall
import krylov.Methods.CorrectionCount

/-!
Article: main_krylov, thm:centre, admissible intermediate correction actions.
Use: turn the exact single-action hypothesis H4 into actual symmetric physical
perturbations, and replay the genuine at-most-one-query correction phase.
Source: the previously proved symmetric-ball identity (Rump03, Lemma 5.1),
the actual positive metric root and the existing nonanticipating executor.
-/

namespace krylov.Information
noncomputable section
open Matrix krylov.Secant krylov.Reference krylov.LinearAlgebra krylov.Methods
open scoped Matrix.Norms.L2Operator InnerProductSpace
variable {p : ℕ}

/-- A prescribed physical action is attained by an actual symmetric relative-budget perturbation.
Use: construct the intermediate correction replacement required by H4.
Article: main_krylov, thm:centre(iii), symmetric norm-ω single-action completion.
Proof: normalize the actual input and target by the genuine positive metric
root, apply the proved self-adjoint ball-image identity, and reconstruct the
physical symmetric matrix by the inverse canonical congruence. -/
theorem exists_relative_symmetric_image (G : Matrix (Fin p) (Fin p) ℝ) (hG : G.PosDef)
    (u w : EuclideanSpace ℝ (Fin p)) {ω : ℝ} (hω : 0≤ω)
    (hw : ‖cgOperator (metricRoot G)⁻¹ w‖≤ω*‖cgOperator (metricRoot G) u‖) :
    ∃ F : Matrix (Fin p) (Fin p) ℝ, F.IsSymm ∧ relativeBudget G F≤ω ∧ cgOperator F u=w := by
  -- Complete the normalized single action with a true self-adjoint operator.
  obtain ⟨T,hTs,hT,hTu⟩ := exists_selfAdjoint_image
    (cgOperator (metricRoot G) u) (cgOperator (metricRoot G)⁻¹ w) hω hw
  let X := (Matrix.toEuclideanCLM (n := Fin p) (𝕜 := ℝ)).toAlgEquiv.symm T
  have hX : cgOperator X=T :=
    (Matrix.toEuclideanCLM (n := Fin p) (𝕜 := ℝ)).toAlgEquiv.apply_symm_apply T
  have hXs : X.IsSymm := by
    apply Matrix.isHermitian_iff_isSymm.mp
    apply Matrix.isSymmetric_toEuclideanLin_iff.mp
    change (cgOperator X).toLinearMap.IsSymmetric
    rw [hX]
    exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hTs
  let F := metricRoot G*X*metricRoot G
  have hF : F.IsSymm := by
    simp only [F,Matrix.IsSymm,transpose_mul,(metricRoot_isSymm G).eq,hXs.eq,Matrix.mul_assoc]
  have hrel : relativeOperator G F=X := by
    simp only [F,relativeOperator,← Matrix.mul_assoc]
    rw [nonsing_inv_mul _ (metricRoot_det_unit G hG),Matrix.one_mul,
      Matrix.mul_assoc,mul_nonsing_inv _ (metricRoot_det_unit G hG),Matrix.mul_one]
  refine ⟨F,hF,?_,?_⟩
  · rw [relativeBudget,hrel,chebyshev1.opNorm,← Matrix.l2_opNorm_toEuclideanCLM]
    change ‖cgOperator X‖≤ω
    rwa [hX]
  · -- Undo the actual output normalization after applying the completed canonical operator.
    have hcancel : cgOperator (metricRoot G) (cgOperator (metricRoot G)⁻¹ w)=w := by
      have hh := congrArg (fun M => cgOperator M w)
        (mul_nonsing_inv _ (metricRoot_det_unit G hG))
      simpa only [cgOperator,map_mul,mul_apply_eq_comp,map_one,
        one_apply_eq_self] using hh
    change cgOperator (metricRoot G*X*metricRoot G) u=w
    simp only [cgOperator,map_mul,mul_apply_eq_comp]
    change cgOperator (metricRoot G) (cgOperator X (cgOperator (metricRoot G) u))=w
    rw [hX,hTu,hcancel]

/-- H4, including a zero actual correction, has an actual symmetric physical budget witness.
Use: replacing F_k+2Y_k preserves its prescribed action without retaining its full operator norm.
Article: main_krylov, thm:centre, condition H4 and zero-correction convention.
Proof: a zero input has zero target; otherwise use the exact normalized
action inequality in the proved relative symmetric-image construction. -/
theorem exists_relative_action_replacement (G R : Matrix (Fin p) (Fin p) ℝ)
    (hG : G.PosDef) (u : EuclideanSpace ℝ (Fin p)) {ω : ℝ} (hω : 0≤ω)
    (hH4 : u=0 ∨ ‖cgOperator (metricRoot G)⁻¹ (cgOperator R u)‖≤
      ω*‖cgOperator (metricRoot G) u‖) :
    ∃ F : Matrix (Fin p) (Fin p) ℝ, F.IsSymm ∧ relativeBudget G F≤ω ∧
      cgOperator F u=cgOperator R u := by
  apply exists_relative_symmetric_image G hG u (cgOperator R u) hω
  rcases hH4 with hu | hu
  · simp only [hu,map_zero,norm_zero,mul_zero,le_refl]
  · exact hu

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The displacement chosen before the first actual correction observation, or zero when no query is made.
Use: H4 constrains precisely this one action in the source class with at most one query.
Article: main_krylov, thm:centre, u_k. -/
def firstCorrectionStep : CorrectionTree E → E
  | .done => 0
  | .query u _ => u

/-- Matching only the actual first action replays an entire at-most-one-query correction phase.
Use: symmetric H4 completion preserves all intermediate observed data.
Article: main_krylov, thm:centre(iii), one-query replacement replay.
Proof: a stopped phase is independent of the oracle; in a queried phase
the common first answer is recorded and both continuation branches stop. -/
theorem one_correction_replay (q : CorrectionTree E) (hq : CorrectionsAtMostOne q)
    (B C : E →L[ℝ] E) (g : E)
    (hBC : B (firstCorrectionStep q)=C (firstCorrectionStep q)) :
    runCorrections q B g=runCorrections q C g := by
  cases q with
  | done => rfl
  | query u next =>
    change B u=C u at hBC
    have hn := hq (g+C u)
    simp only [runCorrections,hBC,hn]

/-- A whole genuine at-most-one-correction run replays under matching probes and matching first actions.
Use: the completed twin may use different operators outside its actual single queried vectors.
Article: main_krylov, thm:centre(iii), complete history under H4 replacements.
Proof: induct on the executed history; equal past data select the same
probe, line step and correction decision, whose actual single query replays. -/
theorem one_correction_run_replay (m : ProbedMethod E) (hm : OneCorrectionMethod m)
    (A B C D : ℕ → E →L[ℝ] E) (g : E) (N : ℕ)
    (hprobe : ∀ k<N, let H := methodRun m A B g k
      A k (m.direction H)=C k (m.direction H))
    (hquery : ∀ k<N, let H := methodRun m A B g k
      let u := firstCorrectionStep (m.correction H (A k (m.direction H)))
      B k u=D k u) :
    methodRun m A B g N=methodRun m C D g N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    -- Select the true next correction from the already preserved complete history.
    have hpast := ih (fun k hk => hprobe k (by omega)) (fun k hk => hquery k (by omega))
    rw [methodRun,methodRun,← hpast]
    have hp := hprobe N (by omega)
    have hq := one_correction_replay _ (hm _ _) (B N) (D N)
      (searchedGradient (methodRun m A B g N).gradient
        (m.direction (methodRun m A B g N)) (A N (m.direction (methodRun m A B g N))))
      (hquery N (by omega))
    simp only [methodAdvance,← hp]
    rw [hq]

end
end krylov.Information
