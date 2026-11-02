import krylov.Correction.CycleData
import krylov.Methods.RFCPhase
import krylov.Methods.ProbedModelReference

/-!
Article: main_krylov, thm:C, the true final RFC model correction.
Use: identify actual returned gradients with the real inverse-model residual
formula on derived gate and inverse domains before applying asymptotics.
Source: actual RFC array execution, genuine positive CG model domains and
the already proved exact physical projected-correction equation.
-/

namespace krylov.Correction
noncomputable section
open Matrix Filter Asymptotics Topology krylov.Methods krylov.Reference krylov.Stability
open scoped Matrix.Norms.L2Operator InnerProductSpace
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The actual full RFC correction phase equals its genuine full augmented model tree on a derived neighborhood.
Use: the final asymptotic solve is tied to actual gate acceptance and real observed query execution.
Article: main_krylov, thm:C and apD:prefix, actual final model solve.
Proof: the actual old arrays are analytic with positive nonzero CG steps and
true quadratic images. Their observed defect is zero at the reference, hence
the real gate passes locally; the existing exact array-execution theorem then identifies the phase. -/
theorem full_phase_execution_eventually (count : ℕ)
    (A B : X → ℕ → E →L[ℝ] E) (g : X → E)
    (hA : ∀ i, AnalyticAt ℝ (fun z => A z i) 0)
    (hB : ∀ i, AnalyticAt ℝ (fun z => B z i) 0) (hg : AnalyticAt ℝ g 0)
    (Q : E →L[ℝ] E) (hA0 : A 0=(fun _ => Q)) (hB0 : B 0=(fun _ => Q))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (k : ℕ) (hk : 0<k) (hpre : ∀ i≤k, CG.gradient Q (g 0) i≠0) :
    let m := rfcMethod fullMemory count (E := E)
    let U := fun z => probedStepBasis m (A z) (B z) (g z) k
    let Z := fun z => probedImageBasis m (A z) (B z) (g z) k
    ∀ᶠ z in 𝓝 (0 : X), probedPhase m (A z) (B z) (g z) k=
      runCorrections (repeatedModelTree (U z) (pairModel (U z) (Z z)) count
        (fullPostSearch count (A z) (B z) (g z) k)) (B z k)
        (fullPostSearch count (A z) (B z) (g z) k) := by
  -- The existing observed gate is proved accepted on the actual analytic old-pair family.
  let m := rfcMethod fullMemory count (E := E)
  let S := fun z (j : Fin k) => probedStep m (A z) (B z) (g z) (k-1-j.val)
  let Y := fun z (j : Fin k) => probedSecant m (A z) (B z) (g z) (k-1-j.val)
  have hd := full_cycle_data_regular count A B g hA hB hg Q hA0 hB0 hQ hpos k hpre
  have hm : ∀ a, CG.gradient Q (g 0) a≠0 → 0<a → 0<fullMemory a := fun _ _ ha => ha
  have href := rfc_reference_augmented_data fullMemory count Q hQ hpos (g 0) hm k hpre
  rw [show min (fullMemory k) k=k from min_self k] at href
  have hn (j : Fin k) : S 0 j≠0 := by
    have hj := href.1 j.succ
    dsimp only [S]
    rw [hA0,hB0]
    exact hj
  have hyQ (j : Fin k) : Y 0 j=Q (S 0 j) := by
    have hj := congrFun href.2.1 j.succ
    dsimp only [Y,S]
    rw [hA0,hB0]
    exact hj
  have hgate := quadratic_pairDefect_gate S Y 0 (fun j => (hd.2.1 j.succ).continuousAt)
    (fun j => (hd.2.2.1 j.succ).continuousAt) Q hQ hpos hn hyQ
  filter_upwards [hgate] with z hz
  have he := probedRFC_phase_array fullMemory count (A z) (B z) (g z) k
  rw [show min (fullMemory k) k=k from min_self k] at he
  rw [he,rfcArrayPhase,ite_eq_left ⟨hk,hz⟩]
  rfl

/-- The real final RFC model has a proved nonsingular neighborhood around the actual quadratic reference.
Use: every inverse in the actual final projected identity has its true model domain discharged.
Article: main_krylov, thm:C, H invertible near the nondegenerate reference.
Proof: actual primitive model regularity gives determinant continuity, and
genuine CG consistency gives the already proved positive quadratic observed model. -/
theorem full_model_unit_eventually (count : ℕ)
    (A B : X → ℕ → E →L[ℝ] E) (g : X → E)
    (hA : ∀ i, AnalyticAt ℝ (fun z => A z i) 0)
    (hB : ∀ i, AnalyticAt ℝ (fun z => B z i) 0) (hg : AnalyticAt ℝ g 0)
    (Q : E →L[ℝ] E) (hA0 : A 0=(fun _ => Q)) (hB0 : B 0=(fun _ => Q))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (k : ℕ) (hpre : ∀ i≤k, CG.gradient Q (g 0) i≠0) :
    let m := rfcMethod fullMemory count (E := E)
    let H := fun z => pairModel (probedStepBasis m (A z) (B z) (g z) k)
      (probedImageBasis m (A z) (B z) (g z) k)
    IsUnit (H 0).det ∧ ∀ᶠ z in 𝓝 (0 : X), IsUnit (H z).det := by
  -- Genuine positive quadratic model data supply the inverse domain before continuity is used.
  let m := rfcMethod fullMemory count (E := E)
  let H := fun z => pairModel (probedStepBasis m (A z) (B z) (g z) k)
    (probedImageBasis m (A z) (B z) (g z) k)
  have hc := (full_cycle_data_regular count A B g hA hB hg Q hA0 hB0 hQ hpos k hpre).2.2.2
  have hp : (H 0).PosDef := by
    dsimp only [H]
    rw [hA0,hB0]
    exact quadratic_probedModel_posDef m (rfcMethod_consistent fullMemory (fun _ ha => ha) count)
      Q hQ hpos (g 0) k (fun a ha => hpre a (by omega))
  have hu : IsUnit (H 0).det := isUnit_iff_ne_zero.mpr hp.det_pos.ne'
  exact ⟨hu,((continuous_id.matrix_det.continuousAt.comp hc.continuousAt).eventually_ne
    (isUnit_iff_ne_zero.mp hu)).mono fun _ hz => isUnit_iff_ne_zero.mpr hz⟩

/-- The actual returned RFC gradient satisfies its exact projected inverse-model identity on a derived neighborhood.
Use: the cubic expansion will apply to the real policy output after its actual final correction.
Article: main_krylov, thm:C, Uᵀg₊=−(UᵀBU−H)H⁻¹Uᵀg′.
Proof: the genuine gate-execution theorem identifies the actual single query;
the genuine model-domain theorem permits the already proved exact coefficient
solve identity, lifted to the actual Euclidean projected residual. -/
theorem full_projected_correction_eventually
    (A B : X → ℕ → E →L[ℝ] E) (g : X → E)
    (hA : ∀ i, AnalyticAt ℝ (fun z => A z i) 0)
    (hB : ∀ i, AnalyticAt ℝ (fun z => B z i) 0) (hg : AnalyticAt ℝ g 0)
    (Q : E →L[ℝ] E) (hA0 : A 0=(fun _ => Q)) (hB0 : B 0=(fun _ => Q))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (k : ℕ) (hk : 0<k) (hpre : ∀ i≤k, CG.gradient Q (g 0) i≠0) :
    let m := rfcMethod fullMemory 1 (E := E)
    let U := fun z => probedStepBasis m (A z) (B z) (g z) k
    let H := fun z => pairModel (U z) (probedImageBasis m (A z) (B z) (g z) k)
    ∀ᶠ z in 𝓝 (0 : X), projectedResidual (U z) (probedGradient m (A z) (B z) (g z) (k+1))=
      -(Matrix.toEuclideanCLM (𝕜 := ℝ) ((correctionCompression (U z) (B z k)-H z)*(H z)⁻¹)
        (projectedResidual (U z) (fullPostSearch 1 (A z) (B z) (g z) k))) := by
  -- Match the actual returned query gradient before invoking the exact nonsingular model equation.
  filter_upwards [full_phase_execution_eventually 1 A B g hA hB hg Q hA0 hB0 hQ hpos k hk hpre,
    (full_model_unit_eventually 1 A B g hA hB hg Q hA0 hB0 hQ hpos k hpre).2] with z hz hu
  rw [probedGradient_succ,hz]
  simp only [repeatedModelTree,runCorrections]
  have he := modelCorrection_projected (probedStepBasis (rfcMethod fullMemory 1) (A z) (B z) (g z) k)
    _ hu (B z k) (fullPostSearch 1 (A z) (B z) (g z) k)
  rw [Matrix.neg_mulVec] at he
  simpa only [projectedResidual,Matrix.toEuclideanCLM_toLp,WithLp.toLp_neg] using congrArg (WithLp.toLp 2) he

end
end krylov.Correction
