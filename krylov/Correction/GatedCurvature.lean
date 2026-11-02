import krylov.Correction.CurvatureScaling

/-!
Article: main_krylov, def:GRFC, the complete positive operator-scaling law.
Use: preserve both actual gates throughout the real GRFC trajectory when
all query operators are multiplied by a common positive scalar.
Source: the proved mixed augmented-model congruence, actual inverse correction
scaling and finite induction on the true retained step/secant history.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference
open scoped Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual gated phase has unchanged gradient and inversely scaled movement under a common positive operator factor.
Use: both real gate decisions, all accepted solves and the FC fallback have their full source covariance.
Article: main_krylov, def:GRFC, phase covariance under A_k,B_k↦cA_k,cB_k.
Proof: the spectral test is identical after the proved positive operator
factor and positive individual column congruence. The normalized defect test
is also identical. Actual exact search leaves the same incoming gradient;
the real accepted correction scales by c⁻¹, cancelled by its true cB oracle. -/
theorem gatedArrayPhase_curvature {p : ℕ} (gamma : ℝ) (s y : Fin p → E) (g d z : E)
    (B : E →L[ℝ] E) (c : ℝ) (hc : 0<c) :
    (gatedArrayPhase gamma (fun i => c⁻¹ • s i) y g d (c • z) (c • B)).movement=
      c⁻¹ • (gatedArrayPhase gamma s y g d z B).movement ∧
    (gatedArrayPhase gamma (fun i => c⁻¹ • s i) y g d (c • z) (c • B)).gradient=
      (gatedArrayPhase gamma s y g d z B).gradient := by
  -- Compare the actual current-plus-old model, whose column factors differ at the head.
  have hd (i : Fin (p+1)) : 0<(Fin.cons 1 (fun _ => c⁻¹) : Fin (p+1) → ℝ) i :=
    Fin.cases zero_lt_one (fun _ => inv_pos.mpr hc) i
  have hgate : matrixSpectralGate gamma
      (pairModel (Fin.cons d (fun i => c⁻¹ • s i)) (Fin.cons (c • z) y)) ↔
      matrixSpectralGate gamma (pairModel (Fin.cons d s) (Fin.cons z y)) := by
    rw [augmentedModel_curvature_scalar s y d z c hc.ne',matrixSpectralGate_scalar gamma _ hc]
    exact matrixSpectralGate_congruence gamma _ _ hd
  simp only [gatedArrayPhase]
  rw [hgate]
  split
  · simp only [rfcArrayPhase,pairDefect_step_scalar s y (inv_pos.mpr hc)]
    split
    · have hχ := augmentedCorrection_curvature_scalar s y d z (searchedGradient g d z) c hc.ne'
      simp only [repeatedModelTree,runCorrections,searchedGradient_probe_scalar g d z c hc.ne']
      rw [hχ]
      simp only [add_zero,_root_.smul_apply,map_smul,smul_smul,inv_mul_cancel₀ hc.ne',one_smul,and_self]
    · simp only [searchedGradient_probe_scalar g d z c hc.ne',smul_zero,and_self]
  · simp only [searchedGradient_probe_scalar g d z c hc.ne',smul_zero,and_self]

/-- Every actual GRFC run is invariant in gradients and directions under a common positive operator factor, with inverse scaling of actual steps.
Use: complete the article's second scaling law through all executed gates and every real retained observation.
Article: main_krylov, def:GRFC, full A₀,E_l,E′,F_k↦c(A₀,E_l,E′,F_k) covariance.
Proof: retain the actual step and actual consecutive-gradient secant in the
induction. The genuine mixed stored-step scaling preserves the true retained
direction. The preceding gated-phase theorem preserves the actual gradient
and scales the real correction displacement; exact search scales the line
step by the same reciprocal factor, completing the true next record. -/
theorem gated_curvature_scalar (memory : ℕ → ℕ) (gamma : ℝ)
    (A B : ℕ → E →L[ℝ] E) (g : E) (c : ℝ) (hc : 0<c) (N : ℕ) :
    let m := gatedMethod memory gamma (E := E)
    probedGradient m (fun k => c • A k) (fun k => c • B k) g N=probedGradient m A B g N ∧
      ∀ i<N,
        m.direction (methodRun m (fun k => c • A k) (fun k => c • B k) g i)=
          m.direction (methodRun m A B g i) ∧
        probedStep m (fun k => c • A k) (fun k => c • B k) g i=c⁻¹ • probedStep m A B g i ∧
        probedSecant m (fun k => c • A k) (fun k => c • B k) g i=probedSecant m A B g i := by
  -- Actual recorded secants stay fixed, whereas actual stored displacements change their units.
  let m := gatedMethod memory gamma (E := E)
  let Ac := fun k => c • A k
  let Bc := fun k => c • B k
  change probedGradient m Ac Bc g N=probedGradient m A B g N ∧ _
  induction N with
  | zero => exact ⟨rfl,by intro i hi; omega⟩
  | succ k ih =>
    have hs : (fun i : Fin (min (memory k) k) => probedStep m Ac Bc g (k-1-i.val))=
        fun i => c⁻¹ • probedStep m A B g (k-1-i.val) := by
      funext i
      have hi := i.isLt
      exact (ih.2 _ (by omega)).2.1
    have hy : (fun i : Fin (min (memory k) k) => probedSecant m Ac Bc g (k-1-i.val))=
        fun i => probedSecant m A B g (k-1-i.val) := by
      funext i
      have hi := i.isLt
      exact (ih.2 _ (by omega)).2.2
    have hd : m.direction (methodRun m Ac Bc g k)=m.direction (methodRun m A B g k) := by
      change windowDirection (selectedWindow memory _) _=windowDirection (selectedWindow memory _) _
      rw [selectedWindow_methodRun,selectedWindow_methodRun,windowDirection_executed_take,windowDirection_executed_take]
      change conjugacyDirection _ _ (probedGradient m Ac Bc g k)=conjugacyDirection _ _ (probedGradient m A B g k)
      rw [hs,hy,ih.1,conjugacyDirection_step_scalar _ _ _ c⁻¹ (inv_ne_zero hc.ne')]
    have hphase : (probedPhase m Ac Bc g k).movement=c⁻¹ • (probedPhase m A B g k).movement ∧
        (probedPhase m Ac Bc g k).gradient=(probedPhase m A B g k).gradient := by
      simp only [m,probedGated_phase_array]
      change (gatedArrayPhase _ _ _ (probedGradient m Ac Bc g k) _ _ _).movement=_ ∧
        (gatedArrayPhase _ _ _ (probedGradient m Ac Bc g k) _ _ _).gradient=_
      rw [hs,hy,ih.1,hd]
      exact gatedArrayPhase_curvature gamma _ _ _ _ _ (B k) c hc
    have hnext : probedGradient m Ac Bc g (k+1)=probedGradient m A B g (k+1) := hphase.2
    have hstep : probedStep m Ac Bc g k=c⁻¹ • probedStep m A B g k := by
      change lineLength (probedGradient m Ac Bc g k) _ _ • _+_=c⁻¹ • _
      rw [ih.1,hd]
      change lineLength (probedGradient m A B g k) _ (c • _) • _+_=c⁻¹ • _
      rw [lineLength_probe_scalar,hphase.1,mul_smul,← smul_add]
      rfl
    refine ⟨hnext,?_⟩
    intro i hi
    by_cases he : i=k
    · subst i
      refine ⟨hd,hstep,?_⟩
      rw [probedSecant,hnext,ih.1]
      rfl
    · exact ih.2 i (by omega)

end
end krylov.Correction
