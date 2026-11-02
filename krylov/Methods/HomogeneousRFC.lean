import krylov.Methods.RFCPhase

/-!
Article: main_krylov, lem:U(c,d), genuine gated RFC trajectory homogeneity.
Use: prove degree-one scaling of the actual executed repeated RFC gradients,
directions, total steps and recorded secants for every pair-retention rule.
Source: actual retained-age coordinates, actual degree-zero inverse coefficients,
scale invariance of the observed gate and real finite-query phase covariance.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every real gated repeated RFC trajectory is homogeneous in the initial gradient, with the same actual branch and true recorded secants.
Use: supplies the actual cone homogeneity of RFC and RFC_k, including full, sliding and restarted memory.
Article: main_krylov, lem:U(c,d), actual homogeneous RFC cycle maps.
Proof: induct over the genuine recorded data. True old steps and secants
scale together, so the real retained direction scales. The real observed gate
is invariant and its repeated query phase scales. Its true returned gradient,
line-plus-correction displacement and consecutive-gradient secant therefore scale. -/
theorem rfc_scalar (memory : ℕ → ℕ) (count : ℕ)
    (A B : ℕ → E →L[ℝ] E) (g : E) (c : ℝ) (hc : c≠0) (N : ℕ) :
    let m := rfcMethod memory count (E := E)
    probedGradient m A B (c • g) N=c • probedGradient m A B g N ∧
      ∀ i<N, m.direction (methodRun m A B (c • g) i)=c • m.direction (methodRun m A B g i) ∧
        probedStep m A B (c • g) i=c • probedStep m A B g i ∧
        probedSecant m A B (c • g) i=c • probedSecant m A B g i := by
  -- Real secants are part of the induction because RFC records all actual correction contributions.
  let m := rfcMethod memory count (E := E)
  change probedGradient m A B (c • g) N=c • probedGradient m A B g N ∧ _
  induction N with
  | zero => exact ⟨rfl,by intro i hi; omega⟩
  | succ k ih =>
    have hs : (fun i : Fin (min (memory k) k) => probedStep m A B (c • g) (k-1-i.val))=
        fun i => c • probedStep m A B g (k-1-i.val) := by
      funext i
      have hi := i.isLt
      exact (ih.2 _ (by omega)).2.1
    have hy : (fun i : Fin (min (memory k) k) => probedSecant m A B (c • g) (k-1-i.val))=
        fun i => c • probedSecant m A B g (k-1-i.val) := by
      funext i
      have hi := i.isLt
      exact (ih.2 _ (by omega)).2.2
    have hd : m.direction (methodRun m A B (c • g) k)=c • m.direction (methodRun m A B g k) := by
      change windowDirection (selectedWindow memory _) _=c • windowDirection (selectedWindow memory _) _
      rw [selectedWindow_methodRun,selectedWindow_methodRun,windowDirection_executed_take,windowDirection_executed_take]
      change conjugacyDirection _ _ (probedGradient m A B (c • g) k)=c • conjugacyDirection _ _ (probedGradient m A B g k)
      rw [hs,hy,ih.1,conjugacyDirection_scalar _ _ _ c hc]
    have hphase : (probedPhase m A B (c • g) k).movement=c • (probedPhase m A B g k).movement ∧
        (probedPhase m A B (c • g) k).gradient=c • (probedPhase m A B g k).gradient := by
      dsimp only [m]
      simp only [probedRFC_phase_array]
      change (rfcArrayPhase _ _ (probedGradient m A B (c • g) k) _ _ _ _).movement=_ ∧
        (rfcArrayPhase _ _ (probedGradient m A B (c • g) k) _ _ _ _).gradient=_
      rw [hs,hy,ih.1,hd,map_smul]
      exact rfcArrayPhase_scalar _ _ _ _ _ (B k) count c hc
    have hnext : probedGradient m A B (c • g) (k+1)=c • probedGradient m A B g (k+1) := hphase.2
    have hstep : probedStep m A B (c • g) k=c • probedStep m A B g k := by
      change lineLength (probedGradient m A B (c • g) k) _ _ • _+_=c • _
      rw [ih.1,hd,map_smul,lineLength_scalar _ _ _ c hc,hphase.1,smul_comm,← smul_add]
      rfl
    refine ⟨hnext,?_⟩
    intro i hi
    by_cases he : i=k
    · subst i
      refine ⟨hd,hstep,?_⟩
      rw [probedSecant,hnext,ih.1,← smul_sub]
      rfl
    · exact ih.2 i (by omega)

end
end krylov.Methods
