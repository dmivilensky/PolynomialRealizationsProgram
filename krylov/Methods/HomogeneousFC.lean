import krylov.Methods.HomogeneousSolve
import krylov.Methods.DirectionReindex

/-!
Article: main_krylov, lem:U(c,d), actual FC cone homogeneity.
Use: derive homogeneity of the genuine adaptive full-memory FC trajectory
from its real observed coefficient solves and exact line searches.
Source: the proved degree-zero actual coefficient identities and exact
finite-coordinate form of the executed data-only FC policy.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every actual full-memory FC gradient, direction and step scales with its actual initial gradient.
Use: supplies genuine output homogeneity for compact-reference cone remainders, at every finite order.
Article: main_krylov, lem:U(c,d), homogeneous actual FC cycle map.
Proof: induct over the real recorded trajectory. All past steps and their
actual images scale together, so the true conjugacy coefficients stay fixed;
the exact search scalar stays fixed as well and the real observed update scales. -/
theorem fullFC_scalar (A : ℕ → E →L[ℝ] E) (g : E) (c : ℝ) (hc : c≠0) (N : ℕ) :
    fcGradient fullMemory A (c • g) N=c • fcGradient fullMemory A g N ∧
      ∀ i<N, fcDirection fullMemory A (c • g) i=c • fcDirection fullMemory A g i ∧
        fcStep fullMemory A (c • g) i=c • fcStep fullMemory A g i := by
  -- Scaling is proved on the real adaptive run, including singular totalized states and stopped tails.
  induction N with
  | zero => exact ⟨rfl,by intro i hi; omega⟩
  | succ k ih =>
    have hs : (fun i : Fin k => fcStep fullMemory A (c • g) (k-1-i.val))=
        fun i => c • fcStep fullMemory A g (k-1-i.val) := by
      funext i
      exact (ih.2 _ (by omega)).2
    have hy : (fun i : Fin k => fcSecant fullMemory A (c • g) (k-1-i.val))=
        fun i => c • fcSecant fullMemory A g (k-1-i.val) := by
      funext i
      rw [fcSecant,(ih.2 (k-1-i.val) (by omega)).2,map_smul]
      rfl
    have hd : fcDirection fullMemory A (c • g) k=c • fcDirection fullMemory A g k := by
      rw [fullFC_direction_array,hs,hy,ih.1,conjugacyDirection_scalar _ _ _ c hc,fullFC_direction_array]
    have hstep : fcStep fullMemory A (c • g) k=c • fcStep fullMemory A g k := by
      rw [fcStep,ih.1,hd,map_smul,lineLength_scalar _ _ _ c hc,smul_comm]
      rfl
    constructor
    · rw [fcGradient_succ,ih.1,fcSecant,hstep,map_smul,← smul_add,fcGradient_succ,fcSecant]
    · intro i hi
      by_cases he : i=k
      · subst i; exact ⟨hd,hstep⟩
      · exact ih.2 i (by omega)

end
end krylov.Methods
