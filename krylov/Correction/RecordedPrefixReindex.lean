import krylov.Correction.RFCLinearAngles
import krylov.Methods.FullProbedWindow
import Mathlib.Data.Fin.Rev

/-!
Article: main_krylov, thm:UCq, original observed finite-prefix dictionary.
Use: Derive true quantitative RFC search and prefix facts from the original
executed observations in their actual positive-root metric.
Source: proved actual execution identities, genuine observed conditioning
and weighted CG geometry; no final stability conclusion is assumed.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p q : ℕ}

/-- Bijectively relabeling actual observed columns preserves the true Euclidean projected-residual norm.
Use: Assemble the actual uniform ordinary-RFC induction under condition (N).
Article: main_krylov, thm:UCq.
Proof: The genuine squared coordinate norm is a finite sum preserved by the supplied equivalence.
-/
theorem projectedResidual_norm_reindex (e : Fin q ≃ Fin p) (s : Fin p → E) (g : E) :
    ‖projectedResidual (s ∘ e) g‖=‖projectedResidual s g‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.real_norm_sq_eq,projectedResidual,coordinates,Function.comp_apply]
  exact Equiv.sum_comp e (fun i => inner ℝ (s i) g ^ 2)

/-- The real nonzero, normalized-angle and projected-residual prefix property is invariant under arbitrary finite coordinate equivalences.
Use: Assemble the actual uniform ordinary-RFC induction under condition (N).
Article: main_krylov, thm:UCq.
Proof: Transport actual columns and pairings through the bijection and use the proved genuine projected-residual norm identity.
-/
theorem recordedPrefixBound_reindex (e : Fin q ≃ Fin p) (a C ε : ℝ) (s : Fin p → E) (g : E) :
    recordedPrefixBound a C ε (s ∘ e) g ↔ recordedPrefixBound a C ε s g := by
  have hu : unitWindow (s ∘ e)=unitWindow s ∘ e := rfl
  have hn : ‖projectedResidual (unitWindow (s ∘ e)) g‖=‖projectedResidual (unitWindow s) g‖ := by
    rw [hu,projectedResidual_norm_reindex]
  constructor
  · intro h
    refine ⟨fun i => ?_,fun i j hij => ?_,?_⟩
    · simpa only [Function.comp_apply,e.apply_symm_apply] using h.1 (e.symm i)
    · have ht := h.2.1 (e.symm i) (e.symm j) (fun hh => hij (e.symm.injective hh))
      simpa only [hu,Function.comp_apply,e.apply_symm_apply] using ht
    · rw [← hn]; exact h.2.2
  · intro h
    refine ⟨fun i => h.1 (e i),fun i j hij => ?_,?_⟩
    · simpa only [hu,Function.comp_apply] using h.2.1 (e i) (e j) (fun hh => hij (e.injective hh))
    · rw [hn]; exact h.2.2

/-- The original newest-first executed transcript has exactly the chronological canonical recorded-prefix property.
Use: Assemble the actual uniform ordinary-RFC induction under condition (N).
Article: main_krylov, thm:UCq.
Proof: Its true observed length and entry-age dictionary give the actual reverse-index equivalence. Apply finite prefix invariance to the same real recorded steps.
-/
theorem recordedPrefixBound_executed_chronological (s y : ℕ → E) (R : E →L[ℝ] E)
    (g : E) (k : ℕ) (a C ε : ℝ) :
    recordedPrefixBound a C ε (fun i : Fin (executedPairs s y k).length => R (windowSteps (executedPairs s y k) i)) g ↔
      recordedPrefixBound a C ε (fun i : Fin k => R (s i.val)) g := by
  let W := executedPairs s y k
  let e : Fin W.length ≃ Fin k := (finCongr (executedPairs_length s y k)).trans Fin.revPerm
  have he (i : Fin W.length) : (e i).val=k-1-i.val := by
    change (Fin.revPerm ((finCongr (executedPairs_length s y k)) i)).val=_
    simp only [Fin.revPerm_apply,Fin.rev,Fin.val_mk,finCongr_apply,Fin.val_cast]
    omega
  have hs : (fun i : Fin W.length => R (windowSteps W i))=(fun i : Fin k => R (s i.val)) ∘ e := by
    funext i
    change R (W[i.val]).1=_
    rw [executedPairs_get s y k i.val (by simpa only [W,executedPairs_length] using i.isLt)]
    simp only [Function.comp_apply,he]
  rw [hs]
  exact recordedPrefixBound_reindex e a C ε _ g

end
end krylov.Correction
