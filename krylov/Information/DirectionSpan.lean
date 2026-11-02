import krylov.Information.ObservationReplay
import krylov.Methods.ProbedStepBasis
import krylov.Methods.FinalizedInformation

/-!
Article: main_krylov, thm:centre, the actual method's direction flag.
Use: derive inclusion of every actual total step and every correction branch
in the span of the method's own directions before applying the physical reflection.
Source: the existing genuine full recorded-step span and real finite query
executor. No quadratic-reference or nonstagnation assumption is needed here.
-/

namespace krylov.Information
noncomputable section
open krylov.Methods krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual span of a method's own directions through its current iteration.
Use: this is the flag defining the source's information-preserving physical reflection.
Article: main_krylov, thm:centre, 𝒱_k=span{d₀,…,d_k}. -/
def executedDirectionSpan (m : ProbedMethod E) (A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    Submodule ℝ E := Submodule.span ℝ (probedDirection m A B g '' Set.Iic k)

/-- Actual executed direction flags increase with their chronological horizon.
Use: each older total step remains in the genuine current direction flag.
Article: main_krylov, thm:centre, increasing method flags.
Proof: include the actual old direction generators through the true index inequality. -/
theorem executedDirectionSpan_mono (m : ProbedMethod E) (A B : ℕ → E →L[ℝ] E) (g : E)
    {j k : ℕ} (hj : j≤k) : executedDirectionSpan m A B g j≤executedDirectionSpan m A B g k :=
  Submodule.span_mono (Set.image_mono (Set.Iic_subset_Iic.mpr hj))

/-- The true current chosen direction belongs to its actual executed prefix flag.
Use: the physical line search stays in the same real direction subspace.
Article: main_krylov, thm:centre, current direction membership.
Proof: it is the actual last chronological generator of that span. -/
theorem probedDirection_mem_executedDirectionSpan (m : ProbedMethod E)
    (A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    probedDirection m A B g k∈executedDirectionSpan m A B g k :=
  Submodule.subset_span ⟨k,Set.mem_Iic.mpr le_rfl,rfl⟩

/-- Every actual total evaluated step lies in the method's own direction flag.
Use: replace stored-step correction spans by the actual direction flag without assuming the desired observation replay.
Article: main_krylov, thm:centre, s_k∈𝒱_k.
Proof: strong induction puts each genuine older recorded step in the current
flag. The real full augmented correction span therefore lies in that flag;
the true executed correction movement and actual line displacement both remain there. -/
theorem probedStep_mem_executedDirectionSpan (memory : ℕ → ℕ) (m : ProbedMethod E)
    (hm : ProbedSpanRestricted memory m) (A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    probedStep m A B g k∈executedDirectionSpan m A B g k := by
  -- Every old stored total step is handled before the current correction tree is enlarged.
  induction k using Nat.strong_induction_on with
  | h k ih =>
    let K := executedDirectionSpan m A B g k
    have hd : probedDirection m A B g k∈K := probedDirection_mem_executedDirectionSpan m A B g k
    have hle : Submodule.span ℝ (Set.range (probedStepBasis m A B g k))≤K := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      refine Fin.cases hd (fun j => ?_) i
      exact executedDirectionSpan_mono m A B g (by omega : k-1-j.val≤k)
        (ih (k-1-j.val) (by omega))
    have hq := CorrectionTree.inSubspace_mono _ _ K hle
      (correction_in_fullStepSpan memory m hm A B g k)
    have hmove : (probedPhase m A B g k).movement∈K :=
      runCorrections_movement_mem K _ (B k) _ hq
    exact K.add_mem (K.smul_mem _ hd) hmove

/-- Every possible branch of the actual current correction tree stays in the method's own direction flag.
Use: every intermediate query, not only its accumulated movement, receives the preserved twin action.
Article: main_krylov, thm:centre, u_k∈𝒱_k and complete adaptive observation preservation.
Proof: all actual augmented full-step generators lie in the true current
direction flag by the preceding total-step induction; enlarge the existing
all-branch source correction-span theorem to that actual flag. -/
theorem correction_in_executedDirectionSpan (memory : ℕ → ℕ) (m : ProbedMethod E)
    (hm : ProbedSpanRestricted memory m) (A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    (m.correction (methodRun m A B g k) (probedProbe m A B g k)).InSubspace
      (executedDirectionSpan m A B g k) := by
  -- Transfer every actual correction branch after proving inclusion of its true stored generators.
  apply CorrectionTree.inSubspace_mono _ _ _ ?_ (correction_in_fullStepSpan memory m hm A B g k)
  apply Submodule.span_le.mpr
  rintro _ ⟨i,rfl⟩
  refine Fin.cases (probedDirection_mem_executedDirectionSpan m A B g k) (fun j => ?_) i
  exact executedDirectionSpan_mono m A B g (by omega : k-1-j.val≤k)
    (probedStep_mem_executedDirectionSpan memory m hm A B g (k-1-j.val))

end
end krylov.Information
