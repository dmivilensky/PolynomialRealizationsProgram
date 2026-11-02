import krylov.Methods.SmoothProbedFields
import krylov.Methods.ReferenceModels
import krylov.Methods.StaticTermination
import krylov.Envelope.KrylovFlags

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:filtration, genuine moving full-step correction basis.
Use: enlarge the real retained correction span to the actual current raw
direction and all genuine earlier recorded steps, with a fixed true finite
dimension and independently proved nonsingular reference Grams.
Source: real chronological observed-pair indexing, actual global quadratic
CG consistency and genuine nonstagnating CG conjugacy and positivity.
-/

namespace krylov.Methods
noncomputable section
open Matrix krylov.Reference krylov.Envelope
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The genuine fixed finite family of the actual current raw direction and all real earlier recorded steps in newest-first order.
Use: The genuine fixed finite family of the actual current raw direction and all real earlier recorded steps in newest-first order.
Article: main_krylov, apB:lem:filtration, genuine moving full-step correction basis.
Proof: Read only the actual chosen direction and true executed step transcript. -/
def probedStepBasis (m : ProbedMethod E) (A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) : Fin (k+1) → E :=
  Fin.cons (probedDirection m A B g k) (fun i : Fin k => probedStep m A B g (k-1-i.val))

/-- Every actual source-admissible raw correction tree lies in the true full executed-step span, for every retained memory rule.
Use: Every actual source-admissible raw correction tree lies in the true full executed-step span, for every retained memory rule.
Article: main_krylov, apB:lem:filtration, genuine moving full-step correction basis.
Proof: Locate each real retained step in the genuine chronological transcript and enlarge its true span; finite correction-tree induction transfers every actual branch. -/
theorem correction_in_fullStepSpan (memory : ℕ → ℕ) (m : ProbedMethod E)
    (hm : ProbedSpanRestricted memory m) (A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    (m.correction (methodRun m A B g k) (probedProbe m A B g k)).InSubspace
      (Submodule.span ℝ (Set.range (probedStepBasis m A B g k))) := by
  -- Enlarge precisely the genuine retained observed span, without assuming any stored-window basis condition.
  have hs := (hm (methodRun m A B g k)).2 (probedProbe m A B g k)
  have hle : Submodule.span ℝ (Set.range (windowSteps
      ((probedDirection m A B g k,probedProbe m A B g k)::selectedWindow memory (methodRun m A B g k))))≤
      Submodule.span ℝ (Set.range (probedStepBasis m A B g k)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Submodule.subset_span ⟨0,rfl⟩
    · have hp := List.get_mem (selectedWindow memory (methodRun m A B g k)) j
      let p := (selectedWindow memory (methodRun m A B g k)).get j
      change p∈selectedWindow memory (methodRun m A B g k) at hp
      rw [selectedWindow_methodRun] at hp
      have hp' := List.mem_of_mem_take hp
      obtain ⟨a,ha,he⟩ := List.mem_iff_getElem.mp hp'
      have ha' : a<k := by simpa only [executedPairs_length] using ha
      rw [executedPairs_get _ _ k a ha'] at he
      have hv : windowSteps ((probedDirection m A B g k,probedProbe m A B g k)::
          selectedWindow memory (methodRun m A B g k)) j.succ=
          probedStep m A B g (k-1-a) := by
        exact congrArg Prod.fst he.symm
      rw [hv]
      exact Submodule.subset_span ⟨Fin.succ ⟨a,ha'⟩,rfl⟩
  have hmono : ∀ q : CorrectionTree E, q.InSubspace (Submodule.span ℝ (Set.range (windowSteps ((probedDirection m A B g k,probedProbe m A B g k)::selectedWindow memory (methodRun m A B g k))))) → q.InSubspace (Submodule.span ℝ (Set.range (probedStepBasis m A B g k))) := by
    intro q
    induction q with
    | done => exact fun _ => trivial
    | query u next ih => exact fun h => ⟨hle h.1,fun v => ih v (h.2 v)⟩
  exact hmono _ hs

/-- The genuine augmented full-step basis of every globally CG-consistent raw method is independent on each true nonstagnating quadratic prefix.
Use: The genuine augmented full-step basis of every globally CG-consistent raw method is independent on each true nonstagnating quadratic prefix.
Article: main_krylov, apB:lem:filtration, genuine moving full-step correction basis.
Proof: Identify actual old steps with genuine CG steps. Their true independence and real conjugacy separate the positively scaled actual current CG direction from their genuine span. -/
theorem probedStepBasis_independent (m : ProbedMethod E) (hm : CGConsistent m)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ)
    (hg : ∀ i≤k, CG.gradient Q g i≠0) :
    LinearIndependent ℝ (probedStepBasis m (fun _ => Q) (fun _ => Q) g k) := by
  -- Real quadratic consistency identifies both the true old physical steps and the actual positive current direction scale.
  obtain ⟨c,hc,hd,_⟩ := hm Q hQ hpos g k
  have hs : (fun i : Fin k => probedStep m (fun _ => Q) (fun _ => Q) g (k-1-i.val))=
      fun i : Fin k => referenceStep Q g (k-1-i.val) := by
    funext i
    exact quadratic_probedStep_eq_cg m hm Q hQ hpos g _
  change LinearIndependent ℝ (Fin.cons (m.direction _) _)
  rw [hd,hs]
  have htail : LinearIndependent ℝ (fun i : Fin k => referenceStep Q g (k-1-i.val)) := by
    apply reference_window_independent Q hQ hpos g k (fun i hi => hg i hi.le)
    · intro i j he
      change k-1-i.val=k-1-j.val at he
      apply Fin.ext
      have := i.isLt
      have := j.isLt
      omega
    · intro i;have := i.isLt;omega
  apply htail.finCons
  intro hcspan
  have hinv := CG.invariant Q hQ hpos g k (fun i hi => hg i hi.le)
  have hdn := (CG.invariant_line_pos Q hpos g k hinv (hg k le_rfl)).1
  have hle : Submodule.span ℝ (Set.range fun i : Fin k => referenceStep Q g (k-1-i.val))≤
      (innerSL ℝ (Q (CG.direction Q g k))).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change inner ℝ (Q (CG.direction Q g k)) (referenceStep Q g (k-1-i.val))=0
    rw [real_inner_comm,referenceStep,real_inner_smul_left,
      hinv.conjugate _ k (by have := i.isLt;omega) le_rfl,mul_zero]
  have he := hle hcspan
  change inner ℝ (Q (CG.direction Q g k)) (c • CG.direction Q g k)=0 at he
  rw [real_inner_smul_right,real_inner_comm] at he
  exact (mul_pos hc (hpos _ hdn)).ne' he

/-- Both the true Euclidean and genuine reference-image Grams of the actual augmented full-step basis are nonsingular before exhaustion.
Use: Both the true Euclidean and genuine reference-image Grams of the actual augmented full-step basis are nonsingular before exhaustion.
Article: main_krylov, apB:lem:filtration, genuine moving full-step correction basis.
Proof: Apply proved positive operator Gram definiteness to the actual independent family and its true injective positive-operator image. -/
theorem probedStepBasis_gram (m : ProbedMethod E) (hm : CGConsistent m)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ)
    (hg : ∀ i≤k, CG.gradient Q g i≠0) :
    let s := probedStepBasis m (fun _ => Q) (fun _ => Q) g k
    (crossGram s s).det≠0 ∧ (crossGram (fun i => Q (s i)) (fun i => Q (s i))).det≠0 := by
  -- Genuine independence also survives the true injective reference operator, so both real Grams are positive.
  let s := probedStepBasis m (fun _ => Q) (fun _ => Q) g k
  have hs := probedStepBasis_independent m hm Q hQ hpos g k hg
  have hId : (ContinuousLinearMap.id ℝ E).toLinearMap.IsSymmetric := fun _ _ => rfl
  have hpId : ∀ v : E, v≠0 → 0 < inner ℝ v ((ContinuousLinearMap.id ℝ E) v) := by
    intro v hv
    exact real_inner_self_pos.mpr hv
  constructor
  · exact (operatorGram_posDef (ContinuousLinearMap.id ℝ E) hId hpId hs).det_pos.ne'
  · have hQs := hs.map' Q.toLinearMap (LinearMap.ker_eq_bot.mpr (positive_operator_injective Q hpos))
    exact (operatorGram_posDef (ContinuousLinearMap.id ℝ E) hId hpId hQs).det_pos.ne'

/-- The actual fixed-dimensional augmented raw step family is C-two under genuine primitive smooth method hypotheses.
Use: The actual fixed-dimensional augmented raw step family is C-two under genuine primitive smooth method hypotheses.
Article: main_krylov, apB:lem:filtration, genuine moving full-step correction basis.
Proof: Read the genuine current direction and each real earlier step from their proved actual full-history coordinate charts. -/
theorem smoothProbed_stepBasis_regular (m : ProbedMethod E) (hm : CGConsistent m)
    (A B : ℝ → ℕ → E →L[ℝ] E) (g : ℝ → E) (N : ℕ)
    (hA : ∀ i<N, ContDiffAt ℝ 2 (fun t => A t i) 0)
    (hB : ∀ i<N, ContDiffAt ℝ 2 (fun t => B t i) 0) (hg : ContDiffAt ℝ 2 g 0)
    (Q : E →L[ℝ] E) (hA0 : A 0=fun _ => Q) (hB0 : B 0=fun _ => Q)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (hpre : ∀ i<N, CG.gradient Q (g 0) i≠0) (hsmooth : SmoothProbedCycleAt m 2 Q (g 0) N)
    (k : ℕ) (hk : k<N) :
    ContDiffAt ℝ 2 (fun t => probedStepBasis m (A t) (B t) (g t) k) 0 := by
  have hf i hi := smoothProbed_fields_regular m hm A B g 0 N hA hB hg Q hA0 hB0 hQ hpos hpre hsmooth i hi
  apply contDiffAt_pi.mpr
  refine Fin.cases (hf k hk).1 (fun i => ?_)
  exact (hf (k-1-i.val) (by have := i.isLt;omega)).2.2.1

/-- The actual augmented full-step reference family belongs to the genuine next polynomial Krylov flag.
Use: The actual augmented full-step reference family belongs to the genuine next polynomial Krylov flag.
Article: main_krylov, apB:lem:filtration, genuine moving full-step correction basis.
Proof: Identify the true current CG direction and every genuine old CG step, then use the proved actual polynomial flag inclusion. -/
theorem quadratic_stepBasis_mem (m : ProbedMethod E) (hm : CGConsistent m)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ)
    (hg : ∀ i≤k, CG.gradient Q g i≠0) :
    Submodule.span ℝ (Set.range (probedStepBasis m (fun _ => Q) (fun _ => Q) g k))≤CG.krylovSpace Q g (k+1) := by
  -- Derive the genuine nonzero line domains before invoking the actual polynomial Krylov flag theorem.
  have hline (i : ℕ) (hi : i≤k) : CG.length Q g i≠0 :=
    (CG.invariant_line_pos Q hpos g i (CG.invariant Q hQ hpos g i (fun j hj => hg j (by omega))) (hg i hi)).2.1.ne'
  apply Submodule.span_le.mpr
  rintro _ ⟨i,rfl⟩
  refine Fin.cases ?_ (fun j => ?_) i
  · obtain ⟨c,_,hd,_⟩ := hm Q hQ hpos g k
    change m.direction _∈CG.krylovSpace Q g (k+1)
    rw [hd]
    exact Submodule.smul_mem _ _ (cgDirection_mem_krylov Q g k (fun j hj => hline j (by omega)))
  · change probedStep m (fun _ => Q) (fun _ => Q) g (k-1-j.val)∈_
    rw [quadratic_probedStep_eq_cg m hm Q hQ hpos,referenceStep]
    apply Submodule.smul_mem
    have hd := cgDirection_mem_krylov Q g (k-1-j.val) (fun i hi => hline i (by have := j.isLt;omega))
    exact (krylovSpace_mono Q g (show k-1-j.val+1≤k+1 by omega)) hd
end
end krylov.Methods
