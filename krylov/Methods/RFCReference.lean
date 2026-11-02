import krylov.Methods.ExecutedProbed
import krylov.Methods.WindowCoordinates

/-!
Article: main_krylov, lem:U(d), actual quadratic RFC coordinate domains.
Use: discharge all reference finite-coordinate direction/model determinants
and line curvatures from the genuine executed CG-consistent RFC transcript.
Source: the existing actual RFC consistency and proved positive retained/augmented CG model domains.
-/

namespace krylov.Methods
noncomputable section
open Matrix krylov.Reference
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every actual static RFC total step and observed secant is precisely its true CG step and true quadratic image.
Use: no line-only substitute is inserted for an actually recorded corrected pair.
Article: main_krylov, lem:U(d), true quadratic reference coordinates.
Proof: actual consistency identifies the next full recorded-pair transcript;
its genuine newest pair is exactly the true next CG step and its true image. -/
theorem rfc_reference_pair (memory : ℕ → ℕ) (count : ℕ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E)
    (hm : ∀ k, CG.gradient Q g k≠0 → 0<k → 0<memory k) (k : ℕ) :
    probedStep (rfcMethod memory count) (fun _ => Q) (fun _ => Q) g k=referenceStep Q g k ∧
      probedSecant (rfcMethod memory count) (fun _ => Q) (fun _ => Q) g k=Q (referenceStep Q g k) := by
  have hp := (methodRun_pairs_executed (rfcMethod memory count) (fun _ => Q) (fun _ => Q) g (k+1)).symm.trans
    (rfcMethod_static memory count Q hQ hpos g hm (k+1)).2
  exact Prod.mk.inj (List.cons.inj hp).1

/-- The direction chosen by the actual static retained RFC solve is the genuine current CG direction.
Use: justify the true positive current curvature before the adaptive regularity induction.
Article: main_krylov, lem:U(d), actual reference search domain.
Proof: actual RFC consistency supplies the real gradient and pair transcript to the proved retained direction solve. -/
theorem rfc_reference_direction (memory : ℕ → ℕ) (count : ℕ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E)
    (hm : ∀ k, CG.gradient Q g k≠0 → 0<k → 0<memory k) (k : ℕ) :
    windowDirection (selectedWindow memory
      (methodRun (rfcMethod memory count) (fun _ => Q) (fun _ => Q) g k))
        (probedGradient (rfcMethod memory count) (fun _ => Q) (fun _ => Q) g k)=CG.direction Q g k := by
  have ht := rfcMethod_static memory count Q hQ hpos g hm k
  exact retainedMethod_direction memory (rfcCorrection memory count) Q hQ hpos g k _ ht.1 ht.2 (hm k)

/-- The genuine static RFC reference has nonsingular direction and augmented latest models in its fixed chronological coordinates.
Use: discharge the actual analytic solve domains from true CG positivity, including empty retained windows.
Article: main_krylov, lem:U(d), actual RFC reference inverse domains.
Proof: the actual retained and augmented reference models are proved positive
definite; actual transcript equality and the genuine finite coordinate cast
preserve their exact determinants. -/
theorem rfc_reference_coordinate_domains (memory : ℕ → ℕ) (count : ℕ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E)
    (hm : ∀ k, CG.gradient Q g k≠0 → 0<k → 0<memory k) (k : ℕ)
    (hpre : ∀ i≤k, CG.gradient Q g i≠0) :
    let s := probedStep (rfcMethod memory count) (fun _ => Q) (fun _ => Q) g
    let y := probedSecant (rfcMethod memory count) (fun _ => Q) (fun _ => Q) g
    let S := fun i : Fin (min (memory k) k) => s (k-1-i.val)
    let Y := fun i : Fin (min (memory k) k) => y (k-1-i.val)
    (crossGram Y S).det≠0 ∧
      (pairModel (Fin.cons (CG.direction Q g k) S) (Fin.cons (Q (CG.direction Q g k)) Y)).det≠0 := by
  -- Both actual inverse domains come from genuine reference positive forms before any coordinate inverse is used.
  let s := probedStep (rfcMethod memory count) (fun _ => Q) (fun _ => Q) g
  let y := probedSecant (rfcMethod memory count) (fun _ => Q) (fun _ => Q) g
  have hp : executedPairs s y k=referencePairs Q g k :=
    (methodRun_pairs_executed (rfcMethod memory count) (fun _ => Q) (fun _ => Q) g k).symm.trans
      (rfcMethod_static memory count Q hQ hpos g hm k).2
  constructor
  · have hc := crossGram_det_of_coordinates _ _ _ _
      (retainedWindow_coordinates s y k (memory k)).1 (retainedWindow_coordinates s y k (memory k)).2
    have hn := (retainedConjugacy_posDef Q hQ hpos g k (memory k) (fun i hi => hpre i hi.le)).det_pos.ne'
    rw [hp] at hc
    rwa [hc] at hn
  · have hc := windowModel_of_coordinates _ _ _ _
      (augmentedWindow_coordinates s y k (memory k) (CG.direction Q g k) (Q (CG.direction Q g k))).1
      (augmentedWindow_coordinates s y k (memory k) (CG.direction Q g k) (Q (CG.direction Q g k))).2
    have hn := (augmentedModel_posDef Q hQ hpos g k (memory k) hpre).det_pos.ne'
    have hdet := congrArg Matrix.det hc
    rw [Matrix.det_submatrix_equiv_self] at hdet
    rw [hp] at hdet
    rwa [hdet] at hn

/-- Genuine actual RFC reference arrays have nonzero augmented columns, true quadratic images and zero post-search projection.
Use: discharge every actual reference premise of the normalized repeated-residual order theorem.
Article: main_krylov, lem:projected-residual, nondegenerate quadratic prefix.
Proof: actual RFC pairs are true CG pairs; positive true CG line lengths and
curvatures give nonzero columns. The genuine next CG invariant annihilates the
current direction and every retained old step in the actual augmented family. -/
theorem rfc_reference_augmented_data (memory : ℕ → ℕ) (count : ℕ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E)
    (hm : ∀ k, CG.gradient Q g k≠0 → 0<k → 0<memory k) (k : ℕ)
    (hpre : ∀ i≤k, CG.gradient Q g i≠0) :
    let S := fun i : Fin (min (memory k) k) =>
      probedStep (rfcMethod memory count) (fun _ => Q) (fun _ => Q) g (k-1-i.val)
    let Y := fun i : Fin (min (memory k) k) =>
      probedSecant (rfcMethod memory count) (fun _ => Q) (fun _ => Q) g (k-1-i.val)
    let U : Fin (min (memory k) k+1) → E := Fin.cons (CG.direction Q g k) S
    let Z : Fin (min (memory k) k+1) → E := Fin.cons (Q (CG.direction Q g k)) Y
    (∀ i, U i≠0) ∧ Z=(fun i => Q (U i)) ∧ coordinates U (CG.gradient Q g (k+1))=0 := by
  -- Every old finite age is a genuine preterminal CG time; its actual recorded step has positive length.
  have hk := CG.invariant Q hQ hpos g (k+1) (fun i hi => hpre i (by omega))
  have hstep (i : Fin (min (memory k) k)) : referenceStep Q g (k-1-i.val)≠0 := by
    have hi := i.isLt
    have hj : k-1-i.val<k := by omega
    obtain ⟨hd,hl,_⟩ := CG.invariant_line_pos Q hpos g (k-1-i.val)
      (CG.invariant Q hQ hpos g (k-1-i.val) (fun j hj' => hpre j (by omega))) (hpre _ (by omega))
    exact smul_ne_zero hl.ne' hd
  refine ⟨?_,?_,?_⟩
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (CG.invariant_line_pos Q hpos g k
        (CG.invariant Q hQ hpos g k (fun j hj => hpre j hj.le)) (hpre k le_rfl)).1
    · change probedStep (rfcMethod memory count) (fun _ => Q) (fun _ => Q) g (k-1-j.val)≠0
      rw [(rfc_reference_pair memory count Q hQ hpos g hm _).1]
      exact hstep j
  · funext i
    refine Fin.cases rfl (fun j => ?_) i
    change probedSecant (rfcMethod memory count) (fun _ => Q) (fun _ => Q) g (k-1-j.val)=
      Q (probedStep (rfcMethod memory count) (fun _ => Q) (fun _ => Q) g (k-1-j.val))
    rw [(rfc_reference_pair memory count Q hQ hpos g hm _).1,
      (rfc_reference_pair memory count Q hQ hpos g hm _).2]
  · ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hk.old_direction k (by omega)
    · change inner ℝ (probedStep (rfcMethod memory count) (fun _ => Q) (fun _ => Q) g (k-1-j.val))
        (CG.gradient Q g (k+1))=0
      rw [(rfc_reference_pair memory count Q hQ hpos g hm _).1,referenceStep,real_inner_smul_left,
        hk.old_direction _ (by omega),mul_zero]

end
end krylov.Methods
