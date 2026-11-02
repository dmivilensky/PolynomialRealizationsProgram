import krylov.Methods.ProbedModelBasis
import krylov.Correction.ChronologicalModel
import krylov.Correction.ObservedAugmentedGram
import krylov.Methods.CanonicalWindows

/-!
Article: main_krylov, thm:UCq, actual chronological full-model columns.
Use: Identify each old recorded column and the final raw direction of the
true normalized model, retaining a basis when its last line displacement is zero.
Source: mathlib's Fin.cons_comp_rev and actual recorded observation indexing;
the existing observed-conjugacy angle and genuine unit-Gram inequalities.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Stability
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {k n : ℕ}

/-- Reversing the genuine newest-first full step family gives the actual chronological recorded steps followed by the current raw direction.
Use: Match the original executor's true columns to terminal quantitative coordinates.
Article: main_krylov, thm:UCq.
Proof: Reuse Fin.cons_comp_rev; reversing the actual retained age cancels its chronological index subtraction.
-/
theorem probedStepBasis_reverse (m : ProbedMethod E) (A B : ℕ → E →L[ℝ] E)
    (g : E) (k : ℕ) :
    (probedStepBasis m A B g k) ∘ Fin.revPerm=
      Fin.snoc (fun i : Fin k => probedStep m A B g i.val) (probedDirection m A B g k) := by
  change (Fin.cons (probedDirection m A B g k)
    (fun i : Fin k => probedStep m A B g (k-1-i.val))) ∘ Fin.rev=_
  rw [Fin.cons_comp_rev]
  congr 1
  funext i
  change probedStep m A B g (k-1-(Fin.rev i).val)=probedStep m A B g i.val
  congr 1
  simp only [Fin.rev,Fin.val_mk]
  omega

/-- Reversing the genuine newest-first image family gives actual chronological measured secants followed by the true current probe.
Use: Keep real correction-contaminated observations in terminal source coordinates.
Article: main_krylov, thm:UCq.
Proof: The same true age-reversal identity selects each actual measured secant and leaves the current probe last.
-/
theorem probedImageBasis_reverse (m : ProbedMethod E) (A B : ℕ → E →L[ℝ] E)
    (g : E) (k : ℕ) :
    (probedImageBasis m A B g k) ∘ Fin.revPerm=
      Fin.snoc (fun i : Fin k => probedSecant m A B g i.val) (probedProbe m A B g k) := by
  change (Fin.cons (probedProbe m A B g k)
    (fun i : Fin k => probedSecant m A B g (k-1-i.val))) ∘ Fin.rev=_
  rw [Fin.cons_comp_rev]
  congr 1
  funext i
  change probedSecant m A B g (k-1-(Fin.rev i).val)=probedSecant m A B g i.val
  congr 1
  simp only [Fin.rev,Fin.val_mk]
  omega

/-- Genuine individual column normalization commutes with adjoining the actual final raw direction.
Use: Retain the real last direction even when its searched displacement vanishes.
Article: main_krylov, thm:UCq.
Proof: Each old coordinate and the true final coordinate use their own original norm.
-/
theorem unitWindow_snoc (s : Fin k → E) (d : E) :
    unitWindow (Fin.snoc s d)=Fin.snoc (unitWindow s) (NormedSpace.normalize d) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [unitWindow,rescaleWindow,Fin.snoc_last,NormedSpace.normalize]
  · simp only [unitWindow,rescaleWindow,Fin.snoc_castSucc]

/-- The true primal metric map commutes with the original chronological final-column extension.
Use: Identify real canonical recorded columns before normalization.
Article: main_krylov, thm:UCq.
Proof: Evaluate the actual last and old coordinates separately.
-/
theorem primalWindow_snoc (base : Matrix (Fin n) (Fin n) ℝ)
    (s : Fin k → EuclideanSpace ℝ (Fin n)) (d : EuclideanSpace ℝ (Fin n)) :
    primalWindow base (Fin.snoc s d)=Fin.snoc (primalWindow base s) (cgOperator (metricRoot base) d) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [primalWindow,Fin.snoc_last,cgOperator]
  · simp only [primalWindow,Fin.snoc_castSucc]

/-- The true dual metric map commutes with the original chronological image-column extension.
Use: Preserve actual measured secants and the genuine current probe.
Article: main_krylov, thm:UCq.
Proof: Evaluate each actual chronological coordinate under the same inverse-root map.
-/
theorem dualWindow_snoc (base : Matrix (Fin n) (Fin n) ℝ)
    (s : Fin k → EuclideanSpace ℝ (Fin n)) (d : EuclideanSpace ℝ (Fin n)) :
    dualWindow base (Fin.snoc s d)=Fin.snoc (dualWindow base s) (cgOperator (metricRoot base)⁻¹ d) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [dualWindow,Fin.snoc_last,cgOperator]
  · simp only [dualWindow,Fin.snoc_castSucc]

/-- The genuine chronological canonical model columns are exactly the individually normalized actual recorded steps and actual last raw direction.
Use: Apply the quantitative old-step and terminal-coordinate bounds to the real executor.
Article: main_krylov, thm:UCq.
Proof: Compose the proved true age reversal, primal coordinate and final-column normalization identities.
-/
theorem normalized_chronological_steps (base : Matrix (Fin n) (Fin n) ℝ)
    (m : ProbedMethod (EuclideanSpace ℝ (Fin n)))
    (A B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    unitWindow (primalWindow base ((probedStepBasis m A B g k) ∘ Fin.revPerm))=
      Fin.snoc (unitWindow (primalWindow base (fun i : Fin k => probedStep m A B g i.val)))
        (NormedSpace.normalize (cgOperator (metricRoot base) (probedDirection m A B g k))) := by
  rw [probedStepBasis_reverse,primalWindow_snoc,unitWindow_snoc]

/-- The genuine chronological normalized images use each real measured secant divided by its own actual step norm and the true final probe divided by its raw direction norm.
Use: Derive the terminal measured-model contamination allowance from actual observed pairs.
Article: main_krylov, thm:UCq.
Proof: Reverse the real current-plus-age image family and its own step family together; the true primal and dual maps retain these exact individual normalizers.
-/
theorem normalized_chronological_images (base : Matrix (Fin n) (Fin n) ℝ)
    (m : ProbedMethod (EuclideanSpace ℝ (Fin n)))
    (A B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    rescaleWindow (dualWindow base ((probedImageBasis m A B g k) ∘ Fin.revPerm))
      (fun i => ‖primalWindow base ((probedStepBasis m A B g k) ∘ Fin.revPerm) i‖⁻¹)=
      Fin.snoc
        (fun i : Fin k => ‖cgOperator (metricRoot base) (probedStep m A B g i.val)‖⁻¹ •
          cgOperator (metricRoot base)⁻¹ (probedSecant m A B g i.val))
        (‖cgOperator (metricRoot base) (probedDirection m A B g k)‖⁻¹ •
          cgOperator (metricRoot base)⁻¹ (probedProbe m A B g k)) := by
  rw [probedImageBasis_reverse,probedStepBasis_reverse,primalWindow_snoc,dualWindow_snoc]
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [rescaleWindow,Fin.snoc_last]
  · simp only [rescaleWindow,Fin.snoc_castSucc,primalWindow,dualWindow,cgOperator]

/-- True old recorded angles and actual image conjugacy bound every genuine chronological augmented unit-column angle by their sum.
Use: Derive the real last full-basis Gram without comparing its raw final direction to CG.
Article: main_krylov, thm:UCq.
Proof: The existing observed-conjugacy inequality bounds each new angle by the real relative secant error; actual old angles keep their supplied bound. Separate the genuine last and old coordinate pairs.
-/
theorem unit_snoc_observed_angles (s y : Fin k → E) (d : E)
    (hs : ∀ i, s i≠0) (hd : d≠0) {a η : ℝ} (ha : 0≤a) (hη : 0≤η)
    (hy : ∀ i, ‖y i-s i‖≤η*‖s i‖) (ho : ∀ i, inner ℝ (y i) d=0)
    (hangle : ∀ i j, i≠j → |inner ℝ (unitWindow s i) (unitWindow s j)|≤a) :
    ∀ i j : Fin (k+1), i≠j →
      |inner ℝ (unitWindow (Fin.snoc s d) i) (unitWindow (Fin.snoc s d) j)|≤a+η := by
  have hnew (j : Fin k) : |inner ℝ (unitWindow s j) (NormedSpace.normalize d)|≤η := by
    have horth : inner ℝ (rescaleWindow y (fun i => ‖s i‖⁻¹) j) (NormedSpace.normalize d)=0 := by
      simp only [rescaleWindow,NormedSpace.normalize,real_inner_smul_left,real_inner_smul_right,ho,mul_zero]
    have h := approximate_conjugacy_bound (unitWindow s j)
      (rescaleWindow y (fun i => ‖s i‖⁻¹) j) (NormedSpace.normalize d)
      (ContinuousLinearMap.id ℝ E) (unitWindow_norm s hs j) (ε := 0) (by simp)
      (unitWindow_pair_error s y hs hy j) horth
    simpa only [ContinuousLinearMap.id_apply,zero_add,NormedSpace.norm_normalize hd,mul_one] using h
  intro i j
  rw [unitWindow_snoc]
  revert j
  refine Fin.lastCases ?_ (fun i => ?_) i
  · intro j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · intro hij; exact (hij rfl).elim
    · intro _hij
      simp only [Fin.snoc_last,Fin.snoc_castSucc]
      rw [real_inner_comm]
      exact (hnew j).trans (by linarith)
  · intro j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · intro _hij
      simp only [Fin.snoc_last,Fin.snoc_castSucc]
      exact (hnew i).trans (by linarith)
    · intro hij
      simp only [Fin.snoc_castSucc]
      exact (hangle i j (fun h => hij (congrArg Fin.castSucc h))).trans (by linarith)

/-- The actual chronological augmented unit-column Gram has the uniform dimension-times-angle-plus-pair-error bound.
Use: Derive the genuine final basis inverse domain from real observed search geometry.
Article: main_krylov, thm:UCq.
Proof: Every true old column and the actual last direction are nonzero. Apply the existing spectral unit-Gram inequality to the proved real augmented angle bounds.
-/
theorem unit_snoc_observed_gram (s y : Fin k → E) (d : E)
    (hs : ∀ i, s i≠0) (hd : d≠0) {a η : ℝ} (ha : 0≤a) (hη : 0≤η)
    (hy : ∀ i, ‖y i-s i‖≤η*‖s i‖) (ho : ∀ i, inner ℝ (y i) d=0)
    (hangle : ∀ i j, i≠j → |inner ℝ (unitWindow s i) (unitWindow s j)|≤a) :
    ‖crossGram (unitWindow (Fin.snoc s d)) (unitWindow (Fin.snoc s d))-1‖≤
      ((k+1 : ℕ) : ℝ)*(a+η) := by
  have hu (i : Fin (k+1)) : (Fin.snoc s d : Fin (k+1) → E) i≠0 := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using hd
    · simpa only [Fin.snoc_castSucc] using hs j
  exact unitGram_deviation _ (unitWindow_norm _ hu) (add_nonneg ha hη)
    (unit_snoc_observed_angles s y d hs hd ha hη hy ho hangle)

/-- Actual relative old secant contamination bounds every genuine normalized chronological image discrepancy from its own true probe-time canonical operator, with exact zero current-probe discrepancy.
Use: Derive the terminal measured-model factor estimate from real executed observations.
Article: main_krylov, thm:UCq.
Proof: True chronological dictionaries identify each actual old pair and the last raw direction/probe. The current image is its genuine queried operator image. Every old discrepancy keeps its own relative norm allowance. Apply the existing exact individual-column normalization estimate to these true nonzero columns.
-/
theorem normalized_chronological_contamination (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (m : ProbedMethod (EuclideanSpace ℝ (Fin n)))
    (A B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) {η : ℝ} (hη : 0≤η)
    (hs : ∀ i<k, cgOperator (metricRoot base) (probedStep m A B g i)≠0)
    (hd : cgOperator (metricRoot base) (probedDirection m A B g k)≠0)
    (hxi : ∀ i<k, ‖cgOperator (metricRoot base)⁻¹ (probedSecant m A B g i)-
      canonicalOperator base (A i) (cgOperator (metricRoot base) (probedStep m A B g i))‖≤
        η*‖cgOperator (metricRoot base) (probedStep m A B g i)‖) :
    let S := primalWindow base ((probedStepBasis m A B g k) ∘ Fin.revPerm)
    let Y := dualWindow base ((probedImageBasis m A B g k) ∘ Fin.revPerm)
    ∀ i, ‖rescaleWindow Y (fun j => ‖S j‖⁻¹) i-canonicalOperator base (A i.val) (unitWindow S i)‖≤η := by
  let S := primalWindow base ((probedStepBasis m A B g k) ∘ Fin.revPerm)
  let Y := dualWindow base ((probedImageBasis m A B g k) ∘ Fin.revPerm)
  have hS : S=Fin.snoc
      (fun i : Fin k => cgOperator (metricRoot base) (probedStep m A B g i.val))
      (cgOperator (metricRoot base) (probedDirection m A B g k)) := by
    dsimp only [S]
    rw [probedStepBasis_reverse,primalWindow_snoc]
    rfl
  have hY : Y=Fin.snoc
      (fun i : Fin k => cgOperator (metricRoot base)⁻¹ (probedSecant m A B g i.val))
      (cgOperator (metricRoot base)⁻¹ (probedProbe m A B g k)) := by
    dsimp only [Y]
    rw [probedImageBasis_reverse,dualWindow_snoc]
    rfl
  have hS0 (i : Fin (k+1)) : S i≠0 := by
    rw [hS]
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using hd
    · simpa only [Fin.snoc_castSucc] using hs j.val j.isLt
  have hraw (i : Fin (k+1)) : ‖Y i-canonicalOperator base (A i.val) (S i)‖≤η*‖S i‖ := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [hS,hY,Fin.snoc_last,Fin.val_last]
      have he : cgOperator (metricRoot base)⁻¹ (probedProbe m A B g k)=
          canonicalOperator base (A k) (cgOperator (metricRoot base) (probedDirection m A B g k)) :=
        (canonicalOperator_primal base hb (A k) (probedDirection m A B g k)).symm
      rw [he,sub_self,norm_zero]
      exact mul_nonneg hη (norm_nonneg _)
    · simpa only [hS,hY,Fin.snoc_castSucc,Fin.val_castSucc] using hxi j.val j.isLt
  dsimp only
  intro i
  exact unitWindow_image_error S Y (fun i => canonicalOperator base (A i.val)) hS0 hraw i

end
end krylov.Correction
