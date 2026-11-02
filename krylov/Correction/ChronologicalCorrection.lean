import krylov.Correction.ChronologicalModel
import krylov.Methods.CanonicalWindows
import krylov.Correction.ActualSolve

/-!
Article: main_krylov, thm:UCq, actual chronological terminal query.
Use: Connect the original real ordinary-RFC output to the normalized
chronological measured model used in the quantitative cubic calculation.
Source: the existing true finite model reindexing, positive-root covariance,
column normalization and the original observed-gate correction executor.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Stability
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p n : ℕ}

/-- Genuine chronological latest-information models transform by the true diagonal column congruence.
Use: Normalize the actual chronological measured model without changing its physical query.
Article: main_krylov, thm:UCq.
Proof: In each real triangular entry the two column scales are exactly its two matrix-axis scales; commute those real factors.
-/
theorem latest_crossGram_rescale (s y : Fin p → E) (d : Fin p → ℝ) :
    latest (crossGram (rescaleWindow s d) (rescaleWindow y d))=
      rescaleModel (latest (crossGram s y)) d := by
  ext i j
  simp only [latest,crossGram,rescaleWindow,real_inner_smul_left,real_inner_smul_right,
    rescaleModel,Matrix.diagonal_mul,Matrix.mul_diagonal]
  rcases le_total i j with hij|hji
  · simp only [min_eq_left hij,max_eq_right hij]; ring
  · simp only [min_eq_right hji,max_eq_left hji]; ring

/-- The actual chronological latest-model correction is precisely the same physical solve in original newest-first coordinates.
Use: Identify the real executor's observed model with the chronological flag algebra.
Article: main_krylov, thm:UCq.
Proof: Reuse genuine model-correction invariance under the reversal equivalence and the exact chronological latest/pair-model identity; the reversal involution cancels.
-/
theorem chronological_modelCorrection (s y : Fin p → E) (g : E) :
    combine s (modelCoefficients s (latest (crossGram s y)) g)=
      combine (s ∘ Fin.revPerm)
        (modelCoefficients (s ∘ Fin.revPerm) (pairModel (s ∘ Fin.revPerm) (y ∘ Fin.revPerm)) g) := by
  have hs : (s ∘ Fin.revPerm) ∘ Fin.revPerm=s := by
    funext i; simp only [Function.comp_apply,Fin.revPerm_apply,Fin.rev_rev]
  have ht := modelCorrection_reindex Fin.revPerm (s ∘ Fin.revPerm)
    (pairModel (s ∘ Fin.revPerm) (y ∘ Fin.revPerm)) g
  rw [hs,latest_crossGram_reverse_pairModel] at ht
  exact ht

/-- True individual column normalization preserves the genuine chronological observed-model physical correction.
Use: Apply the uniform cubic calculation to the original measured query.
Article: main_krylov, thm:UCq.
Proof: The actual nonzero column norms give the genuine diagonal inverse domain. Exact model congruence and the existing column-rescaling correction identity preserve the real solve, which then reindexes to newest-first storage.
-/
theorem normalized_chronological_modelCorrection
    (s y : Fin p → E) (hs : ∀ i, s i≠0) (g : E) :
    combine (unitWindow s)
      (modelCoefficients (unitWindow s)
        (latest (crossGram (unitWindow s) (rescaleWindow y (fun i => ‖s i‖⁻¹)))) g)=
      combine (s ∘ Fin.revPerm)
        (modelCoefficients (s ∘ Fin.revPerm) (pairModel (s ∘ Fin.revPerm) (y ∘ Fin.revPerm)) g) := by
  simp only [unitWindow]
  rw [latest_crossGram_rescale,
    modelCorrection_rescale s (latest (crossGram s y)) _ (unitWindow_diagonal_unit s hs),
    chronological_modelCorrection]

/-- Actual primal/dual metric coordinates preserve the genuine chronological latest-information model exactly.
Use: Keep the original measured observations in the canonical cubic response.
Article: main_krylov, thm:UCq.
Proof: Each selected triangular entry is the existing exact primal/dual search pairing.
-/
theorem canonical_latest_crossGram (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (s y : Fin p → EuclideanSpace ℝ (Fin n)) :
    latest (crossGram (primalWindow base s) (dualWindow base y))=latest (crossGram s y) := by
  ext i j
  exact (canonical_search_pairing base hb (s (min i j)) (y (max i j))).symm

/-- The true normalized chronological canonical model query is exactly the metric-root image of the original newest-first physical query.
Use: Tie the quantitative terminal model formula to the actual original measured correction.
Article: main_krylov, thm:UCq.
Proof: Genuine column rescaling and chronological reindexing preserve the physical solve. Actual primal/dual pair-model covariance and the existing canonical model-correction identity then give its real metric-root image.
-/
theorem canonical_chronological_modelCorrection (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (s y : Fin p → EuclideanSpace ℝ (Fin n))
    (hs : ∀ i, primalWindow base s i≠0) (g : EuclideanSpace ℝ (Fin n)) :
    let S := primalWindow base s
    let Y := dualWindow base y
    let t := unitWindow S
    let z := rescaleWindow Y (fun i => ‖S i‖⁻¹)
    combine t (modelCoefficients t (latest (crossGram t z)) (cgOperator (metricRoot base)⁻¹ g))=
      cgOperator (metricRoot base) (combine (s ∘ Fin.revPerm)
        (modelCoefficients (s ∘ Fin.revPerm) (pairModel (s ∘ Fin.revPerm) (y ∘ Fin.revPerm)) g)) := by
  dsimp only
  rw [normalized_chronological_modelCorrection _ _ hs]
  change combine (primalWindow base (s ∘ Fin.revPerm))
    (modelCoefficients (primalWindow base (s ∘ Fin.revPerm))
      (pairModel (primalWindow base (s ∘ Fin.revPerm)) (dualWindow base (y ∘ Fin.revPerm)))
      (cgOperator (metricRoot base)⁻¹ g))=_
  rw [canonical_pairModel base hb]
  exact canonical_modelCorrection base hb (s ∘ Fin.revPerm) (pairModel (s ∘ Fin.revPerm) (y ∘ Fin.revPerm)) g

/-- An actually accepted noninitial ordinary-RFC phase returns its genuine searched gradient plus the true single measured-model query action.
Use: Identify the real original terminal gradient before any geometric estimate.
Article: main_krylov, thm:UCq.
Proof: The exact actual RFC array dictionary selects its genuine accepted defect branch. Executing the existing one-query model tree gives exactly the stated real gradient.
-/
theorem ordinary_phase_gradient_model (A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) (hk : 0<k)
    (hgate : ‖pairDefect
      (fun i : Fin k => probedStep (rfcMethod fullMemory 1) A B g (k-1-i.val))
      (fun i : Fin k => probedSecant (rfcMethod fullMemory 1) A B g (k-1-i.val))‖<1) :
    let m := rfcMethod fullMemory 1 (E := E)
    let U := probedStepBasis m A B g k
    let Y := probedImageBasis m A B g k
    let v := fullPostSearch 1 A B g k
    probedGradient m A B g (k+1)=v+B k (combine U (modelCoefficients U (pairModel U Y) v)) := by
  dsimp only
  rw [probedGradient_succ,probedRFC_phase_array]
  rw [show min (fullMemory k) k=k from min_self k,rfcArrayPhase,ite_eq_left ⟨hk,hgate⟩]
  rfl

/-- The actual accepted ordinary-RFC output is exactly its true normalized chronological canonical model correction applied to the actual searched gradient.
Use: Apply the quantitative cubic model theorem to the real executed last query, preserving zero last searched displacements.
Article: main_krylov, thm:UCq.
Proof: The genuine normalized chronological query equals the metric-root image of the actual original query. Exact positive-root operator covariance transforms its true returned gradient; the actual accepted-phase execution identity supplies that original gradient.
-/
theorem ordinary_canonical_chronological_gradient
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (A B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (hk : 0<k)
    (hgate : ‖pairDefect
      (fun i : Fin k => probedStep (rfcMethod fullMemory 1) A B g (k-1-i.val))
      (fun i : Fin k => probedSecant (rfcMethod fullMemory 1) A B g (k-1-i.val))‖<1)
    (hs : ∀ i, primalWindow base ((probedStepBasis (rfcMethod fullMemory 1) A B g k) ∘ Fin.revPerm) i≠0) :
    let m := rfcMethod fullMemory 1 (E := EuclideanSpace ℝ (Fin n))
    let S := primalWindow base ((probedStepBasis m A B g k) ∘ Fin.revPerm)
    let Y := dualWindow base ((probedImageBasis m A B g k) ∘ Fin.revPerm)
    let t := unitWindow S
    let z := rescaleWindow Y (fun i => ‖S i‖⁻¹)
    let J := cgOperator (metricRoot base)⁻¹
    let v := J (fullPostSearch 1 A B g k)
    J (probedGradient m A B g (k+1))=
      v+canonicalOperator base (B k) (combine t (modelCoefficients t (latest (crossGram t z)) v)) := by
  let m := rfcMethod fullMemory 1 (E := EuclideanSpace ℝ (Fin n))
  let U := probedStepBasis m A B g k
  let Z := probedImageBasis m A B g k
  have hU : (U ∘ Fin.revPerm) ∘ Fin.revPerm=U := by
    funext i; simp only [Function.comp_apply,Fin.revPerm_apply,Fin.rev_rev]
  have hZ : (Z ∘ Fin.revPerm) ∘ Fin.revPerm=Z := by
    funext i; simp only [Function.comp_apply,Fin.revPerm_apply,Fin.rev_rev]
  have hc := canonical_chronological_modelCorrection base hb (U ∘ Fin.revPerm) (Z ∘ Fin.revPerm)
    hs (fullPostSearch 1 A B g k)
  dsimp only at hc ⊢
  rw [hU,hZ] at hc
  rw [hc]
  simp only [cgOperator]
  rw [canonicalOperator_primal base hb,ordinary_phase_gradient_model A B g k hk hgate,map_add]


end
end krylov.Correction
