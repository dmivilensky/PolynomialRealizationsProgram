import krylov.Stability.CanonicalDirectionGeometry
import krylov.Stability.UniformConjugacy
import krylov.Methods.DirectionStaircase

/-!
Article: main_krylov, apB:lem:UAsteps, genuine normalized actual FC old observations.
Use: derive all unit Gram, pair-image and conjugacy hypotheses of the uniform
search estimate from the real executed FC history and true canonical budgets.
Source: actual retained-solve nonzero columns, genuine root cancellation and
proved exact canonical FC conjugacy/angle identities.
-/

namespace krylov.Stability
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n k : ℕ}

/-- Every actual FC step entering the next defined solve has a genuinely nonzero canonical image.
Use: normalize real old columns only after proving their actual nonzero domain.
Article: main_krylov, apB:lem:UAsteps.
Proof: the genuine next coefficient matrix forces the actual physical step
nonzero, and the real inverse root cancels any zero canonical image. -/
theorem fullFC_old_canonical_step_ne (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (A : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (i : ℕ)
    (hnext : IsUnit (crossGram
      (windowImages (selectedWindow fullMemory (fcHistory fullMemory A g (i+1))))
      (windowSteps (selectedWindow fullMemory (fcHistory fullMemory A g (i+1))))).det) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (fcStep fullMemory A g i)≠0 := by
  have hn := fullFC_step_ne_of_next_solve A g i hnext
  intro hz
  have he := congrArg (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹) hz
  rw [canonical_primal_dual_cancel base hb,map_zero] at he
  exact hn he

/-- The true normalized old-step Gram of a defined FC prefix has its dimension-times-budget spectral deviation bound.
Use: all actual rectangular Gram conditioning premises follow from real observed conjugacy and true operator budgets.
Article: main_krylov, apB:lem:UAsteps.
Proof: every genuine preceding step is nonzero by the actual next solve.
The proved real FC canonical angle estimate controls each distinct old pair;
apply the actual normalized Gram spectral bound. -/
theorem fullFC_old_step_gram (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (A : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) {δ : ℝ} (hδ : 0≤δ)
    (hsolve : ∀ i≤k, IsUnit (crossGram
      (windowImages (selectedWindow fullMemory (fcHistory fullMemory A g i)))
      (windowSteps (selectedWindow fullMemory (fcHistory fullMemory A g i)))).det)
    (hA : ∀ i<k, ‖canonicalOperator base (A i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤δ) :
    let t : Fin k → EuclideanSpace ℝ (Fin n) := fun i => NormedSpace.normalize
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (fcStep fullMemory A g i.val))
    ‖crossGram t t-1‖≤(k : ℝ)*δ := by
  -- Unit normalization and every angle bound come from the actually executed retained solves.
  apply unitGram_deviation _ (fun i => NormedSpace.norm_normalize
    (fullFC_old_canonical_step_ne base hb A g i.val (hsolve (i.val+1) (by omega)))) hδ
  intro i j hij
  by_cases hi : i.val < j.val
  · rw [real_inner_comm]
    exact fullFC_canonical_angle base hb A g hi (hsolve j.val j.isLt.le) (hA i.val i.isLt)
  · have hj : j.val < i.val := by
      have hn : i.val≠j.val := fun he => hij (Fin.ext he)
      omega
    exact fullFC_canonical_angle base hb A g hj (hsolve i.val i.isLt.le) (hA j.val j.isLt)

/-- Each true normalized canonical old secant image annihilates the actual current canonical FC direction.
Use: discharge the real observed-image conjugacy premise of the uniform projected-direction estimate.
Article: main_krylov, apB:lem:UAsteps.
Proof: move the actual normalization through the true linear canonical
operator, transfer the real root pairing, and use genuine executed old-image conjugacy. -/
theorem fullFC_old_canonical_image (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (A : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (hsolve : IsUnit (crossGram
      (windowImages (selectedWindow fullMemory (fcHistory fullMemory A g k)))
      (windowSteps (selectedWindow fullMemory (fcHistory fullMemory A g k)))).det) (i : Fin k) :
    let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
    inner ℝ (canonicalOperator base (A i.val) (NormedSpace.normalize (R (fcStep fullMemory A g i.val))))
      (R (fcDirection fullMemory A g k))=0 := by
  dsimp only
  rw [NormedSpace.normalize,map_smul,real_inner_smul_left,canonicalOperator_primal base hb,real_inner_comm]
  rw [← canonical_search_pairing base hb]
  have he := fullFC_direction_conjugate A g i.isLt hsolve
  change inner ℝ (fcDirection fullMemory A g k) (A i.val (fcStep fullMemory A g i.val))=0 at he
  rw [he,mul_zero]

/-- A true canonical operator budget bounds the real normalized old-image error by that same budget.
Use: the source relative pair-error hypothesis is derived from actual queried FC steps and the real operator.
Article: main_krylov, apB:lem:UAsteps.
Proof: the genuine next defined solve and actual root cancellation give a
true unit old column; apply the actual deviation operator norm to that column. -/
theorem fullFC_old_canonical_image_error (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (A : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (i : ℕ)
    (hnext : IsUnit (crossGram
      (windowImages (selectedWindow fullMemory (fcHistory fullMemory A g (i+1))))
      (windowSteps (selectedWindow fullMemory (fcHistory fullMemory A g (i+1))))).det)
    {δ : ℝ} (hA : ‖canonicalOperator base (A i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤δ) :
    let t := NormedSpace.normalize (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (fcStep fullMemory A g i))
    ‖canonicalOperator base (A i) t-t‖≤δ := by
  let t := NormedSpace.normalize (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (fcStep fullMemory A g i))
  have ht : ‖t‖=1 := NormedSpace.norm_normalize (fullFC_old_canonical_step_ne base hb A g i hnext)
  have he := (canonicalOperator base (A i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))).le_opNorm t
  rw [ht,mul_one] at he
  exact he.trans hA
end
end krylov.Stability
