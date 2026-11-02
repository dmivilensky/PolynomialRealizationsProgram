import krylov.Methods.ChronologicalWindow
import krylov.Correction.ObservedSearchDomains

/-!
Article: main_krylov, thm:UCq, true canonical observed-search geometry.
Use: Transport genuine chronological observed solves, span and conjugacy
equations to the original positive-root metric before uniform estimates.
Source: actual executed-pair reindexing, genuine metric pairing invariance
and positive quadratic forms of operators within one half of the identity.
-/

namespace krylov.Stability
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Correction
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n k : ℕ}

/-- The true observed conjugacy cross Gram is preserved by its primal/dual metric maps.
Use: Derive actual uniform RFC search geometry from its true observed data.
Article: main_krylov, thm:UCq.
Proof: Each genuine matrix entry is the preserved canonical search pairing, with real inner-product symmetry.
-/
theorem canonical_crossGram (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (s y : Fin k → EuclideanSpace ℝ (Fin n)) :
    crossGram (dualWindow base y) (primalWindow base s)=crossGram y s := by
  ext i j
  change inner ℝ (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ (y i))
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (s j))=inner ℝ (y i) (s j)
  rw [real_inner_comm,← canonical_search_pairing base hb,real_inner_comm]

/-- The actual observed-list direction has its genuine chronological canonical old-span equation.
Use: Derive actual uniform RFC search geometry from its true observed data.
Article: main_krylov, thm:UCq.
Proof: Reindex the true executed solve chronologically, move the real coefficient synthesis through the positive-root map and use zero-safe normalization invariance of its actual span.
-/
theorem chronological_canonical_direction_span (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (s y : ℕ → EuclideanSpace ℝ (Fin n)) (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
    let J := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
    R (windowDirection (executedPairs s y k) g)+cgOperator base (J g)∈
      Submodule.span ℝ (Set.range (unitWindow (fun i : Fin k => R (s i.val)))) := by
  let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
  dsimp only
  rw [windowDirection_chronological,canonical_base_dual base hb]
  change _∈Submodule.span ℝ (Set.range (fun i : Fin k => NormedSpace.normalize (R (s i.val))))
  rw [span_normalize_eq_span]
  have hc := combine_mem_span (fun i : Fin k => R (s i.val))
    (conjugacyCoefficients (fun i : Fin k => s i.val) (fun i : Fin k => y i.val) g)
  have he : R (conjugacyDirection (fun i : Fin k => s i.val) (fun i : Fin k => y i.val) g)+R g=
      combine (fun i : Fin k => R (s i.val))
        (conjugacyCoefficients (fun i : Fin k => s i.val) (fun i : Fin k => y i.val) g) := by
    simp only [conjugacyDirection,map_add,map_neg,combine_operator R]
    abel
  rw [he]
  exact hc

/-- A nonsingular actual chronological observed solve annihilates every true canonical old secant image.
Use: Derive actual uniform RFC search geometry from its true observed data.
Article: main_krylov, thm:UCq.
Proof: The implemented coefficient inverse gives exact real conjugacy; chronological execution and actual primal/dual pairing transfer that equation.
-/
theorem chronological_canonical_image_conjugacy (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (s y : ℕ → EuclideanSpace ℝ (Fin n)) (g : EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (hC : IsUnit (crossGram (fun i : Fin k => y i.val) (fun i : Fin k => s i.val)).det) (i : Fin k) :
    inner ℝ (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ (y i.val))
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (windowDirection (executedPairs s y k) g))=0 := by
  rw [windowDirection_chronological,real_inner_comm,← canonical_search_pairing base hb,real_inner_comm]
  exact congrFun (conjugacyDirection_conjugate _ _ g hC) i

/-- Every nonzero actual direction has strictly positive search curvature under a half-identity canonical operator allowance.
Use: Derive actual uniform RFC search geometry from its true observed data.
Article: main_krylov, thm:UCq.
Proof: The genuine metric root cannot annihilate a nonzero physical direction. Cauchy--Schwarz bounds the actual quadratic-form deviation by one half of its positive squared canonical norm.
-/
theorem canonical_curvature_positive (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (d : EuclideanSpace ℝ (Fin n)) (hd : d≠0)
    (hA : ‖canonicalOperator base A-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤(1/2 : ℝ)) :
    0< inner ℝ d (A d) := by
  let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
  have hRd : R d≠0 := by
    intro hz
    have ht := congrArg (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹) hz
    rw [canonical_primal_dual_cancel base hb,map_zero] at ht
    exact hd ht
  have ht := (canonicalOperator base A-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))).le_opNorm (R d)
  have hi := norm_inner_le_norm (𝕜 := ℝ) (R d)
    ((canonicalOperator base A-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) (R d))
  rw [Real.norm_eq_abs] at hi
  have hbnd := hi.trans (mul_le_mul_of_nonneg_left (ht.trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _))) (norm_nonneg _))
  have he : inner ℝ (R d) ((canonicalOperator base A-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) (R d))=
      inner ℝ d (A d)-‖R d‖^2 := by
    change inner ℝ (R d) (canonicalOperator base A (R d)-R d)=_
    rw [inner_sub_right,real_inner_self_eq_norm_sq]
    dsimp only [R]
    rw [canonicalOperator_primal base hb,← canonical_search_pairing base hb]
  rw [he] at hbnd
  have hp := sq_pos_of_pos (norm_pos_iff.mpr hRd)
  nlinarith [(abs_le.mp hbnd).1]

end
end krylov.Stability
