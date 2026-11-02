import krylov.Information.FormCoordinates
import krylov.Information.TwinBudgets
import krylov.Stability.UniformConjugacy
import krylov.Stability.CanonicalFCOperators
import krylov.LinearAlgebra.GershgorinBound

/-!
Article: main_krylov, s4:cor-Q, genuine pre-quadratic near-conjugacy geometry.
Use: derive the original sharp Gram defect from actual primitive increment
budgets and true common CG probe actions, before any reflection or slack claim.
Source: exact positive-root metric pairing, genuine CG conjugacy, normalized
actual operator-angle bounds and the proved sharp Gershgorin Gram estimate.
-/

namespace krylov.Information
noncomputable section
open Matrix Finset krylov.Reference krylov.Methods krylov.Secant krylov.Correction krylov.Stability krylov.LinearAlgebra
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- Every actual original physical probe has canonical deviation from identity bounded by the true finite total primitive increment budget.
Use: apply uniform actual operator geometry directly to original source scenarios.
Article: main_krylov, s4:cor-Q, actual primitive-budget near-conjugacy.
Proof: the true base becomes identity under its own inverse-root normalization. Additivity leaves exactly the original accumulated increments; their genuine relative spectral budgets sum over the actual probe prefix and are bounded by the full source profile. -/
theorem Scenario.probe_canonical_budget (S : Scenario n) (hS : S.base.PosDef) (N : ℕ)
    (ω : ℕ → ℝ) (hE : ∀ l<N, relativeBudget S.base (S.increment l)≤ω l)
    {k : ℕ} (hk : k≤N) :
    ‖canonicalOperator S.base (S.probeOracle k)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤∑ l∈range N, ω l := by
  -- Normalize the true original probe sum using its actual positive base.
  have he : relativeOperator S.base (S.probe k)=1+relativeOperator S.base (∑ l∈range k, S.increment l) := by
    simp only [Scenario.probe,relativeOperator,Matrix.mul_add,Matrix.add_mul]
    rw [show (metricRoot S.base)⁻¹*S.base*(metricRoot S.base)⁻¹=1 from relativeOperator_base S.base hS]
  change ‖canonicalOperator S.base (Matrix.toEuclideanCLM (𝕜 := ℝ) (S.probe k))-
    ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤_
  rw [canonicalOperator_matrix,he,map_add,map_one]
  change ‖ContinuousLinearMap.id ℝ _+cgOperator (relativeOperator S.base (∑ l∈range k, S.increment l))-ContinuousLinearMap.id ℝ _‖≤_
  rw [add_sub_cancel_left]
  change relativeBudget S.base (∑ l∈range k, S.increment l)≤_
  exact ((relative_budget_sum S.base (range k) S.increment).trans
    (sum_le_sum fun i hi => hE i ((mem_range.mp hi).trans_le hk))).trans
    (sum_le_sum_of_subset_of_nonneg (range_mono hk) (fun i hi _ =>
      (norm_nonneg (relativeOperator S.base (S.increment i))).trans (hE i (mem_range.mp hi))))


/-- The actual own-base normalized original CG directions of a pre-quadratic source have pairwise angles bounded by the genuine total increment budget.
Use: derive near-conjugacy from primitive source conditions without a geometric bound premise or a smallest-energy denominator.
Article: main_krylov, s4:cor-Q, actual primitive-budget near-conjugacy.
Proof: the true symmetric earlier probe agrees with the original reference on its own CG direction. Genuine quadratic CG conjugacy therefore gives the actual earlier-probe pairing zero. Exact primal/dual root pairing transfers that real equation to canonical coordinates. The proved normalized-conjugacy theorem applies with the original accumulated operator budget. -/
theorem Scenario.PreQuadratic.canonical_angle {S : Scenario n}
    (hbase : S.base.PosDef) {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    {g : EuclideanSpace ℝ (Fin n)} {N : ℕ} (h : S.PreQuadratic (cgOperator A) g N)
    (hpre : ∀ l<N, CG.gradient (cgOperator A) g l≠0)
    (hE : ∀ l<N, (S.increment l).IsSymm)
    (ω : ℕ → ℝ) (hω : ∀ l<N, relativeBudget S.base (S.increment l)≤ω l)
    {i j : ℕ} (hij : i<j) (hj : j≤N) :
    |inner ℝ (NormedSpace.normalize (cgOperator (metricRoot S.base) (CG.direction (cgOperator A) g i)))
      (NormedSpace.normalize (cgOperator (metricRoot S.base) (CG.direction (cgOperator A) g j)))|≤∑ l∈range N, ω l := by
  -- Use the real earlier symmetric probe to transfer the genuine quadratic conjugacy equation.
  have hBi : (S.probe i).IsSymm := by
    change (S.base+∑ l∈range i, S.increment l)ᵀ=_
    simp only [transpose_add,transpose_sum,hbase.1.isSymm.eq]
    congr 1
    apply sum_congr rfl
    intro l hl
    exact (hE l ((mem_range.mp hl).trans_le (hij.le.trans hj))).eq
  have hsym : (S.probeOracle i).toLinearMap.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr (Matrix.isHermitian_iff_isSymm.mpr hBi)
  have hc := (CG.invariant (cgOperator A) (cgOperator_positive A hA).1
    (cgOperator_positive A hA).2 g j (fun l hl => hpre l (hl.trans_le hj))).conjugate i j hij le_rfl
  have ho : inner ℝ (CG.direction (cgOperator A) g i) (S.probeOracle i (CG.direction (cgOperator A) g j))=0 := by
    have hh := hsym (CG.direction (cgOperator A) g i) (CG.direction (cgOperator A) g j)
    change inner ℝ (S.probeOracle i (CG.direction (cgOperator A) g i)) (CG.direction (cgOperator A) g j)=
      inner ℝ (CG.direction (cgOperator A) g i) (S.probeOracle i (CG.direction (cgOperator A) g j)) at hh
    rw [h i (hij.trans_le hj)] at hh
    have hq := (cgOperator_positive A hA).1 (CG.direction (cgOperator A) g i) (CG.direction (cgOperator A) g j)
    change inner ℝ (cgOperator A (CG.direction (cgOperator A) g i)) (CG.direction (cgOperator A) g j)=
      inner ℝ (CG.direction (cgOperator A) g i) (cgOperator A (CG.direction (cgOperator A) g j)) at hq
    exact hh.symm.trans (hq.trans hc)
  apply normalized_conjugacy_bound _ _ (canonicalOperator S.base (S.probeOracle i))
    (S.probe_canonical_budget hbase N ω hω (hij.le.trans hj))
  have hop := canonicalOperator_primal S.base hbase (S.probeOracle i) (CG.direction (cgOperator A) g j)
  change canonicalOperator S.base (S.probeOracle i) (cgOperator (metricRoot S.base) (CG.direction (cgOperator A) g j))=
    cgOperator (metricRoot S.base)⁻¹ (S.probeOracle i (CG.direction (cgOperator A) g j)) at hop
  rw [hop]
  exact (canonical_search_pairing S.base hbase _ _).symm.trans ho

end
end krylov.Information
