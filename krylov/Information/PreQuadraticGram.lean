import krylov.Information.PreQuadraticAngles
import krylov.Information.DirectionGram
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
variable {N : ℕ}

/-- The true common pre-quadratic direction Gram satisfies exactly the original defect bound ε≤(n−1)W₀ from primitive physical increment budgets.
Use: derive the precise flag distortion required by the source's stated 1−4nW₀ slack, with no assumed near-conjugacy certificate.
Article: main_krylov, s4:cor-Q, genuine common pre-quadratic Gram defect.
Proof: genuine full active CG gives an actual independent common direction
basis. Its real own-base normalized columns are unit by the proved true
column-energy theorem. Original probe agreement and primitive source budgets
bound every genuine pairwise angle. The actual normalized direction Gram
is exactly that real column Gram; the sharp Gershgorin estimate supplies
precisely n−1, rather than an extra dimension loss. -/
theorem Scenario.PreQuadratic.reference_gram_bound {S : Scenario (N+1)}
    (hbase : S.base.PosDef) {A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ} (hA : A.PosDef)
    {g : EuclideanSpace ℝ (Fin (N+1))} (hcount : referenceAtomCount A hA g=N+1)
    (h : S.PreQuadratic (cgOperator A) g N)
    (hE : ∀ l<N, (S.increment l).IsSymm)
    (ω : ℕ → ℝ) (hω : ∀ l<N, relativeBudget S.base (S.increment l)≤ω l) :
    let D := fullBasisMatrix (referenceDirectionColumns A g)
    directionDefect (Dᵀ*S.base*D)≤(N : ℝ)*(∑ l∈range N, ω l) := by
  -- Full genuine CG rank makes the original physical direction-energy normalizer well-defined.
  let D := fullBasisMatrix (referenceDirectionColumns A g)
  let u := fun i : Fin (N+1) => NormedSpace.normalize
    (cgOperator (metricRoot S.base) (euclideanColumn D i))
  have hD : IsUnit D.det := fullBasisMatrix_unit _ (referenceDirectionColumns_independent A hA g hcount)
  have hunit (i : Fin (N+1)) : ‖u i‖=1 := by
    change ‖NormedSpace.normalize (cgOperator (metricRoot S.base) (euclideanColumn D i))‖=1
    rw [← normalizedColumns_column]
    exact normalizedColumns_norm S.base D hbase hD i
  have hpre (i : ℕ) (hi : i<N) : CG.gradient (cgOperator A) g i≠0 := cg_nonstagnation A hA g i (by omega)
  have hangle (i j : Fin (N+1)) (hij : i≠j) : |inner ℝ (u i) (u j)|≤∑ l∈range N, ω l := by
    rcases lt_or_gt_of_ne hij with hij' | hji'
    · exact h.canonical_angle hbase hA hpre hE ω hω hij' (by omega)
    · rw [real_inner_comm]
      exact h.canonical_angle hbase hA hpre hE ω hω hji' (by omega)
  have hW : 0≤∑ l∈range N, ω l := sum_nonneg fun i hi =>
    (norm_nonneg (relativeOperator S.base (S.increment i))).trans (hω i (mem_range.mp hi))
  have hnorm := unitGram_deviation_sharp u hunit hW hangle
  change directionDefect (Dᵀ*S.base*D)≤_
  rw [directionDefect,normalizedDirectionGram_unitWindow S.base D hbase hD]
  simpa only [Nat.add_sub_cancel,u,chebyshev1.opNorm] using hnorm

end
end krylov.Information
