import krylov.Correction.FullBasisAlgebra
import krylov.Information.BudgetMidpoint

/-!
Article: main_krylov, thm:C2(c), reconstruction from true finite query data.
Use: construct an actual matrix extension of the observed later-query
operator actions and prove that it supplies the complete original midpoint
fibre, with no inaccessible full source matrix used by the decision.
Source: exact square query-basis reconstruction and the true codimension-one
normal functional, followed by proved observed-restriction midpoint invariance.
-/

namespace krylov.Information
noncomputable section
open Matrix Filter Asymptotics Topology Finset krylov.Reference krylov.Secant krylov.Envelope
  krylov.Correction krylov.Methods krylov.LinearAlgebra krylov.Stability
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The actual operator matrix extending an observed full query array, with any prescribed value in its unobserved slot.
Use: finite known query directions and their genuine measured images determine this extension without exposing the unknown full matrix.
Article: main_krylov, thm:C2(c), actual data extension Y C⁻¹. -/
def queryDataMatrix (U Y : Fin n → EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  fullBasisMatrix Y*(fullBasisMatrix U)⁻¹

/-- Actual query-column matrix action equals the real linear combination of its original physical columns.
Use: reconstruct vectors and operator actions through the true finite query coefficients.
Article: main_krylov, thm:C2(c), exact query-basis synthesis.
Proof: each genuine Euclidean coordinate is the same finite matrix-product sum, with scalar factors commuted. -/
theorem fullBasisMatrix_action (U : Fin n → EuclideanSpace ℝ (Fin n))
    (c : EuclideanSpace ℝ (Fin n)) : cgOperator (fullBasisMatrix U) c=∑ i, c i • U i := by
  ext j
  change (∑ i, U i j*c i)=(∑ i, c i • U i) j
  simp only [WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,smul_eq_mul]
  exact sum_congr rfl fun _ _ => mul_comm _ _

/-- Every actual vector has its exact true full-query decomposition on the genuine inverse domain.
Use: the observed hyperplane is proved from actual query data and is not an assumed codimension-one representation.
Article: main_krylov, thm:C2(c), u=Σ(C⁻¹u)_i d_i.
Proof: the actual query matrix cancels its genuine inverse, and its physical action is the original column sum. -/
theorem queryBasis_decomposition (U : Fin n → EuclideanSpace ℝ (Fin n))
    (hU : IsUnit (fullBasisMatrix U).det) (u : EuclideanSpace ℝ (Fin n)) :
    u=∑ i, (cgOperator (fullBasisMatrix U)⁻¹ u) i • U i := by
  have hh : cgOperator (fullBasisMatrix U) (cgOperator (fullBasisMatrix U)⁻¹ u)=u := by
    simp only [cgOperator,← mul_apply_eq_comp,← map_mul,mul_nonsing_inv _ hU,map_one,one_apply_eq_self]
  exact hh.symm.trans (fullBasisMatrix_action U _)

/-- The actual matrix extension returns every originally prescribed true query image on its genuine full-basis inverse domain.
Use: the midpoint reconstruction reads only the real measured columns and any chosen harmless unobserved slot.
Article: main_krylov, thm:C2(c), (Y C⁻¹)d_i=y_i.
Proof: exact physical column transport gives the true product Y C⁻¹ C;
its justified inverse cancellation returns precisely the original image array.
-/
theorem queryDataMatrix_columns (U Y : Fin n → EuclideanSpace ℝ (Fin n))
    (hU : IsUnit (fullBasisMatrix U).det) (i : Fin n) :
    cgOperator (queryDataMatrix U Y) (U i)=Y i := by
  -- Preserve the actual physical column array before cancelling the genuine query-basis inverse.
  have he : fullBasisMatrix (fun j => cgOperator (queryDataMatrix U Y) (U j))=fullBasisMatrix Y := by
    rw [fullBasisMatrix_map]
    simp only [queryDataMatrix,Matrix.mul_assoc,nonsing_inv_mul _ hU,Matrix.mul_one]
  exact congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => WithLp.toLp 2 (fun j => M j i)) he

/-- A true unit normal vanishing on every observed full-query column has a nonzero pairing with the sole missing column.
Use: the actual observed directions span exactly the normal hyperplane, with no extra rank or subspace premise.
Article: main_krylov, thm:C2(c), genuine single missing query coefficient.
Proof: exact full-query reconstruction expresses every real normal pairing
as the missing query coefficient times that column's pairing. Were the latter
zero, the true unit normal would pair to zero with itself, a contradiction.
-/
theorem queryBasis_normal_coordinate (U : Fin n → EuclideanSpace ℝ (Fin n))
    (hU : IsUnit (fullBasisMatrix U).det) (v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖=1)
    (a : Fin n) (horth : ∀ i : Fin n, i≠a → inner ℝ v (U i)=0) :
    inner ℝ v (U a)≠0 ∧ ∀ u : EuclideanSpace ℝ (Fin n),
      inner ℝ v u=(cgOperator (fullBasisMatrix U)⁻¹ u) a*inner ℝ v (U a) := by
  -- Derive the true normal functional directly from actual full-query coefficients.
  have hpair (u : EuclideanSpace ℝ (Fin n)) :
      inner ℝ v u=(cgOperator (fullBasisMatrix U)⁻¹ u) a*inner ℝ v (U a) := by
    conv_lhs => rw [queryBasis_decomposition U hU u]
    simp only [inner_sum,real_inner_smul_right]
    rw [sum_eq_single a]
    · intro i _ hi
      rw [horth i hi,mul_zero]
    · simp
  refine ⟨?_,hpair⟩
  intro hz
  have hh := hpair v
  rw [real_inner_self_eq_norm_sq,hv,one_pow,hz,mul_zero] at hh
  exact one_ne_zero hh

/-- Two actual linear actions agreeing on every observed full-query column agree on the entire genuine observed normal hyperplane.
Use: the true finite measured data determine precisely the original hyperplane restriction used by the consistency midpoint.
Article: main_krylov, thm:C2(c), exact finite-query to observed-hyperplane bridge.
Proof: the actual unit normal makes the one missing coefficient nonzero
in its true coordinate functional. A perpendicular input therefore has
zero missing coefficient. Reconstruct its genuine full-query sum and apply
the given original observed-column actions term by term.
-/
theorem queryBasis_hyperplane_action (U : Fin n → EuclideanSpace ℝ (Fin n))
    (hU : IsUnit (fullBasisMatrix U).det) (v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖=1)
    (a : Fin n) (horth : ∀ i : Fin n, i≠a → inner ℝ v (U i)=0)
    (S T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hST : ∀ i : Fin n, i≠a → S (U i)=T (U i)) :
    ∀ u : EuclideanSpace ℝ (Fin n), inner ℝ v u=0 → S u=T u := by
  -- The genuinely missing coefficient vanishes on exactly the observed normal hyperplane.
  obtain ⟨hne,hpair⟩ := queryBasis_normal_coordinate U hU v hv a horth
  intro u hu
  have hc : (cgOperator (fullBasisMatrix U)⁻¹ u) a=0 :=
    (mul_eq_zero.mp ((hpair u).symm.trans hu)).resolve_right hne
  rw [queryBasis_decomposition U hU u,map_sum,map_sum]
  apply sum_congr rfl
  intro i _
  by_cases hi : i=a
  · subst i
    simp only [hc,zero_smul,map_zero]
  · rw [map_smul,map_smul,hST i hi]

/-- Every genuine finite observed-query array gives exactly the same primitive-budget consistency midpoint as the unknown actual source operator.
Use: the informed decision is constructed entirely from true finite data, with its complete source completion fibre proved rather than assumed.
Article: main_krylov, thm:C2(c), actual data-only finite-query midpoint reconstruction.
Proof: the explicit extension returns every real prescribed query image.
It therefore agrees with the true source on all observed full-query columns.
The genuine unit normal and full query rank extend those equalities to the
entire actual observed hyperplane; exact midpoint information invariance
then identifies the finite-data decision with the true source midpoint.
-/
theorem queryDataMatrix_midpoint (U Y : Fin n → EuclideanSpace ℝ (Fin n))
    (hU : IsUnit (fullBasisMatrix U).det) (v e : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖=1)
    (a : Fin n) (horth : ∀ i : Fin n, i≠a → inner ℝ v (U i)=0)
    (R : Matrix (Fin n) (Fin n) ℝ) (hY : ∀ i : Fin n, i≠a → Y i=cgOperator R (U i)) (ω : ℝ) :
    budgetCompletionMidpoint ω v e (queryDataMatrix U Y)=budgetCompletionMidpoint ω v e R := by
  -- The one arbitrary unobserved image is never used in the genuine completion restriction.
  apply budgetCompletionMidpoint_congr
  apply queryBasis_hyperplane_action U hU v hv a horth
  intro i hi
  exact (queryDataMatrix_columns U Y hU i).trans (hY i hi)

end
end krylov.Information
