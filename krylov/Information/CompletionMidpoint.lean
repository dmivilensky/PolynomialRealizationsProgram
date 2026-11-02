import krylov.LinearAlgebra.CompletionWidth
import krylov.Envelope.ScenarioBudgets
import Mathlib.Analysis.Convex.Topology

/-!
Article: main_krylov, thm:C2(c), the actual observed-data consistency midpoint.
Use: define the genuine compact completion fibre and its computable hidden
quadratic midpoint, preserving singular boundary and empty-fibre cases.
Source: finite-dimensional closed spectral-ball compactness, true linear
observed-action constraints and the proved boundary-inclusive width bound.
-/

namespace krylov.Information
noncomputable section
open Matrix Set Finset krylov.Reference krylov.Secant krylov.Envelope krylov.LinearAlgebra
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The actual symmetric unit-ball completions of a prescribed observed hyperplane action.
Use: the only unobserved scalar is reconstructed from the original physical data constraints, including singular endpoint blocks.
Article: main_krylov, thm:C2(c), the known-base consistency fibre. -/
def hyperplaneCompletions (v : EuclideanSpace ℝ (Fin n)) (R : Matrix (Fin n) (Fin n) ℝ) :
    Set (Matrix (Fin n) (Fin n) ℝ) :=
  {S | S∈symmetricMatrixBall 1 ∧ ∀ u : EuclideanSpace ℝ (Fin n), inner ℝ v u=0 → cgOperator S u=cgOperator R u}

/-- The actual observed-hyperplane completion fibre is compact, even when empty or contained in the singular boundary.
Use: its true scalar extrema exist whenever the genuine source matrix supplies a feasible completion.
Article: main_krylov, thm:C2(c), compact original consistency set.
Proof: intersect the existing actual compact symmetric spectral ball with
all true closed linear observed-action equalities. Infinite intersections
of closed sets retain every original hyperplane constraint.
-/
theorem hyperplaneCompletions_compact (v : EuclideanSpace ℝ (Fin n))
    (R : Matrix (Fin n) (Fin n) ℝ) : IsCompact (hyperplaneCompletions v R) := by
  -- Every actual fixed-input matrix action is continuous in the genuine spectral matrix topology.
  have hc : IsClosed {S : Matrix (Fin n) (Fin n) ℝ | ∀ u : EuclideanSpace ℝ (Fin n),
      inner ℝ v u=0 → cgOperator S u=cgOperator R u} := by
    simp only [ofPred_forall]
    apply isClosed_iInter
    intro u
    apply isClosed_iInter
    intro _hu
    let L := (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).toAlgEquiv.toLinearMap.toContinuousLinearMap
    have ha : Continuous (fun S : Matrix (Fin n) (Fin n) ℝ => cgOperator S u) :=
      L.continuous.clm_apply continuous_const
    exact isClosed_eq ha continuous_const
  exact (symmetricMatrixBall_compact (n := n) 1).inter_right hc

/-- The actual observed-hyperplane completion fibre is convex, with the original symmetric spectral ball and every genuine action constraint preserved.
Use: its scalar quadratic image is the full consistency interval rather than a disconnected set with the same endpoints.
Article: main_krylov, thm:C2(c), convexity of the original completion fibre.
Proof: spectral-ball convex combinations retain symmetry and unit norm by
the true norm triangle inequality. Every actual observed operator action
is linear, so the same convex weights sum back to the prescribed action.
-/
theorem hyperplaneCompletions_convex (v : EuclideanSpace ℝ (Fin n))
    (R : Matrix (Fin n) (Fin n) ℝ) : Convex ℝ (hyperplaneCompletions v R) := by
  -- Preserve every genuine completion constraint under the same true convex combination.
  intro S hS T hT a b ha hb hab
  refine ⟨⟨(hS.1.1.smul a).add (hT.1.1.smul b),?_⟩,?_⟩
  · change ‖a • S+b • T‖≤1
    calc
      _ ≤ ‖a • S‖+‖b • T‖ := norm_add_le _ _
      _ = a*‖S‖+b*‖T‖ := by rw [norm_smul,norm_smul,Real.norm_of_nonneg ha,Real.norm_of_nonneg hb]
      _ ≤ a*1+b*1 := add_le_add (mul_le_mul_of_nonneg_left hS.1.2 ha) (mul_le_mul_of_nonneg_left hT.1.2 hb)
      _ = 1 := by linarith
  · intro u hu
    simp only [cgOperator,map_add,map_smul,_root_.add_apply,_root_.smul_apply]
    change a • cgOperator S u+b • cgOperator T u=cgOperator R u
    rw [hS.2 u hu,hT.2 u hu,← add_smul,hab,one_smul]

/-- The genuine unit-direction quadratic entry read from an actual symmetric completion.
Use: define the consistency interval for the original first CG diagonal, even when it differs from the true unobserved normal direction.
Article: main_krylov, thm:C2(c), q(E)=⟨ŝ₀,Eŝ₀⟩. -/
def completionQuadratic (e : EuclideanSpace ℝ (Fin n)) (S : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  inner ℝ e (cgOperator S e)

/-- The actual hidden quadratic entry is a continuous function of its genuine physical completion matrix.
Use: compact consistency sets have true attained scalar endpoints.
Article: main_krylov, thm:C2(c), continuous observed-diagonal functional.
Proof: the true fixed-input matrix action and real inner product are continuous. -/
theorem completionQuadratic_continuous (e : EuclideanSpace ℝ (Fin n)) : Continuous (completionQuadratic e) := by
  change Continuous (fun S : Matrix (Fin n) (Fin n) ℝ => inner ℝ e (cgOperator S e))
  apply continuous_const.inner
  let L := (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).toAlgEquiv.toLinearMap.toContinuousLinearMap
  exact L.continuous.clm_apply continuous_const

/-- The actual midpoint of the hidden quadratic consistency interval, with the ordinary real empty-set convention on impossible data.
Use: it depends solely on the prescribed genuine observed hyperplane action and the known unit norm budget.
Article: main_krylov, thm:C2(c), computable consistency-interval midpoint q̂. -/
def completionMidpoint (v e : EuclideanSpace ℝ (Fin n)) (R : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (sInf (completionQuadratic e '' hyperplaneCompletions v R)+
    sSup (completionQuadratic e '' hyperplaneCompletions v R))/2

/-- Equal actual observed-hyperplane restrictions give exactly the same completion fibre.
Use: the full unknown matrix never provides extra information to the midpoint algorithm.
Article: main_krylov, thm:C2(c), exact data-only consistency set.
Proof: both genuine source fibres impose precisely the same known operator action on every perpendicular query vector. -/
theorem hyperplaneCompletions_congr (v : EuclideanSpace ℝ (Fin n))
    (R T : Matrix (Fin n) (Fin n) ℝ)
    (h : ∀ u : EuclideanSpace ℝ (Fin n), inner ℝ v u=0 → cgOperator R u=cgOperator T u) :
    hyperplaneCompletions v R=hyperplaneCompletions v T := by
  ext S
  constructor
  · rintro ⟨hS,hSR⟩
    exact ⟨hS,fun u hu => (hSR u hu).trans (h u hu)⟩
  · rintro ⟨hS,hST⟩
    exact ⟨hS,fun u hu => (hST u hu).trans (h u hu).symm⟩

/-- The genuine consistency midpoint is identical on all matrices with the same actual observed hyperplane action.
Use: this is the exact information restriction for the source's known-base midpoint decision, including infeasible data.
Article: main_krylov, thm:C2(c), data-only midpoint invariance.
Proof: equal actual observed restrictions give exactly the same original completion set and therefore the same two real scalar endpoints. -/
theorem completionMidpoint_congr (v e : EuclideanSpace ℝ (Fin n))
    (R T : Matrix (Fin n) (Fin n) ℝ)
    (h : ∀ u : EuclideanSpace ℝ (Fin n), inner ℝ v u=0 → cgOperator R u=cgOperator T u) :
    completionMidpoint v e R=completionMidpoint v e T := by
  rw [completionMidpoint,completionMidpoint,hyperplaneCompletions_congr v R T h]


/-- Every genuine feasible observed-hyperplane completion has the full closed scalar consistency interval, with both endpoints attained.
Use: the actual midpoint is the midpoint of the complete original consistency interval even on the spectral-ball boundary.
Article: main_krylov, thm:C2(c), exact compact scalar consistency interval.
Proof: the true completion fibre is convex and compact. Its actual
continuous quadratic functional therefore has a connected compact image,
which is exactly the interval between its genuine real infimum and supremum.
-/
theorem completionQuadratic_image_interval (v e : EuclideanSpace ℝ (Fin n))
    (R : Matrix (Fin n) (Fin n) ℝ) (hne : (hyperplaneCompletions v R).Nonempty) :
    completionQuadratic e '' hyperplaneCompletions v R=
      Icc (sInf (completionQuadratic e '' hyperplaneCompletions v R))
        (sSup (completionQuadratic e '' hyperplaneCompletions v R)) := by
  have hc := completionQuadratic_continuous e
  exact eq_Icc_of_connected_compact
    ⟨hne.image _,(hyperplaneCompletions_convex v R).isPreconnected.image _ hc.continuousOn⟩
    ((hyperplaneCompletions_compact v R).image hc)

/-- The genuine data-only consistency midpoint has unit size and the exact boundary-inclusive hidden-entry error bound for every actual symmetric unit-budget source matrix.
Use: the informed-base algorithm needs neither an inverse-gap hypothesis nor an assumed midpoint or scalar interval estimate.
Article: main_krylov, thm:C2(c), |q̂|≤1 and |q−q̂|≤1−‖x‖².
Proof: the actual source matrix belongs to its genuine compact completion
fibre. Both scalar endpoints are attained by real admissible matrices. The
proved boundary-inclusive quadratic diameter bounds their gap, while the
true source entry lies between them. The midpoint has at most half that
gap and stays in the genuine unit quadratic interval by spectral norm bounds.
-/
theorem completionMidpoint_bounds (v e : EuclideanSpace ℝ (Fin n))
    (hv : ‖v‖=1) (he : ‖e‖=1) (R : Matrix (Fin n) (Fin n) ℝ)
    (hR : R.IsSymm) (hRn : ‖R‖≤1) :
    |completionMidpoint v e R|≤1 ∧
      |completionQuadratic e R-completionMidpoint v e R|≤
        1-‖cgOperator R v-(inner ℝ v (cgOperator R v)) • v‖^2 := by
  -- Attain both endpoints on the genuine feasible physical source completion set.
  let K := hyperplaneCompletions v R
  let q := completionQuadratic e
  have hmem : R∈K := ⟨⟨hR,hRn⟩,fun _ _ => rfl⟩
  have hK := hyperplaneCompletions_compact v R
  have hq := completionQuadratic_continuous e
  obtain ⟨L,hL,hlo,hmin⟩ := hK.exists_sInf_image_eq_and_le ⟨R,hmem⟩ hq.continuousOn
  obtain ⟨U,hU,hhi,hmax⟩ := hK.exists_sSup_image_eq_and_ge ⟨R,hmem⟩ hq.continuousOn
  have hlow := hmin R hmem
  have hhigh := hmax R hmem
  have hsym (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.IsSymm) : (cgOperator S).toLinearMap.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr (Matrix.isHermitian_iff_isSymm.mpr hS)
  have hnorm (S : Matrix (Fin n) (Fin n) ℝ) (hS : ‖S‖≤1) : ‖cgOperator S‖≤1 := by
    simpa only [cgOperator,Matrix.l2_opNorm_toEuclideanCLM] using hS
  have hdiam := completion_quadratic_diameter (cgOperator U) (cgOperator L) (cgOperator R)
    (hsym U hU.1.1) (hsym L hL.1.1) (hsym R hR)
    (hnorm U hU.1.2) (hnorm L hL.1.2) v e hv he hU.2 hL.2
  have hgap : q U-q L≤2*(1-‖cgOperator R v-(inner ℝ v (cgOperator R v)) • v‖^2) :=
    (le_abs_self _).trans hdiam
  have hquad (S : Matrix (Fin n) (Fin n) ℝ) (hS : ‖S‖≤1) : |q S|≤1 := by
    simpa only [q,completionQuadratic,he,one_pow] using contraction_quadratic_bound (cgOperator S) (hnorm S hS) e
  have hlunit := abs_le.mp (hquad L hL.1.2)
  have huunit := abs_le.mp (hquad U hU.1.2)
  have hmid : completionMidpoint v e R=(q L+q U)/2 := by
    rw [completionMidpoint,hlo,hhi]
  rw [hmid]
  exact ⟨abs_le.mpr ⟨by linarith,by linarith⟩,abs_le.mpr ⟨by linarith,by linarith⟩⟩


end
end krylov.Information
