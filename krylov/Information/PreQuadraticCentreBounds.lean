import krylov.Information.CentreBudgets
import krylov.Information.PreQuadraticModel

/-!
Article: main_krylov, s4:cor-Q, original physical common-centre budgets.
Use: derive actual common-centre positivity and the printed 3W and 2W+w
bounds from original individual source budgets and true flag geometry.
Source: finite flag telescoping, real spectral norm subadditivity, exact
relative-budget congruence and the standard Neumann inverse estimate.
-/

namespace krylov.Information
noncomputable section
open Matrix Finset krylov.Reference krylov.Methods krylov.Secant krylov.Correction krylov.Stability krylov.LinearAlgebra
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator MatrixOrder
variable {p N : ℕ}

/-- Original pre-quadratic physical increment and terminal budgets imply the true common-centre displacement and hidden-terminal-error bounds.
Use: Discharge the source centre estimates directly from real pre-quadratic hypotheses.
Article: main_krylov, s4:cor-Q, actual common-centre metric estimates.
Proof: Full active CG gives a genuine common direction basis. Primitive physical budgets give its sharp actual Gram defect at most one quarter and flag distortion at most two. Forward budget invariance and exact physical centre transport then give both stated bounds. -/
theorem Scenario.PreQuadratic.centre_budgets {S : Scenario (N+1)}
    {Q : Matrix (Fin (N+1)) (Fin (N+1)) ℝ} (hQ : Q.PosDef)
    {g : EuclideanSpace ℝ (Fin (N+1))} (hcount : referenceAtomCount Q hQ g=N+1)
    (h : S.PreQuadratic (cgOperator Q) g N) (hbase : S.base.PosDef)
    (hE : ∀ l<N, (S.increment l).IsSymm) (hT : S.terminal.IsSymm)
    (ω : ℕ → ℝ) (w : ℝ)
    (hω : ∀ l<N, relativeBudget S.base (S.increment l)≤ω l)
    (hw : relativeBudget S.base S.terminal≤w)
    (hsmall : 4*((N : ℝ)+1)*(∑ l∈range N, ω l)≤1) :
    relativeBudget S.base (S.preQuadraticCentre Q g-S.base)≤3*(∑ l∈range N, ω l) ∧
      relativeBudget S.base (S.lastOperator N-S.preQuadraticCentre Q g)≤2*(∑ l∈range N, ω l)+w := by
  -- The original physical source supplies the genuine common coordinate metric and its true Gram defect.
  let D := fullBasisMatrix (referenceDirectionColumns Q g)
  let C := S.inCoordinates D
  -- The finite centre identity separates old-prefix curvature from the actual probe drift.
  let W := ∑ l∈range N, ω l
  have hD : IsUnit D.det := fullBasisMatrix_unit _ (referenceDirectionColumns_independent Q hQ g hcount)
  have hC : C.base.PosDef := formMap_posDef D S.base hD hbase
  have hεW : directionDefect C.base≤(N : ℝ)*W := h.reference_gram_bound hbase hQ hcount hE ω hω
  have hW : 0≤W := sum_nonneg fun l hl => (norm_nonneg (relativeOperator S.base (S.increment l))).trans (hω l (mem_range.mp hl))
  have hε : 0≤directionDefect C.base := norm_nonneg _
  have hquarter : directionDefect C.base≤(1/4 : ℝ) := by nlinarith
  have he : directionDefect C.base<1 := by linarith
  have hk : flagDistortion C.base≤2 := by
    change (1+directionDefect C.base)/(1-directionDefect C.base)≤2
    apply (div_le_iff₀ (by linarith : 0<1-directionDefect C.base)).mpr
    linarith
  have hCE (i : ℕ) (hi : i<N) : (C.increment i).IsSymm := formMap_isSymm D _ (hE i hi)
  have hCω (i : ℕ) (hi : i<N) : relativeBudget C.base (C.increment i)≤ω i := by
    rw [show relativeBudget C.base (C.increment i)=relativeBudget S.base (S.increment i) from
      formMap_budget D S.base _ hD hbase (hE i hi)]
    exact hω i hi
  have hCT : C.terminal.IsSymm := formMap_isSymm D _ hT
  have hCw : relativeBudget C.base C.terminal≤w := by
    rw [show relativeBudget C.base C.terminal=relativeBudget S.base S.terminal from
      formMap_budget D S.base _ hD hbase hT]
    exact hw
  have hb := C.physical_centre_budgets D hD hC he hk hCE hCT ω w hCω hCw
  rw [S.inCoordinates_inPhysical D hD] at hb
  exact hb


/-- The actual common pre-quadratic observed physical centre is symmetric.
Use: Prove the centre metric domain before using its inverse.
Article: main_krylov, s4:cor-Q, actual common-centre metric estimates.
Proof: The latest-information model is symmetric and its genuine physical inverse congruence preserves symmetry. -/
theorem Scenario.preQuadraticCentre_isSymm (S : Scenario (N+1))
    (Q : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hQ : Q.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hcount : referenceAtomCount Q hQ g=N+1) :
    (S.preQuadraticCentre Q g).IsSymm := by
  let D := fullBasisMatrix (referenceDirectionColumns Q g)
  have hD : IsUnit D.det := fullBasisMatrix_unit _ (referenceDirectionColumns_independent Q hQ g hcount)
  change ((S.inCoordinates D).physicalCentre D).IsSymm
  rw [Scenario.physicalCentre_form _ D hD]
  exact inverseForm_isSymm D _ (latest_isSymm _)

/-- Original pre-quadratic budgets prove positivity and genuine invertibility of the common physical centre and bound its true relative inverse norm by two.
Use: Remove all supplied centre inverse-domain premises from the source instance comparison.
Article: main_krylov, s4:cor-Q, actual common-centre metric estimates.
Proof: The proved 3W displacement is at most one half. The exact relative Loewner comparison makes the actual centre positive, and the previously proved Neumann inverse bound applies to its genuine relative matrix. -/
theorem Scenario.PreQuadratic.centre_domain {S : Scenario (N+1)}
    {Q : Matrix (Fin (N+1)) (Fin (N+1)) ℝ} (hQ : Q.PosDef)
    {g : EuclideanSpace ℝ (Fin (N+1))} (hcount : referenceAtomCount Q hQ g=N+1)
    (h : S.PreQuadratic (cgOperator Q) g N) (hbase : S.base.PosDef)
    (hE : ∀ l<N, (S.increment l).IsSymm) (hT : S.terminal.IsSymm)
    (ω : ℕ → ℝ) (w : ℝ)
    (hω : ∀ l<N, relativeBudget S.base (S.increment l)≤ω l)
    (hw : relativeBudget S.base S.terminal≤w)
    (hsmall : 4*((N : ℝ)+1)*(∑ l∈range N, ω l)≤1)
    (hhalf : 3*(∑ l∈range N, ω l)≤1/2) :
    let J := S.preQuadraticCentre Q g
    J.PosDef ∧ IsUnit J.det ∧ ‖(relativeOperator S.base J)⁻¹‖≤2 := by
  -- The original budgets bound the true centre displacement before any inverse is used.
  let J := S.preQuadraticCentre Q g
  have hb := h.centre_budgets hQ hcount hbase hE hT ω w hω hw hsmall
  have hbudget : relativeBudget S.base (J-S.base)≤1/2 := hb.1.trans hhalf
  have hsym : J.IsSymm := S.preQuadraticCentre_isSymm Q hQ g hcount
  have hp : J.PosDef := (relative_displacement_base S.base J hbase hsym
    (by norm_num : (0 : ℝ)≤1/2) (by norm_num) hbudget).2.2
  have he : relativeOperator S.base J-1=relativeOperator S.base (J-S.base) := by
    simp only [relativeOperator,Matrix.mul_sub,Matrix.sub_mul]
    rw [show (metricRoot S.base)⁻¹*S.base*(metricRoot S.base)⁻¹=1 from relativeOperator_base S.base hbase]
  have hn : ‖relativeOperator S.base J-1‖≤1/2 := by rw [he]; exact hbudget
  exact ⟨hp,(Matrix.isUnit_iff_isUnit_det J).mp hp.isUnit,(near_identity_inverse _ hn).2.1⟩

end
end krylov.Information
