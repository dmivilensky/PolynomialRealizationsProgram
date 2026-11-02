import krylov.Information.CommonTwinCentre

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

/-- The actual accumulated old-prefix curvature is symmetric under only the original finite source symmetries.
Use: Use the real old-block sum in physical spectral-budget comparisons.
Article: main_krylov, s4:cor-Q, actual common-centre metric estimates.
Proof: Transpose the finite sum and each genuine diagonal prefix congruence. -/
theorem Scenario.oldPart_isSymm (S : Scenario p) (k : ℕ)
    (hE : ∀ l<k, (S.increment l).IsSymm) : (S.oldPart k).IsSymm := by
  change (S.oldPart k)ᵀ=S.oldPart k
  simp only [Scenario.oldPart,transpose_sum]
  apply sum_congr rfl
  intro l hl
  simp only [transpose_mul,(prefixProjection_isSymm p l).eq,
    (hE l (mem_range.mp hl)).eq,Matrix.mul_assoc]

/-- The genuine accumulated old-prefix curvature costs at most the true flag distortion times the sum of original individual budgets.
Use: Derive the hidden terminal-model error without an assumed projector estimate.
Article: main_krylov, s4:cor-Q, actual common-centre metric estimates.
Proof: The proved flag-relative-budget theorem controls each actual old-prefix congruence; the genuine relative spectral norm is subadditive over their finite sum. -/
theorem Scenario.oldPart_budget (S : Scenario p) (k : ℕ)
    (hG : S.base.PosDef) (he : directionDefect S.base<1)
    (hE : ∀ l<k, (S.increment l).IsSymm) :
    relativeBudget S.base (S.oldPart k)≤
      flagDistortion S.base*(∑ l∈range k, relativeBudget S.base (S.increment l)) := by
  -- Sum only the original finite-horizon old-prefix compressions.
  have hb (l : ℕ) (hl : l∈range k) := flag_relative_budget S.base (S.increment l)
    hG (hE l (mem_range.mp hl)) he (fun i => if i.val≤l then 1 else 0)
      (fun i => by split_ifs <;> norm_num)
  simp only [diagonal_transpose] at hb
  calc
    _ ≤ ∑ l∈range k, relativeBudget S.base (prefixProjection p l*S.increment l*prefixProjection p l) :=
      relative_budget_sum _ _ _
    _ ≤ ∑ l∈range k, flagDistortion S.base*relativeBudget S.base (S.increment l) := sum_le_sum hb
    _ = _ := (mul_sum _ _ _).symm

/-- The true coordinate centre differs from its original base by at most 3W and its real terminal operator by at most 2W+w.
Use: Establish the original centre and hidden-error constants from primitive source budgets.
Article: main_krylov, s4:cor-Q, actual common-centre metric estimates.
Proof: The finite observed-centre identity leaves precisely the old-block sum. Its derived budget is at most 2W; the original accumulated probe drift costs W and the independent terminal perturbation costs w. -/
theorem Scenario.coordinate_centre_budgets (S : Scenario (N+1))
    (hG : S.base.PosDef) (he : directionDefect S.base<1)
    (hk : flagDistortion S.base≤2)
    (hE : ∀ l<N, (S.increment l).IsSymm) (ω : ℕ → ℝ) (w : ℝ)
    (hω : ∀ l<N, relativeBudget S.base (S.increment l)≤ω l)
    (hw : relativeBudget S.base S.terminal≤w) :
    relativeBudget S.base (latest (observed S.probe)-S.base)≤3*(∑ l∈range N, ω l) ∧
      relativeBudget S.base (S.lastOperator N-latest (observed S.probe))≤2*(∑ l∈range N, ω l)+w := by
  -- The finite centre identity separates old-prefix curvature from the actual probe drift.
  let W := ∑ l∈range N, ω l
  have hs : (∑ l∈range N, relativeBudget S.base (S.increment l))≤W := sum_le_sum fun l hl => hω l (mem_range.mp hl)
  have hW : 0≤W := (sum_nonneg (fun l _ => norm_nonneg (relativeOperator S.base (S.increment l)))).trans hs
  have hy : relativeBudget S.base (S.oldPart N)≤2*W :=
    (S.oldPart_budget N hG he hE).trans (by nlinarith [flagDistortion_pos S.base he])
  have hj := S.latest_probe_error_finite hG.1.isSymm hE
  have hcentre : latest (observed S.probe)-S.base=
      (∑ l∈range N, S.increment l)+(-S.oldPart N) := by
    rw [← hj,Scenario.probe]
    abel
  have hdelta : S.lastOperator N-latest (observed S.probe)=S.oldPart N+S.terminal := by
    rw [← hj,Scenario.lastOperator]
    abel
  constructor
  · rw [hcentre]
    have hsum := (relative_budget_sum S.base (range N) S.increment).trans hs
    have hh := relative_budget_add S.base (∑ l∈range N, S.increment l) (-S.oldPart N)
    rw [relative_budget_neg] at hh
    exact hh.trans (by linarith)
  · rw [hdelta]
    exact (relative_budget_add _ _ _).trans (add_le_add hy hw)


/-- The actual observed physical centre is exactly the inverse physical form of the chronological latest model.
Use: Transport true centre budgets through a genuine full physical direction basis.
Article: main_krylov, s4:cor-Q, actual common-centre metric estimates.
Proof: The proved actual physical observation identity recovers the true original coordinate pairings. -/
theorem Scenario.physicalCentre_form (S : Scenario p) (D : Matrix (Fin p) (Fin p) ℝ)
    (hD : IsUnit D.det) : S.physicalCentre D=inverseFormMap D (latest (observed S.probe)) := by
  unfold Scenario.physicalCentre
  rw [S.physical_observed_data D hD]
  rfl

/-- The genuine 3W centre displacement and 2W+w terminal-error bounds survive physical coordinate transport exactly.
Use: Use the actual original physical base metric in the instance comparison.
Article: main_krylov, s4:cor-Q, actual common-centre metric estimates.
Proof: The physical inverse form map is linear and preserves symmetry and genuine relative spectral budgets. Transport both proved coordinate-centre inequalities through that same real congruence. -/
theorem Scenario.physical_centre_budgets (S : Scenario (N+1))
    (D : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hD : IsUnit D.det)
    (hG : S.base.PosDef) (he : directionDefect S.base<1)
    (hk : flagDistortion S.base≤2)
    (hE : ∀ l<N, (S.increment l).IsSymm) (hT : S.terminal.IsSymm)
    (ω : ℕ → ℝ) (w : ℝ)
    (hω : ∀ l<N, relativeBudget S.base (S.increment l)≤ω l)
    (hw : relativeBudget S.base S.terminal≤w) :
    relativeBudget (S.inPhysical D).base (S.physicalCentre D-(S.inPhysical D).base)≤3*(∑ l∈range N, ω l) ∧
      relativeBudget (S.inPhysical D).base ((S.inPhysical D).lastOperator N-S.physicalCentre D)≤2*(∑ l∈range N, ω l)+w := by
  -- Transport each true physical form through the same original full direction inverse.
  have hj := latest_isSymm (observed S.probe)
  have hb : S.physicalCentre D-(S.inPhysical D).base=
      inverseFormMap D (latest (observed S.probe)-S.base) := by
    rw [S.physicalCentre_form D hD,map_sub]
    rfl
  have hd : (S.inPhysical D).lastOperator N-S.physicalCentre D=
      inverseFormMap D (S.lastOperator N-latest (observed S.probe)) := by
    rw [S.physicalCentre_form D hD,map_sub]
    rw [Scenario.inPhysical,Scenario.mapForms_lastOperator]
  have hl : (S.lastOperator N).IsSymm := by
    change (S.probe N+S.terminal)ᵀ=S.probe N+S.terminal
    simp only [Scenario.probe,transpose_add,transpose_sum,hG.1.isSymm.eq,hT.eq]
    congr 2
    apply sum_congr rfl
    intro l hl
    exact (hE l (mem_range.mp hl)).eq
  have hbound := S.coordinate_centre_budgets hG he hk hE ω w hω hw
  rw [hb,hd]
  change relativeBudget (inverseFormMap D S.base) _≤_ ∧ relativeBudget (inverseFormMap D S.base) _≤_
  rw [inverseForm_budget D S.base _ hD hG (hj.sub hG.1.isSymm),
    inverseForm_budget D S.base _ hD hG (hl.sub hj)]
  exact hbound


end
end krylov.Information
