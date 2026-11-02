import krylov.Information.FlagMetric

/-!
Article: main_krylov, thm:centre, joint metric admissibility of the reflected scenario.
Use: discharge H1--H3 for the actual constructed base, every increment and
the terminal perturbation, with the article's precise common slack.
Source: the actual direction-Gram distortion bound, the spectral triangle
inequality and the exact Loewner change of metric. Intermediate actions (H4)
are handled separately by symmetric single-image completion.
-/

namespace krylov.Information
noncomputable section
open Matrix Finset krylov.Secant
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
variable {p : ℕ}

/-- The relative spectral budget is a seminorm under addition of physical forms.
Use: bound the accumulated hidden-block displacement in its genuine base metric.
Article: main_krylov, thm:centre(iii), triangle inequality for relative perturbations.
Proof: inverse-root congruence is additive and the fixed spectral norm is subadditive. -/
theorem relative_budget_add (G E F : Matrix (Fin p) (Fin p) ℝ) :
    relativeBudget G (E+F) ≤ relativeBudget G E+relativeBudget G F := by
  simp only [relativeBudget,relativeOperator,Matrix.mul_add,Matrix.add_mul]
  exact norm_add_le _ _

/-- A finite family of physical forms has at most the sum of its actual relative budgets.
Use: keep each individual profile budget, including zero entries, in the twin displacement.
Article: main_krylov, thm:centre(iii), finite sum of hidden compressions.
Proof: commute the fixed congruence with the finite sum and use the norm triangle inequality. -/
theorem relative_budget_sum {ι : Type*} (G : Matrix (Fin p) (Fin p) ℝ)
    (s : Finset ι) (E : ι → Matrix (Fin p) (Fin p) ℝ) :
    relativeBudget G (∑ i∈s, E i) ≤ ∑ i∈s, relativeBudget G (E i) := by
  simp only [relativeBudget,relativeOperator,Matrix.mul_sum,Matrix.sum_mul]
  exact norm_sum_le _ _

/-- Scalar multiplication scales the actual relative spectral budget by the scalar's absolute value.
Use: the factor two in the twin base displacement is exact.
Article: main_krylov, thm:centre(iii), ϖ=2κ_ε²Σ‖E_l‖_(A₀).
Proof: congruence is linear and the earlier fixed operator norm is homogeneous. -/
theorem relative_budget_smul (G E : Matrix (Fin p) (Fin p) ℝ) (c : ℝ) :
    relativeBudget G (c • E)=|c| * relativeBudget G E := by
  rw [relativeBudget,relativeOperator_smul,chebyshev1.opNorm_smul]
  rfl

/-- Negating a physical perturbation preserves its actual relative spectral budget.
Use: terminal reflection and the sign in each reflected increment cost no budget.
Article: main_krylov, thm:centre, E′^♯=−E′.
Proof: inverse-root congruence preserves negation and the norm is even. -/
theorem relative_budget_neg (G E : Matrix (Fin p) (Fin p) ℝ) :
    relativeBudget G (-E)=relativeBudget G E := by
  simp only [relativeBudget,relativeOperator_neg,chebyshev1.opNorm,norm_neg]

/-- The near-conjugacy factor is strictly positive on the actual source domain.
Use: the exact H1 reciprocal slack and the summed base displacement are well defined.
Article: main_krylov, apD:centre, κ_ε²>0 for ε<1.
Proof: the genuine norm defect is nonnegative and its denominator is strictly positive. -/
theorem flagDistortion_pos (G : Matrix (Fin p) (Fin p) ℝ)
    (he : directionDefect G < 1) : 0 < flagDistortion G := by
  have hn : 0 ≤ directionDefect G := chebyshev1.opNorm_nonneg _
  exact div_pos (by linarith) (by linarith)

/-- The common relative base displacement used in the article's inner class.
Use: one number controls positivity and every new-base budget simultaneously.
Article: main_krylov, apD:centre, ϖ=2κ_ε²Σ_l‖E_l‖_(A₀). -/
def Scenario.twinDisplacement (S : Scenario p) (N : ℕ) : ℝ :=
  2*flagDistortion S.base*∑ l∈range N, relativeBudget S.base (S.increment l)

/-- A real symmetric increment remains symmetric under the actual flag reflection.
Use: the signed Loewner budget characterization applies to each constructed twin increment.
Article: main_krylov, thm:centre, symmetry of E_l^♯.
Proof: transpose the diagonal congruence and use symmetry of the original increment. -/
theorem reflectedIncrement_isSymm (l : ℕ) (E : Matrix (Fin p) (Fin p) ℝ)
    (hE : E.IsSymm) : (reflectedIncrement l E).IsSymm := by
  simp only [reflectedIncrement,flagReflection,Matrix.IsSymm,transpose_neg,
    transpose_mul,diagonal_transpose,hE.eq,Matrix.mul_assoc]

/-- Each genuine reflected increment has at most the proved near-conjugacy budget loss.
Use: verify all original increment budgets after the common change of base.
Article: main_krylov, thm:centre(iii), ‖E_l^♯‖_(A₀)≤κ_ε²‖E_l‖_(A₀).
Proof: the actual diagonal reflection has unit-modulus signs; apply the
proved coordinate-contraction estimate and remove the harmless outer sign. -/
theorem reflectedIncrement_budget (G E : Matrix (Fin p) (Fin p) ℝ)
    (hG : G.PosDef) (hE : E.IsSymm) (he : directionDefect G < 1) (l : ℕ) :
    relativeBudget G (reflectedIncrement l E) ≤ flagDistortion G*relativeBudget G E := by
  rw [reflectedIncrement,relative_budget_neg]
  simpa only [flagReflection,diagonal_transpose] using
    flag_relative_budget G E hG hE he (fun i => if i.val≤l then 1 else -1)
      (fun i => by split_ifs <;> norm_num)

/-- The explicit twin base has the article's actual summed relative displacement bound.
Use: positivity and all admissibility statements below concern the constructed base itself.
Article: main_krylov, thm:centre(iii), ‖A₀^♯−A₀‖_(A₀)≤ϖ.
Proof: each hidden-coordinate projection contracts the diagonal energy form;
sum its derived actual relative-budget bounds and retain the exact factor two. -/
theorem Scenario.reflect_base_displacement (S : Scenario p) (N : ℕ)
    (hG : S.base.PosDef) (he : directionDefect S.base < 1)
    (hE : ∀ l<N, (S.increment l).IsSymm) :
    relativeBudget S.base ((S.reflect N).base-S.base) ≤ S.twinDisplacement N := by
  -- Estimate the actual hidden-block sum, rather than assuming its budget.
  have hb (l : ℕ) (hl : l∈range N) := flag_relative_budget S.base (S.increment l)
    hG (hE l (mem_range.mp hl)) he (fun i => if i.val≤l then 0 else 1)
      (fun i => by split_ifs <;> norm_num)
  simp only [diagonal_transpose] at hb
  change relativeBudget S.base
    ((S.base+(2 : ℝ) • ∑ l∈range N,
      complementProjection p l*S.increment l*complementProjection p l)-S.base)≤_
  rw [add_sub_cancel_left,relative_budget_smul,abs_of_nonneg (by norm_num : (0 : ℝ)≤2)]
  have hs := (relative_budget_sum S.base (range N)
    (fun l => complementProjection p l*S.increment l*complementProjection p l)).trans
      (sum_le_sum hb)
  calc
    _ ≤ 2*(∑ l∈range N, flagDistortion S.base*relativeBudget S.base (S.increment l)) :=
      mul_le_mul_of_nonneg_left hs (by norm_num)
    _ = S.twinDisplacement N := by rw [← mul_sum]; exact (mul_assoc _ _ _).symm

/-- The constructed twin base is symmetric on the finite source horizon.
Use: no symmetry premise on a purported output base is needed for admissibility.
Article: main_krylov, thm:centre(iii), symmetry of A₀^♯.
Proof: every complementary diagonal congruence is symmetric, as is their real scalar sum. -/
theorem Scenario.reflect_base_isSymm (S : Scenario p) (N : ℕ)
    (hG : S.base.IsSymm) (hE : ∀ l<N, (S.increment l).IsSymm) :
    (S.reflect N).base.IsSymm := by
  -- Transpose each genuine summand before reassembling the finite base displacement.
  change (S.reflect N).baseᵀ=(S.reflect N).base
  simp only [Scenario.reflect,transpose_add,transpose_smul,transpose_sum,hG.eq]
  congr 2
  apply sum_congr rfl
  intro l hl
  simp only [transpose_mul,complementProjection,diagonal_transpose,
    (hE l (mem_range.mp hl)).eq,Matrix.mul_assoc]

/-- Strict inner-class displacement gives the exact base sandwich and positive twin metric.
Use: a common positive output base supports all reflected spectral budgets.
Article: main_krylov, thm:centre(iii), (1−ϖ)A₀≼A₀^♯≼(1+ϖ)A₀.
Proof: the proved actual displacement controls the physical Loewner endpoints;
the strict positive lower endpoint establishes positive definiteness. -/
theorem Scenario.reflect_base_metric (S : Scenario p) (N : ℕ)
    (hG : S.base.PosDef) (he : directionDefect S.base < 1)
    (hE : ∀ l<N, (S.increment l).IsSymm) (hv : S.twinDisplacement N < 1) :
    (1-S.twinDisplacement N) • S.base ≤ (S.reflect N).base ∧
      (S.reflect N).base ≤ (1+S.twinDisplacement N) • S.base ∧
      (S.reflect N).base.PosDef := by
  apply relative_displacement_base S.base (S.reflect N).base hG
    (S.reflect_base_isSymm N hG.1.isSymm hE) _ hv
    (S.reflect_base_displacement N hG he hE)
  exact mul_nonneg (mul_nonneg (by norm_num) (flagDistortion_pos _ he).le)
    (sum_nonneg (fun _ _ => chebyshev1.opNorm_nonneg _))

/-- The original H1 slack proves every individual reflected budget in the actual new metric.
Use: covers arbitrary profiles, including zero increments, with one common twin base.
Article: main_krylov, thm:centre, condition H1.
Proof: the reflection costs κ_ε², exactly cancelled by H1; the remaining
factor 1−ϖ is exactly the proved metric-change slack. -/
theorem Scenario.reflect_increment_budget (S : Scenario p) (N : ℕ)
    (hG : S.base.PosDef) (he : directionDefect S.base < 1)
    (hE : ∀ l<N, (S.increment l).IsSymm) (hv : S.twinDisplacement N < 1)
    (l : ℕ) (hl : l<N) {w : ℝ} (hw : 0≤w)
    (hbudget : relativeBudget S.base (S.increment l) ≤
      ((1-S.twinDisplacement N)/flagDistortion S.base)*w) :
    relativeBudget (S.reflect N).base ((S.reflect N).increment l) ≤ w := by
  -- Apply the exact old-metric distortion before changing to the derived positive twin base.
  obtain ⟨hlo,_,hpos⟩ := S.reflect_base_metric N hG he hE hv
  apply relative_budget_change S.base (S.reflect N).base _ hG hpos
    (reflectedIncrement_isSymm l _ (hE l hl)) (by linarith) hw hlo
  exact (reflectedIncrement_budget _ _ hG (hE l hl) he l).trans
    ((mul_le_mul_of_nonneg_left hbudget (flagDistortion_pos _ he).le).trans_eq (by
      field_simp [(flagDistortion_pos S.base he).ne'] ))

/-- The original H2 slack proves the terminal reflected budget in the actual new metric.
Use: terminal and individual increment budgets use the same constructed positive base.
Article: main_krylov, thm:centre, condition H2.
Proof: negation preserves the old budget, and the exact lower base sandwich
absorbs the remaining common factor 1−ϖ. -/
theorem Scenario.reflect_terminal_budget (S : Scenario p) (N : ℕ)
    (hG : S.base.PosDef) (he : directionDefect S.base < 1)
    (hE : ∀ l<N, (S.increment l).IsSymm) (hT : S.terminal.IsSymm)
    (hv : S.twinDisplacement N < 1) {w : ℝ} (hw : 0≤w)
    (hbudget : relativeBudget S.base S.terminal ≤ (1-S.twinDisplacement N)*w) :
    relativeBudget (S.reflect N).base (S.reflect N).terminal ≤ w := by
  obtain ⟨hlo,_,hpos⟩ := S.reflect_base_metric N hG he hE hv
  apply relative_budget_change S.base (S.reflect N).base _ hG hpos
    (by simp only [Scenario.reflect,Matrix.IsSymm,transpose_neg,hT.eq])
    (by linarith) hw hlo
  simpa only [Scenario.reflect,relative_budget_neg] using hbudget

/-- An upper comparison of metrics transfers the budget of a symmetric perturbation.
Use: the twin base displacement costs at most (1+r)ϖ in the fixed reference metric.
Article: main_krylov, thm:centre(iii), reference-radius transfer.
Proof: dominate both signed old-metric endpoints and convert them back
using the actual relative spectral norm characterization. -/
theorem relative_budget_upper_metric (A G E : Matrix (Fin p) (Fin p) ℝ)
    (hA : A.PosDef) (hG : G.PosDef) (hE : E.IsSymm)
    {c v : ℝ} (hc : 0≤c) (hv : 0≤v) (hGA : G≤c • A)
    (hbudget : relativeBudget G E≤v) : relativeBudget A E≤c*v := by
  obtain ⟨hl,hu⟩ := (relative_norm_le_iff G E hG hE hv).mp hbudget
  have hs := smul_le_smul_of_nonneg_left hGA hv
  rw [smul_smul,mul_comm v] at hs
  exact (relative_norm_le_iff A E hA hE (mul_nonneg hc hv)).mpr
    ⟨(neg_le_neg hs).trans hl,hu.trans hs⟩

/-- The actual H3 radius slack proves the fixed-reference radius of the constructed twin base.
Use: H1--H3 jointly preserve positivity, all perturbation budgets and the original base ball.
Article: main_krylov, thm:centre, condition H3.
Proof: H3 first bounds the original base radius and hence its reference
Loewner upper endpoint. Transfer the actual twin displacement through that
endpoint and add the original radius, exactly as prescribed by H3. -/
theorem Scenario.reflect_reference_radius (S : Scenario p) (N : ℕ)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A.PosDef)
    (hG : S.base.PosDef) (he : directionDefect S.base < 1)
    (hE : ∀ l<N, (S.increment l).IsSymm) {r : ℝ} (hr : 0≤r)
    (hbudget : relativeBudget A (S.base-A)+(1+r)*S.twinDisplacement N≤r) :
    relativeBudget A ((S.reflect N).base-A)≤r := by
  -- H3 itself supplies the old reference-radius bound needed for the metric transfer.
  have hv : 0≤S.twinDisplacement N := mul_nonneg
    (mul_nonneg (by norm_num) (flagDistortion_pos _ he).le)
    (sum_nonneg (fun _ _ => chebyshev1.opNorm_nonneg _))
  have hsym : (S.base-A).IsSymm := by
    simp only [Matrix.IsSymm,transpose_sub,hG.1.isSymm.eq,hA.1.isSymm.eq]
  have hold : relativeBudget A (S.base-A)≤r :=
    (le_add_of_nonneg_right (mul_nonneg (by linarith only [hr] : 0≤1+r) hv)).trans hbudget
  have hu := ((relative_norm_le_iff A _ hA hsym hr).mp hold).2
  have hGA : S.base≤(1+r) • A := by
    calc
      S.base = A+(S.base-A) := by abel
      _ ≤ A+r • A := add_le_add le_rfl hu
      _ = (1+r) • A := by rw [add_smul,one_smul]
  have hdisp := relative_budget_upper_metric A S.base ((S.reflect N).base-S.base)
    hA hG (by simp only [Matrix.IsSymm,transpose_sub,
      (S.reflect_base_isSymm N hG.1.isSymm hE).eq,hG.1.isSymm.eq])
    (by linarith only [hr] : 0≤1+r) hv hGA (S.reflect_base_displacement N hG he hE)
  have hadd : (S.reflect N).base-A=(S.base-A)+((S.reflect N).base-S.base) := by abel
  have hnorm := congrArg (relativeBudget A) hadd
  exact hnorm.le.trans ((relative_budget_add _ _ _).trans
    ((add_le_add le_rfl hdisp).trans hbudget))

end
end krylov.Information
