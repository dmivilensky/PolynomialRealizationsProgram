import krylov.OneGradient.KnownBaseSourceEmbedding
import krylov.Information.TwinBudgets
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(b), whole physical source budget conversion.
Use: original own-base admissibility enters the common known-base cube
with exact metric factors and one uniform primitive parameter bound.
Source: true physical Loewner prior bounds, genuine relative-budget metric
transfer and exact supremum norm of the original finite source coordinates.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix Finset krylov.Reference krylov.Secant krylov.Information
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
variable {n : ℕ}

/-- Every original admissible source has its exact known-metric query
and independent output budgets inflated by at most 1+c*t.
Use: the full-source informed upper bound covers the original own-base
budgets with a common factor tending to one, including all zero profiles.
Article: main_krylov, thm:local(b), exact whole-source metric budget transfer.
Proof: the genuine prior ball gives the physical base upper Loewner bound.
Apply the existing signed-form budget transfer to every actual individual
source increment and its real independent terminal form. -/
theorem knownBase_admissible_known_budgets
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (S : Scenario (n+1)) (omega : ℕ → ℝ) (homega : ∀ l<n,0≤omega l)
    (w c t : ℝ) (hw : 0≤w) (hc : 0≤c) (ht : 0≤t) (hsmall : c*t<1)
    (hS : S.Admissible n base (c*t) (fun l => omega l*t) (w*t) 0) :
    (∀ l<n,relativeBudget base (S.increment l)≤(1+c*t)*(omega l*t)) ∧
      relativeBudget base S.terminal≤(1+c*t)*(w*t) := by
  have hfactor : 0≤1+c*t := by positivity
  have hbase := (relative_displacement_base base S.base hb hS.1.1.isSymm
    (mul_nonneg hc ht) hsmall hS.2.1).2.1
  refine ⟨fun l hl => relative_budget_upper_metric base S.base (S.increment l) hb hS.1
    (hS.2.2.1 l hl).1 hfactor (mul_nonneg (homega l hl) ht) hbase (hS.2.2.1 l hl).2,
    relative_budget_upper_metric base S.base S.terminal hb hS.1 hS.2.2.2.1
      hfactor (mul_nonneg hw ht) hbase hS.2.2.2.2.1⟩

/-- The true whole-source canonical tuple is bounded uniformly by
H*t on every original admissible source, where H depends only on the
fixed prior/query/output profile and remains positive at zero budgets.
Use: one common actual cubic source tube covers all physical scenarios,
with no path, continuity, rank or bounded-output premise on source choices.
Article: main_krylov, thm:local(b), original source-wide parameter bound.
Proof: convert every genuine own-base budget to its exact known metric.
For t≤1, the factor is at most 1+c and each actual individual query weight
is at most the original finite total. The real finite source product norm
then gives the same common bound on the full parameter tuple. -/
theorem knownBase_admissible_parameter_norm
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (S : Scenario (n+1)) (omega : ℕ → ℝ) (homega : ∀ l<n,0≤omega l)
    (w c t : ℝ) (hw : 0≤w) (hc : 0≤c) (ht : 0≤t) (ht1 : t≤1) (hsmall : c*t<1)
    (hS : S.Admissible n base (c*t) (fun l => omega l*t) (w*t) 0) :
    let H := 1+c+(1+c)*((∑ l∈range n,omega l)+w)
    ‖knownBaseSourceParameters base hb S hS.1.1.isSymm
      (fun l hl => (hS.2.2.1 l hl).1) hS.2.2.2.1‖≤H*t := by
  let W := ∑ l∈range n,omega l
  let H := 1+c+(1+c)*(W+w)
  have hW : 0≤W := sum_nonneg (fun l hl => homega l (mem_range.mp hl))
  have hH : 0≤H := by dsimp only [H];positivity
  have hfactor : 1+c*t≤1+c := by nlinarith
  have hcH : c≤H := by dsimp only [H];nlinarith [mul_nonneg (by linarith : 0≤1+c) (add_nonneg hW hw)]
  have hWH : (1+c)*W≤H := by dsimp only [H];nlinarith [mul_nonneg (by linarith : 0≤1+c) hw]
  have hwH : (1+c)*w≤H := by dsimp only [H];nlinarith [mul_nonneg (by linarith : 0≤1+c) hW]
  have hbud := knownBase_admissible_known_budgets base hb S omega homega w c t hw hc ht hsmall hS
  apply knownBaseSourceParameters_norm_le base hb S hS.1.1.isSymm
    (fun l hl => (hS.2.2.1 l hl).1) hS.2.2.2.1 (H*t) (mul_nonneg hH ht)
  · exact hS.2.1.trans (mul_le_mul_of_nonneg_right hcH ht)
  · intro l hl
    have hlW : omega l≤W := single_le_sum (fun j hj => homega j (mem_range.mp hj)) (mem_range.mpr hl)
    calc
      _ ≤ (1+c*t)*(omega l*t) := hbud.1 l hl
      _ ≤ (1+c)*(W*t) := mul_le_mul hfactor (mul_le_mul_of_nonneg_right hlW ht)
        (mul_nonneg (homega l hl) ht) (by linarith)
      _ = ((1+c)*W)*t := by ring
      _ ≤ H*t := mul_le_mul_of_nonneg_right hWH ht
  · calc
      _ ≤ (1+c*t)*(w*t) := hbud.2
      _ ≤ (1+c)*(w*t) := mul_le_mul_of_nonneg_right hfactor (mul_nonneg hw ht)
      _ = ((1+c)*w)*t := by ring
      _ ≤ H*t := mul_le_mul_of_nonneg_right hwH ht

end
end krylov.OneGradient
