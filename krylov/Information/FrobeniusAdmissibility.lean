import krylov.Information.KnownBasePlanar

/-!
Article: main_krylov, thm:C2(a), actual physical Frobenius source class.
Use: retain every original physical base and intermediate constraint and
prove all independent true Frobenius budgets of the fixed-base signed pair.
Source: exact canonical relative reconstruction, genuine planar Frobenius
energy and the proved spectral-norm versus Frobenius-norm comparison.
-/

namespace krylov.Information
noncomputable section
open Matrix Filter Asymptotics Topology Finset krylov.Reference krylov.Secant
  krylov.Correction krylov.Methods krylov.LinearAlgebra krylov.Stability
open scoped BigOperators MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}
/-- Actual original Frobenius source admissibility, with the same physical base radius and spectral intermediate-query budgets.
Use: both norm-sensitive minimax bounds quantify over the genuine physical source scenario class.
Article: main_krylov, thm:C2(a), independent relative Frobenius budgets.
Proof: retain the equivalent spectral constraints for reuse and impose the true independent relative Frobenius budgets. -/
def Scenario.FrobeniusAdmissible (S : Scenario n) (N : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ) (r : ℝ) (ω : ℕ → ℝ) (w τ : ℝ) : Prop :=
  S.Admissible N A r ω w τ ∧
    (∀ i<N, chebyshev1.hsNorm (relativeOperator S.base (S.increment i))≤ω i) ∧
    chebyshev1.hsNorm (relativeOperator S.base S.terminal)≤w

/-- The actual original primitive physical Frobenius budgets imply the source admissibility definition with its redundant spectral constraints.
Use: no extra spectral assumption restricts the intended Frobenius source class.
Article: main_krylov, thm:C2(a), equivalence with the original primitive norm budgets.
Proof: every true spectral matrix norm is at most its genuine Frobenius
norm. Apply that standard inequality separately to each original increment
and the independent terminal perturbation; retain all physical base and
intermediate-query constraints exactly.
-/
theorem Scenario.frobeniusAdmissible_of_budgets (S : Scenario n) (N : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ) (r : ℝ) (ω : ℕ → ℝ) (w τ : ℝ)
    (hB : S.base.PosDef) (hr : relativeBudget A (S.base-A)≤r)
    (hE : ∀ i<N, (S.increment i).IsSymm ∧ chebyshev1.hsNorm (relativeOperator S.base (S.increment i))≤ω i)
    (hT : S.terminal.IsSymm) (hTb : chebyshev1.hsNorm (relativeOperator S.base S.terminal)≤w)
    (hF : ∀ i<N, (S.correction i).IsSymm ∧ relativeBudget S.base (S.correction i)≤τ) :
    S.FrobeniusAdmissible N A r ω w τ := by
  -- The genuine Frobenius budgets already imply every reused spectral constraint.
  refine ⟨⟨hB,hr,?_,hT,?_,hF⟩,(fun i hi => (hE i hi).2),hTb⟩
  · intro i hi
    exact ⟨(hE i hi).1,(spectral_le_hsNorm _).trans (hE i hi).2⟩
  · exact (spectral_le_hsNorm _).trans hTb

/-- Every original nonnegative Frobenius profile has genuine signed fixed-base planar physical scenarios satisfying every primitive source budget.
Use: the real complete-data lower family lies in the exact physical Frobenius class, already with a known base.
Article: main_krylov, thm:C2(a), admissible known-base Frobenius lower witnesses.
Proof: the canonical symmetric planar increment has Frobenius energy
γ²+2a²=1 and each original profile entry scales that same unit form.
The terminal rank-one matrix has its exact Frobenius norm. Genuine fixed
inverse-root transport preserves these canonical relative matrices and
sets the physical base exactly to A. Intermediate defects vanish.
-/
theorem knownBasePlanarScenario_frobenius_admissible
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (e f : EuclideanSpace ℝ (Fin n)) (he : ‖e‖=1) (hf : ‖f‖=1) (hef : inner ℝ e f=0)
    (ω : ℕ → ℝ) (w τ r : ℝ) (N : ℕ) (hω : ∀ i<N, 0≤ω i)
    (hw : 0≤w) (hτ : 0≤τ) (hr : 0≤r)
    (a γ σ : ℝ) (hac : 2*a^2+γ^2=1) (hσ : σ^2=1) :
    ((knownBasePlanarScenario e f (fun i => a*ω i) (fun i => γ*ω i) w σ).inPhysical (metricRoot A)⁻¹).FrobeniusAdmissible N A r ω w τ := by
  -- Compute the genuine unit Frobenius form before applying the independent original budgets.
  let P := planarMatrix e f (σ*γ) a 0
  have hP : chebyshev1.hsNorm P=1 := by
    have hs := chebyshev1.hsNorm_sq P
    rw [show P=planarMatrix e f (σ*γ) a 0 from rfl,planar_hsSq e f he hf hef] at hs
    have hσγ : (σ*γ)^2=γ^2 := by rw [mul_pow,hσ,one_mul]
    nlinarith [chebyshev1.hsNorm_nonneg P]
  let S := (knownBasePlanarScenario e f (fun i => a*ω i) (fun i => γ*ω i) w σ).inPhysical (metricRoot A)⁻¹
  have hbase : S.base=A := physical_knownBasePlanarScenario_base A hA e f _ _ w σ
  have hσabs : |σ|=1 := by nlinarith [sq_abs σ,abs_nonneg σ]
  apply Scenario.frobeniusAdmissible_of_budgets S N A r ω w τ
  · rw [hbase]; exact hA
  · simpa only [hbase,sub_self,relativeBudget,relativeOperator,Matrix.mul_zero,Matrix.zero_mul,
      chebyshev1.opNorm,norm_zero] using hr
  · intro i hi
    have heq : S.increment i=inverseFormMap (metricRoot A)⁻¹
        (planarMatrix e f (σ*(γ*ω i)) (a*ω i) 0) := rfl
    refine ⟨inverseForm_isSymm _ _ (planarMatrix_isSymm _ _ _ _ _),?_⟩
    rw [hbase,heq,relativeOperator_inverseRootForm A _ hA]
    have hscale : planarMatrix e f (σ*(γ*ω i)) (a*ω i) 0=ω i • P := by
      dsimp only [P]
      rw [← planarMatrix_scale]
      congr 1 <;> ring
    rw [hscale,hsNorm_smul,abs_of_nonneg (hω i hi),hP,mul_one]
  · exact inverseForm_isSymm _ _ (planarMatrix_isSymm _ _ _ _ _)
  · change chebyshev1.hsNorm (relativeOperator S.base
      (inverseFormMap (metricRoot A)⁻¹ (planarMatrix e f (σ*w) 0 0)))≤w
    rw [hbase,relativeOperator_inverseRootForm A _ hA]
    have hscale : planarMatrix e f (σ*w) 0 0=σ • planarMatrix e f w 0 0 := by
      rw [← planarMatrix_scale]
      simp only [mul_zero]
    rw [hscale,hsNorm_smul,hσabs,one_mul,planar_terminal_hsNorm e f he hf hef hw]
  · intro i _
    have hz : S.correction i=0 := map_zero _
    refine ⟨by rw [hz]; exact Matrix.isSymm_zero,?_⟩
    simpa only [hz,relativeBudget,relativeOperator,Matrix.mul_zero,Matrix.zero_mul,
      chebyshev1.opNorm,norm_zero] using hτ


end
end krylov.Information
