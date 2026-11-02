import krylov.Information.RelativeReferenceError

/-!
Article: main_krylov, s4:cor-Q, actual original own-normalized instance comparison.
Use: compare genuine executed outputs in their own true base metrics and
actual last-CG-error normalizations with exactly the printed source losses.
Source: original common-twin source slack, exact physical spectral metric
comparison and true compact CG reference-error regularity.
-/

namespace krylov.Information
noncomputable section
open Matrix Finset krylov.Reference krylov.Methods krylov.Secant krylov.Correction krylov.Stability krylov.LinearAlgebra
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator MatrixOrder
variable {N : ℕ}

/-- One genuine relative reference ball has positive true last CG errors and a common relative error comparison for every pair of its positive physical bases.
Use: Remove any additional source-displacement restriction from the original instance theorem.
Article: main_krylov, s4:cor-Q, original instance-optimality and inner attainment.
Proof: Choose the actual compact error tube before shrinking the genuine reference ball. Its diameter then fits in that tube, and spectral-budget subadditivity bounds every real pair displacement. -/
theorem referenceBaseChart_relative_error_ball
    (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hcount : referenceAtomCount A hA g=N+1) :
    ∃ r₀ L : ℝ, 0<r₀ ∧ r₀<1 ∧ 0≤L ∧
      ∀ (B C : Matrix (Fin (N+1)) (Fin (N+1)) ℝ), B.PosDef → C.PosDef →
        relativeBudget A (B-A)≤r₀ → relativeBudget A (C-A)≤r₀ →
        0<‖cgCanonicalError B g N‖ ∧ 0<‖cgCanonicalError C g N‖ ∧
          ‖cgCanonicalError C g N‖≤‖cgCanonicalError B g N‖*(1+L*relativeBudget A (C-B)) := by
  -- Shrink the actual reference ball only after the genuine compact tube has been proved.
  obtain ⟨r,δ,L,hr,hr₁,hδ,hL,hcontrol⟩ := referenceBaseChart_relative_error_control A hA g hcount
  let r₀ := min r (δ/2)
  have hr₀ : 0<r₀ := lt_min hr (half_pos hδ)
  have hr₀₁ : r₀<1 := (min_le_left _ _).trans_lt hr₁
  refine ⟨r₀,L,hr₀,hr₀₁,hL,?_⟩
  intro B C hB hC hBr hCr
  have hmove : relativeBudget A (C-B)≤δ := by
    have he : C-B=(C-A)+(-(B-A)) := by abel
    rw [he]
    have ht := relative_budget_add A (C-A) (-(B-A))
    rw [relative_budget_neg] at ht
    exact ht.trans (by nlinarith [min_le_right r (δ/2)])
  have hb := hcontrol B C hB hC.1.isSymm (hBr.trans (min_le_left _ _)) hmove
  have hz : relativeBudget A (C-C)≤δ := by
    simpa only [sub_self,relativeBudget,relativeOperator,Matrix.mul_zero,Matrix.zero_mul,chebyshev1.opNorm,norm_zero] using hδ.le
  have hc := hcontrol C C hC hC.1.isSymm (hCr.trans (min_le_left _ _)) hz
  exact ⟨hb.1,hc.1,hb.2⟩

end
end krylov.Information
