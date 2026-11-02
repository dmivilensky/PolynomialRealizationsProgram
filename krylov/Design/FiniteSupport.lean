import krylov.Design.AtomicBridge

/-!
Article: main_krylov, thm:B, vanishing information for insufficient support.
Use: handle the singular side of the design objective by constructing an actual
normalized annihilating polynomial, rather than using a singular inverse formula.
Source: the elementary product of node factors; finite L2 is reused from jacobi.
-/

namespace krylov.Design
noncomputable section
open Polynomial jacobi.Finite MeasureTheory
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [T2Space X]

/-- Information vanishes when the degree can annihilate every atom.
Article: main_krylov, thm:B, low-support endpoint.
Proof: explicitly normalize the node product at the exterior point and integrate its zero values. -/
theorem christoffel_atomic_zero {N m : ℕ} (M : DiscreteMeasure N) (hNm : N ≤ m)
    (z : Fin N → X) (x : C(X, ℝ)) (hz : ∀ i, x (z i) = M.node i)
    (a : ℝ) (ha : ∀ i, a ≠ M.node i) :
    christoffel m a x (atomicProbability M z) = 0 := by
  let P : ℝ[X] := ∏ i : Fin N, (Polynomial.X - C (M.node i))
  have hdeg : P.natDegree ≤ N := by
    simp [P]
  have hPa : P.eval a ≠ 0 := by
    simp only [P, eval_prod, eval_sub, eval_X, eval_C]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => sub_ne_zero.mpr (ha i)
  have hzP (i : Fin N) : P.eval (M.node i) = 0 := by
    simp only [P, eval_prod, eval_sub, eval_X, eval_C]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)
  let p : Competitor m a := ⟨(P.eval a)⁻¹ • P,
    (natDegree_smul_le _ _).trans (hdeg.trans hNm), by simp [hPa]⟩
  have hp : M.evaluate p.val = 0 := by
    apply PiLp.ext
    intro i
    simp [DiscreteMeasure.evaluate, p, hzP i]
  apply le_antisymm
  · have h := christoffel_le m a x (atomicProbability M z) p
    rw [polynomialEnergy_atomic M z x hz, hp, norm_zero, zero_pow (by decide : 2 ≠ 0)] at h
    exact h
  · exact christoffel_nonneg _ _ _ _

end
end krylov.Design
