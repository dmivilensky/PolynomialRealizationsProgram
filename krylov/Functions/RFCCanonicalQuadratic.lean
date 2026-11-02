import krylov.Functions.RFCPhysicalCompact
import krylov.Functions.FCLeadingCoordinates

/-!
Article: main_krylov, thm:Htransfer, the exact RFC quadratic/canonical dictionary.
Use: identify the genuine physical coefficient with the printed
staircase/fresh-defect product for arbitrary physical segment operators,
including a drifting first secant. Only their actual differences enter.
Source: true inverse-root congruence, finite telescoping and the already
proved native canonical coefficient theorem.
-/

namespace krylov.Functions
noncomputable section
open Matrix Finset krylov.Reference krylov.Methods krylov.Stability krylov.Correction
  krylov.Envelope krylov.Secant krylov.Variation krylov.Nonlinear
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n k : ℕ}

/-- The actual inverse-root canonical matrix reconstructs its original physical operator exactly.
Article: main_krylov, thm:Htransfer, genuine metric transport.
Proof: the proved primal/dual inner-product pairing characterizes the true operator. -/
theorem physicalCanonicalMatrix_reconstruct (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    cgOperator (metricRoot base * physicalCanonicalMatrix base hb W * metricRoot base) = W := by
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_left ℝ
  intro u
  exact (metric_drift_pairing base (physicalCanonicalMatrix base hb W) u v).trans
    (physicalCanonicalMatrix_pairing base hb W u v)

/-- Genuine consecutive canonical differences reconstruct the actual segment path up to its common first-secant drift.
Article: main_krylov, thm:Htransfer.
Proof: true canonical linearity telescopes the finite sum, and the genuine root congruence reconstructs the physical difference. -/
theorem canonical_path_of_physical_differences (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (A : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (i : ℕ) :
    canonicalFCPath base (fun l => physicalCanonicalMatrix base hb (A (l+1)-A l)) 1 i =
      cgOperator base + (A i - A 0) := by
  have ht : (∑ l ∈ range i, physicalCanonicalMatrix base hb (A (l+1)-A l)) =
      physicalCanonicalMatrix base hb (A i - A 0) := by
    simp only [physicalCanonicalMatrix_sub]
    exact sum_range_sub (fun l => physicalCanonicalMatrix base hb (A l)) i
  simp only [canonicalFCPath, one_smul, cumulativeDrift, ht]
  rw [show Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
    (metricRoot base * physicalCanonicalMatrix base hb (A i-A 0) * metricRoot base) = A i-A 0 from
      physicalCanonicalMatrix_reconstruct base hb _]

/-- The actual physical correction operator has exactly the same common drift as its reconstructed search path.
Article: main_krylov, thm:Htransfer.
Proof: reconstruct its genuine measured correction difference after the telescoped segment path. -/
theorem canonical_correction_of_physical_differences (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (A B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (i : ℕ) :
    canonicalCorrectionOperator base (fun l => physicalCanonicalMatrix base hb (A (l+1)-A l))
      (physicalCanonicalMatrix base hb (B i-A i)) i = cgOperator base + (B i-A 0) := by
  rw [canonicalCorrectionOperator, canonical_path_of_physical_differences,
    physicalCanonicalMatrix_reconstruct]
  abel

/-- The actual physical quadratic RFC coefficient is exactly the canonical staircase/fresh-defect response for its true differences.
Article: main_krylov, thm:Htransfer, the complete second-order coefficient dictionary.
Proof: reconstruct canonical queries from the actual physical differences.
They differ from the true queries by one common operator, which cancels
exactly in the genuine quadratic coefficient. Apply the proved native
canonical coefficient identity to these real reconstructed queries. -/
theorem rfcPhysicalQuadratic_eq_canonical
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (k+1))) (hN : k+1 ≤ referenceAtomCount base hb g)
    (A B : ℕ → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1))) :
    cgOperator (metricRoot base)⁻¹ (rfcPhysicalQuadratic base g A B) =
      ‖canonicalCGStep base g k‖ • staircaseOperator base g
        (fun l => physicalCanonicalMatrix base hb (A (l+1)-A l))
        (physicalCanonicalMatrix base hb (B k-A k)) (k+1)
        (freshDefect base g (fun l => physicalCanonicalMatrix base hb (A (l+1)-A l)) (k+1)) := by
  let E := fun l => physicalCanonicalMatrix base hb (A (l+1)-A l)
  let F := fun i => physicalCanonicalMatrix base hb (B i-A i)
  let C := cgOperator base - A 0
  have hA (i : ℕ) : canonicalFCPath base E 1 i = A i + C := by
    rw [canonical_path_of_physical_differences]
    dsimp only [C]
    abel
  have hB (i : ℕ) : canonicalCorrectionOperator base E (F i) i = B i + C := by
    rw [canonical_correction_of_physical_differences]
    dsimp only [C]
    abel
  have hc := native_coefficient_canonical base hb g hN E (F k)
  have hsame : rfcPhysicalQuadratic base g A B =
      rfcPhysicalQuadratic base g (canonicalFCPath base E 1)
        (fun i => canonicalCorrectionOperator base E (F i) i) := by
    have hAe : canonicalFCPath base E 1 = fun i => A i + C := funext hA
    have hBe : (fun i => canonicalCorrectionOperator base E (F i) i) = fun i => B i + C := funext hB
    rw [hAe, hBe]
    exact (rfcPhysicalQuadratic_common_shift base g A B C).symm
  rw [hsame]
  simpa only [rfcPhysicalQuadratic, quadratic_imageBasis, cgOperator, referenceModelBasis, E, F] using hc

end
end krylov.Functions
