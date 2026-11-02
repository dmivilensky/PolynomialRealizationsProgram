import krylov.Envelope.DaleckiiKreinMatrix
import krylov.Envelope.ProjectionMatrices
import krylov.Envelope.AbsorbedPolynomialPairing
import krylov.Envelope.TiltAbsorption

set_option autoImplicit false
/-!
Article: main_krylov, thm:select and apB:lem:DK, genuine actual common-tilt Daleckii--Krein formula.
Use: identify the actual method-independent common tilt functional for
every true symmetric canonical scenario with the printed genuine
complementary-flag compressed polynomial sensitivity matrices.
Source: DaleckiiKrein65 for attribution; actual positive quadratic
shadow differentiation, true absorbed invariance and real metric/trace identities.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Stability krylov.Variation krylov.LinearAlgebra Polynomial Matrix Finset
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- On genuine absorbed symmetric canonical scenarios the actual common-tilt polynomial functional equals the true sum of real increment Frobenius pairings with the printed Daleckii--Krein matrix.
Use: On genuine absorbed symmetric canonical scenarios the actual common-tilt polynomial functional equals the true sum of real increment Frobenius pairings with the printed Daleckii--Krein matrix.
Article: main_krylov, thm:select and apB:lem:DK, genuine actual common-tilt Daleckii--Krein formula.
Proof: The actual positive quadratic information fibre gives the genuine ordered polynomial sensitivity. Factor the true physical increment sum through its real reference roots, apply the actual power-insertion Frobenius coefficient theorem and sum the genuine source increments. -/
theorem absorbed_tilt_daleckiiKrein_pairing (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (hE : ∀ l<N-1, (E l).IsSymm) (habs : AbsorbedIncrements base g E N)
    (p : ℝ[X]) (hdegree : p.natDegree<N) :
    inner ℝ (canonicalPolynomialVector base g p) (commonTilt base g (canonicalFCPath base E) N)=
      ∑ l∈range (N-1), inner ℝ (frobeniusVector (E l)) (frobeniusVector (daleckiiKreinMatrix base g N p)) := by
  -- The actual quadratic-shadow sensitivity is factored through the genuine canonical increment sum before assembling its true Frobenius functional.
  rw [absorbed_tilt_polynomial_pairing base hb g N hN hcount E hE habs p hdegree]
  have hphys : (∑ l∈range (N-1),physicalIncrements base E l)=metricRoot base*(∑ l∈range (N-1),E l)*metricRoot base := by
    simp only [physicalIncrements,Matrix.mul_sum,Matrix.sum_mul]
  have hsym : (∑ l∈range (N-1),E l).IsSymm := by
    change (∑ l∈range (N-1),E l)ᵀ=∑ l∈range (N-1),E l
    rw [Matrix.transpose_sum]
    exact sum_congr rfl (fun l hl => (hE l (mem_range.mp hl)).eq)
  rw [hphys,polynomialVariation_daleckiiKrein_pairing base hb g N p _ hsym,frobeniusVector_sum,sum_inner]

/-- For every actual symmetric canonical scenario the genuine common-tilt polynomial functional equals exactly the printed true sum of original increment pairings with complementary canonical flag compressions of the real Daleckii--Krein matrix.
Use: For every actual symmetric canonical scenario the genuine common-tilt polynomial functional equals exactly the printed true sum of original increment pairings with complementary canonical flag compressions of the real Daleckii--Krein matrix.
Article: main_krylov, thm:select and apB:lem:DK, genuine actual common-tilt Daleckii--Krein formula.
Proof: The actual common tilt is invariant under genuine absorbed compression. Apply the proved true absorbed quadratic CG sensitivity formula and move the real complementary projector compression from each actual increment to its genuine polynomial target matrix by the true cyclic trace identity. -/
theorem actual_tilt_daleckiiKrein_pairing (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (hE : ∀ l<N-1, (E l).IsSymm)
    (p : ℝ[X]) (hdegree : p.natDegree<N) :
    inner ℝ (canonicalPolynomialVector base g p) (commonTilt base g (canonicalFCPath base E) N)=
      ∑ l∈range (N-1), inner ℝ (frobeniusVector (E l))
        (frobeniusVector (canonicalComplementMatrix base g l*daleckiiKreinMatrix base g N p*canonicalComplementMatrix base g l)) := by
  rw [← commonTilt_absorbedIncrements base hb g N hcount E,
    absorbed_tilt_daleckiiKrein_pairing base hb g N hN hcount (absorbedIncrements base g E)
      (fun l hl => absorbedIncrements_symm base g E l (hE l hl)) (absorbedIncrements_absorbed base g E N) p hdegree]
  exact sum_congr rfl (fun l hl => absorbedIncrements_frobenius_pairing base g E l (hE l (mem_range.mp hl)) _)
end
end krylov.Envelope
