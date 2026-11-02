import krylov.Envelope.CanonicalInjections
import Mathlib.Algebra.BigOperators.Intervals

set_option autoImplicit false
/-!
Article: main_krylov, thm:E and s3:def:phi, genuine canonical increment envelope formula.
Use: identify the actual common frozen response with the printed finite
double sum of real canonical increments propagated by the genuine measured
CG continuation polynomials, including empty and exhausted prefixes.
Source: actual physical frozen impulse propagation, true inverse-root
polynomial commutation, genuine canonical source injections and finite
triangular summation on the actual reference horizon.
-/

namespace krylov.Envelope
noncomputable section
open Matrix Polynomial Finset krylov.Reference krylov.Secant krylov.Variation
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The genuine measured-CG polynomial action propagating the true step-i gradient injection to the actual horizon.
Use: The genuine measured-CG polynomial action propagating the true step-i gradient injection to the actual horizon.
Article: main_krylov, thm:E and s3:def:phi, genuine canonical increment envelope formula.
Proof: Evaluate the actual continuation polynomial at the true physical reference operator with its genuine chronological offset. -/
def referenceContinuation (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (N i : ℕ) : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  aeval (cgOperator base).toLinearMap
    (phi (CG.length (cgOperator base) g) (CG.beta (cgOperator base) g) (i+1) (N-(i+1)))

/-- The true canonical source increment double sum with actual CG step energies and genuine measured continuation actions.
Use: The true canonical source increment double sum with actual CG step energies and genuine measured continuation actions.
Article: main_krylov, thm:E and s3:def:phi, genuine canonical increment envelope formula.
Proof: Sum every real earlier increment acting on the actual later normalized CG step, with its genuine square-root energy scale. -/
def canonicalInjectionResponse (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (N : ℕ) : EuclideanSpace ℝ (Fin n) :=
  ∑ l∈range (N-1), ∑ i∈Ico (l+1) N,
    Real.sqrt (cgEnergy base g i) • referenceContinuation base g N i
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (E l) (canonicalCGUnitStep base g i))

/-- The genuine canonical frozen response on the actual source path is the true sum of propagated cumulative canonical increments acting on real computed CG steps.
Use: The genuine canonical frozen response on the actual source path is the true sum of propagated cumulative canonical increments acting on real computed CG steps.
Article: main_krylov, thm:E and s3:def:phi, genuine canonical increment envelope formula.
Proof: Unroll the actual physical frozen executor, commute its true polynomial actions through the genuine inverse metric root and identify each real canonical reference-step injection. -/
theorem canonicalFrozenResponse_formula (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (N : ℕ) :
    canonicalFrozenResponse base g (canonicalFCPath base E) N=
      ∑ i∈range N, referenceContinuation base g N i
        (Matrix.toEuclideanCLM (𝕜 := ℝ) (∑ l∈range i, E l) (canonicalCGStep base g i)) := by
  unfold canonicalFrozenResponse
  rw [frozen_response_formula,map_sum]
  apply sum_congr rfl
  intro i _
  rw [canonical_polynomial_action base hb,referenceInjection_canonicalPath base hb]
  rfl

/-- The actual canonical frozen response is exactly the printed genuine finite canonical-increment double sum.
Use: The actual canonical frozen response is exactly the printed genuine finite canonical-increment double sum.
Article: main_krylov, thm:E and s3:def:phi, genuine canonical increment envelope formula.
Proof: Expand the true cumulative increment action, interchange the genuine finite triangular sums and remove only the actual empty last tail. True zero-safe step normalization and genuine CG energy identify each real square-root energy factor. -/
theorem canonicalFrozenResponse_increment_sum (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (N : ℕ) :
    canonicalFrozenResponse base g (canonicalFCPath base E) N=canonicalInjectionResponse base g E N := by
  -- Every genuine term uses a real canonical increment and the actual later CG step at the fixed true horizon.
  let f := fun l i => referenceContinuation base g N i
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (E l) (canonicalCGStep base g i))
  have hfirst : canonicalFrozenResponse base g (canonicalFCPath base E) N=∑ i∈range N, ∑ l∈range i, f l i := by
    rw [canonicalFrozenResponse_formula base hb]
    apply sum_congr rfl
    intro i _
    simp only [map_sum,_root_.sum_apply,f]
  -- Exchange only the actual finite triangle of earlier increments and later executed reference steps.
  have hswap : (∑ i∈range N, ∑ l∈range i, f l i)=∑ l∈range N, ∑ i∈Ico (l+1) N, f l i := by
    simpa only [Nat.Ico_zero_eq_range] using (sum_Ico_Ico_comm' 0 N f).symm
  -- The sole omitted last increment has an actual empty later-step tail, including the zero and one-step cases.
  have htrim : (∑ l∈range N, ∑ i∈Ico (l+1) N, f l i)=∑ l∈range (N-1), ∑ i∈Ico (l+1) N, f l i := by
    symm
    apply sum_subset (range_mono (Nat.sub_le N 1))
    intro l hl hnot
    have he : l+1=N := by have := mem_range.mp hl;simp only [mem_range] at hnot;omega
    simp only [he,Ico_self,sum_empty]
  rw [hfirst,hswap,htrim]
  unfold canonicalInjectionResponse
  apply sum_congr rfl
  intro l _
  apply sum_congr rfl
  intro i _
  -- Use the true zero-safe normalized CG step and its actual physical energy, with no extra nonzero-step premise.
  have hs : canonicalCGStep base g i=‖canonicalCGStep base g i‖ • canonicalCGUnitStep base g i :=
    (NormedSpace.norm_smul_normalize _).symm
  dsimp only [f]
  rw [hs,map_smul,map_smul,cgEnergy_sqrt base hb]

/-- The true method-independent unexplored response is exactly the genuine orthogonal complement of the printed actual canonical increment double sum.
Use: The true method-independent unexplored response is exactly the genuine orthogonal complement of the printed actual canonical increment double sum.
Article: main_krylov, thm:E and s3:def:phi, genuine canonical increment envelope formula.
Proof: Substitute the proved genuine source increment expansion into the actual canonical frozen response projection. -/
theorem commonTransverseResponse_increment_sum (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (N : ℕ) :
    commonTransverseResponse base g (canonicalFCPath base E) N=
      canonicalInjectionResponse base g E N-
        (exploredFlag base g N).starProjection (canonicalInjectionResponse base g E N) := by
  rw [commonTransverseResponse,canonicalFrozenResponse_increment_sum base hb]
end
end krylov.Envelope
