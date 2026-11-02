import krylov.Envelope.CanonicalResponseFormula
import krylov.LinearAlgebra.FrobeniusSupport

set_option autoImplicit false
/-!
Article: main_krylov, thm:E, genuine common norm-variation trace coefficients.
Use: construct the printed real symmetric outer-product matrices Z_l from
actual measured CG continuations and identify their genuine Frobenius
pairing with the true common unexplored first variation.
Source: standard polynomial calculus of actual symmetric operators, the
proved real symmetric perturbation Frobenius pairing and true CG
explored-flag orthogonality; no norm variation is assumed.
-/

namespace krylov.Envelope
noncomputable section
open Matrix Polynomial Finset krylov.Reference krylov.Secant krylov.Variation krylov.LinearAlgebra
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

/-- Every genuine real polynomial of a true symmetric linear reference operator is actually symmetric.
Use: Every genuine real polynomial of a true symmetric linear reference operator is actually symmetric.
Article: main_krylov, thm:E, genuine common norm-variation trace coefficients.
Proof: Expand the true polynomial into its genuine finite power sum and use standard real symmetric operator power and scalar-sum closure. -/
theorem polynomial_action_symmetric (Q : E →ₗ[ℝ] E) (hQ : Q.IsSymmetric) (p : ℝ[X]) :
    (aeval Q p).IsSymmetric := by
  rw [Polynomial.aeval_eq_sum_range]
  exact LinearMap.isSymmetric_sum _ (fun i _ => LinearMap.IsSymmetric.smul (by rfl) (hQ.pow i))

/-- The genuine Euclidean action of a real symmetric perturbation has exactly the true symmetric outer-product Frobenius pairing.
Use: The genuine Euclidean action of a real symmetric perturbation has exactly the true symmetric outer-product Frobenius pairing.
Article: main_krylov, thm:E, genuine common norm-variation trace coefficients.
Proof: Transfer actual Euclidean coordinates through the real matrix action and reuse the proved genuine symmetric perturbation pairing. -/
theorem symmetric_action_frobenius_euclidean (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm)
    (u v : EuclideanSpace ℝ (Fin n)) :
    inner ℝ u (Matrix.toEuclideanCLM (𝕜 := ℝ) M v)=
      inner ℝ (frobeniusVector M) (frobeniusVector (symmetricOuter (WithLp.ofLp u) (WithLp.ofLp v))) := by
  rw [Matrix.inner_toEuclideanCLM]
  simpa only [star_trivial] using symmetric_action_frobenius M hM (WithLp.ofLp u) (WithLp.ofLp v)

/-- Actual Frobenius entry flattening preserves every true finite matrix sum.
Use: Actual Frobenius entry flattening preserves every true finite matrix sum.
Article: main_krylov, thm:E, genuine common norm-variation trace coefficients.
Proof: Package the proved genuine additive entry flattening as an actual additive map and apply the standard finite sum identity. -/
theorem frobeniusVector_sum {ι : Type*} (s : Finset ι) (Z : ι → Matrix (Fin n) (Fin n) ℝ) :
    frobeniusVector (∑ i∈s, Z i)=∑ i∈s, frobeniusVector (Z i) := by
  let f : Matrix (Fin n) (Fin n) ℝ →+ EuclideanSpace ℝ (Fin n × Fin n) := {
    toFun := frobeniusVector
    map_zero' := by ext ij;rfl
    map_add' := frobeniusVector_add }
  exact map_sum f Z s

/-- The genuine source norm-trace matrix built from actual continuation actions, true reference error and real normalized CG steps.
Use: The genuine source norm-trace matrix built from actual continuation actions, true reference error and real normalized CG steps.
Article: main_krylov, thm:E, genuine common norm-variation trace coefficients.
Proof: Sum the true energy-scaled symmetric outer products over precisely the genuine later reference-step indices. -/
def normTraceCoefficient (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (N l : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  ∑ i∈Ico (l+1) N, Real.sqrt (cgEnergy base g i) •
    symmetricOuter (WithLp.ofLp (referenceContinuation base g N i (cgCanonicalError base g N)))
      (WithLp.ofLp (canonicalCGUnitStep base g i))

/-- The genuine reference-error pairing with the actual canonical injection response equals the printed true sum of perturbation pairings with the real norm-trace coefficient matrices.
Use: The genuine reference-error pairing with the actual canonical injection response equals the printed true sum of perturbation pairings with the real norm-trace coefficient matrices.
Article: main_krylov, thm:E, genuine common norm-variation trace coefficients.
Proof: Expand the actual finite response and true Frobenius sum. Genuine polynomial symmetry transfers each real continuation action to the true reference error; the proved symmetric outer-product action identity identifies every actual increment pairing. -/
theorem canonicalInjectionResponse_norm_trace (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (N : ℕ)
    (hE : ∀ l<N-1, (E l).IsSymm) :
    inner ℝ (cgCanonicalError base g N) (canonicalInjectionResponse base g E N)=
      ∑ l∈range (N-1), inner ℝ (frobeniusVector (E l)) (frobeniusVector (normTraceCoefficient base g N l)) := by
  -- Expand only actual finite source increments and true later CG steps before identifying each real symmetric action functional.
  unfold canonicalInjectionResponse
  rw [inner_sum]
  apply sum_congr rfl
  intro l hl
  rw [normTraceCoefficient,frobeniusVector_sum]
  simp only [inner_sum]
  apply sum_congr rfl
  intro i _
  rw [real_inner_smul_right,frobeniusVector_smul,real_inner_smul_right]
  congr 1
  -- Genuine measured continuation polynomials are symmetric functions of the actual positive reference operator.
  have hs := polynomial_action_symmetric (cgOperator base).toLinearMap (cgOperator_positive base hb).1
    (phi (CG.length (cgOperator base) g) (CG.beta (cgOperator base) g) (i+1) (N-(i+1)))
  change (referenceContinuation base g N i).IsSymmetric at hs
  change inner ℝ (cgCanonicalError base g N) (referenceContinuation base g N i _)=_
  rw [← hs]
  exact symmetric_action_frobenius_euclidean (E l) (hE l (mem_range.mp hl)) _ _

/-- The real common unexplored first variation has exactly the genuine printed norm-trace pairing with the actual reference error.
Use: The real common unexplored first variation has exactly the genuine printed norm-trace pairing with the actual reference error.
Article: main_krylov, thm:E, genuine common norm-variation trace coefficients.
Proof: True CG explored-flag orthogonality annihilates the actual projected response; apply the proved genuine canonical increment trace identity to the remaining real response. -/
theorem commonTransverseResponse_norm_trace (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (N : ℕ)
    (hN : N≤referenceAtomCount base hb g) (hE : ∀ l<N-1, (E l).IsSymm) :
    inner ℝ (cgCanonicalError base g N) (commonTransverseResponse base g (canonicalFCPath base E) N)=
      ∑ l∈range (N-1), inner ℝ (frobeniusVector (E l)) (frobeniusVector (normTraceCoefficient base g N l)) := by
  rw [commonTransverseResponse_increment_sum base hb,inner_sub_right]
  have ho : inner ℝ (cgCanonicalError base g N)
      ((exploredFlag base g N).starProjection (canonicalInjectionResponse base g E N))=0 := by
    rw [real_inner_comm]
    exact exploredFlag_error_orthogonal base hb g hN _ ((exploredFlag base g N).starProjection_apply_mem _)
  rw [ho,sub_zero]
  exact canonicalInjectionResponse_norm_trace base hb g E N hE
end
end krylov.Envelope
