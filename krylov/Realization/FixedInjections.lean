import krylov.Realization.PolynomialMemory

/-!
Article: main_krylov, s6:kernel and prop:dict(i), genuine physical independent injections.
Use: prove the exact printed polynomial error formula for the actual fixed
finite-memory recurrence with arbitrary real physical query injections.
Source: the proved real affine unrolling and algebraic polynomial memory
representation of the existing PasechnyukTakac26 realization data.
-/

namespace krylov.Realization
noncomputable section
open Matrix Polynomial chebyshev1
open scoped BigOperators
variable {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The real polynomial memory step is exactly the original fixed scalar memory update with one genuine physical query.
Use: validates that the polynomial-memory executor really implements the source's fixed affine oracle recursion.
Article: main_krylov, s6:kernel and def:classes(O).
Proof: evaluate each actual affine polynomial entry at Q, commute the fixed
scalar query coefficients through Q and collect the finite physical sums. -/
theorem polynomialMemoryMap_step (R : chebyshev1.Realization ι) (Q : E →ₗ[ℝ] E)
    (s : ℕ) (v : ι → E) (i : ι) :
    polynomialMemoryMap Q (R.polynomialStep s) v i=
      (∑ j, R.P s i j • v j)-R.g s i • Q (∑ j, R.q s j • v j) := by
  change (∑ j, (aeval Q (C (R.P s i j)-X*C (R.g s i*R.q s j))) (v j))=_
  simp only [map_sub,map_mul,aeval_C,aeval_X,LinearMap.sub_apply,Module.End.mul_apply,
    Algebra.algebraMap_eq_smul_one,LinearMap.smul_apply,Module.End.one_apply,
    Finset.sum_sub_distrib,map_sum,map_smul,Finset.smul_sum,smul_smul]
  simp only [mul_comm]

/-- Execute the true fixed finite-memory recursion with each actual additive physical oracle injection.
Use: the query is Qe+ι, and its negative fixed memory input is the real gradient-query insertion.
Article: main_krylov, s6:kernel, g_s=Ae_s+ι_s. -/
def injectedFixedRun (R : chebyshev1.Realization ι) (Q : E →ₗ[ℝ] E)
    (input : ℕ → E) (initial : E) : ℕ → ι → E :=
  affineRun (fun s => polynomialMemoryMap Q (R.polynomialStep s))
    (fun s i => -(R.g s i) • input s) (fun i => R.b i • initial)

omit [DecidableEq ι] in
/-- Each actual fixed-memory update queries Q at its true current memory combination and adds its genuine independent oracle injection.
Use: the exact unrolling theorem concerns the prescribed real oracle g_s=Qe_s+ι_s.
Article: main_krylov, s6:kernel.
Proof: expand one real affine update, use its proved actual query formula,
and collect the two physical terms with the same fixed input coefficient. -/
theorem injectedFixedRun_succ (R : chebyshev1.Realization ι) (Q : E →ₗ[ℝ] E)
    (input : ℕ → E) (initial : E) (s : ℕ) (i : ι) :
    let v := injectedFixedRun R Q input initial s
    injectedFixedRun R Q input initial (s+1) i=
      (∑ j, R.P s i j • v j)-R.g s i • (Q (∑ j, R.q s j • v j)+input s) := by
  let v := injectedFixedRun R Q input initial s
  change polynomialMemoryMap Q (R.polynomialStep s) v i+ -(R.g s i) • input s=
    (∑ j, R.P s i j • v j)-R.g s i • (Q (∑ j, R.q s j • v j)+input s)
  rw [polynomialMemoryMap_step,smul_add,neg_smul]
  abel

/-- The real physical fixed-memory run obeys the exact residual-plus-independent-injection polynomial formula.
Use: unrolling concerns actual injections in arbitrary physical spaces and arbitrary fixed memory, rather than a formal first-order expansion.
Article: main_krylov, s6:kernel and prop:dict(i), e_N=p_R(A)e₀+ΣR_s(A)ι_s.
Proof: apply real finite affine variation of constants to the actual memory
recursion. The real polynomial action identifies every prefix and tail;
actual scalar input/readout contractions are exactly the constructed residual
and independent-injection polynomials, with their genuine negative query sign. -/
theorem injectedFixedRun_formula (R : chebyshev1.Realization ι) (Q : E →ₗ[ℝ] E)
    (input : ℕ → E) (initial : E) (N : ℕ) :
    memoryReadout R.readout (injectedFixedRun R Q input initial N)=
      (aeval Q (R.residualPolynomial N)) initial+
        ∑ s∈Finset.range N, (aeval Q (injectionPolynomial R N s)) (input s) := by
  -- Each actual injection keeps its own actual remaining transfer; the polynomial identification is applied afterwards.
  rw [injectedFixedRun,affineRun_readout]
  simp only [polynomialMemoryMap_ordered]
  rw [memoryReadout_polynomialMemoryMap]
  change (aeval Q (R.residualPolynomial N)) initial+_=_
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  have hn : (fun i => -(R.g s i) • input s)= -(fun i => R.g s i • input s) := by
    ext i
    exact neg_smul _ _
  have hp : injectionPolynomial R N s= -(∑ i, ∑ j, C (R.readout i)*
      orderedProduct (fun t => R.polynomialStep (s+1+t)) (N-(s+1)) i j*C (R.g s j)) := by
    simp only [injectionPolynomial,dotProduct,Matrix.mulVec,Finset.mul_sum,mul_assoc]
  rw [hn,map_neg,map_neg,memoryReadout_polynomialMemoryMap,hp,map_neg,LinearMap.neg_apply]

end
end krylov.Realization
