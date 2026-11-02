import krylov.Realization.AffineUnrolling
import krylov.Realization.InsertionPolynomials
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
Article: main_krylov, s6:kernel and prop:dict(i), physical polynomial memory action.
Use: lift actual polynomial memory matrices to arbitrary real physical vector
spaces, keeping the true independent injections and real query operator.
Source: algebra-homomorphic polynomial evaluation and the already proved
chronological ordered-product convention; no spectral basis is assumed.
-/

namespace krylov.Realization
noncomputable section
open Matrix Polynomial chebyshev1
open scoped BigOperators
variable {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι] [DecidableEq ι]

/-- The actual linear action of a polynomial memory matrix on physical vector-valued memory.
Use: evaluate the same fixed scalar coefficients at the actual physical query operator.
Article: main_krylov, s6:kernel, physical affine realization. -/
def polynomialMemoryMap (Q : E →ₗ[ℝ] E) (M : Matrix ι ι ℝ[X]) : (ι → E) →ₗ[ℝ] (ι → E) where
  toFun v i := ∑ j, (aeval Q (M i j)) (v j)
  map_add' v w := by ext i; simp only [Pi.add_apply,map_add,Finset.sum_add_distrib]
  map_smul' c v := by ext i; simp only [Pi.smul_apply,map_smul,Finset.smul_sum,RingHom.id_apply]

omit [DecidableEq ι] in
/-- Polynomial memory action preserves products as composition of the genuine physical linear actions.
Use: all true physical prefix and tail transfers are evaluations of the existing scalar polynomial matrices.
Article: main_krylov, s6:kernel and prop:dict(i).
Proof: polynomial evaluation preserves products and sums; expand the two
finite memory contractions and interchange their real finite summations. -/
theorem polynomialMemoryMap_mul (Q : E →ₗ[ℝ] E) (M N : Matrix ι ι ℝ[X]) :
    polynomialMemoryMap Q (M*N)=polynomialMemoryMap Q M*polynomialMemoryMap Q N := by
  -- The same real physical Q is used at both factors, so polynomial multiplication is genuine composition.
  apply LinearMap.ext
  intro v
  funext i
  change (∑ j, (aeval Q ((M*N) i j)) (v j))=
    ∑ j, (aeval Q (M i j)) (∑ k, (aeval Q (N j k)) (v k))
  simp only [Matrix.mul_apply,map_sum,map_mul,LinearMap.sum_apply,Module.End.mul_apply]
  rw [Finset.sum_comm]

/-- The empty polynomial memory transfer acts as the actual physical identity.
Use: empty prefixes and empty injection tails have their correct physical boundary values.
Article: main_krylov, s6:kernel.
Proof: the actual diagonal polynomial one evaluates to the identity and every other entry evaluates to zero. -/
theorem polynomialMemoryMap_one (Q : E →ₗ[ℝ] E) :
    polynomialMemoryMap Q (1 : Matrix ι ι ℝ[X])=1 := by
  apply LinearMap.ext
  intro v
  funext i
  change (∑ j, (aeval Q ((1 : Matrix ι ι ℝ[X]) i j)) (v j))=v i
  have he (j : ι) : (aeval Q ((1 : Matrix ι ι ℝ[X]) i j)) (v j)=if i=j then v j else 0 := by
    by_cases hij : i=j <;> simp [Matrix.one_apply,hij]
  simp only [he,Finset.sum_ite_eq,Finset.mem_univ,ite_true]

/-- Every actual chronological physical polynomial transfer equals evaluation of the existing chronological polynomial matrix product.
Use: identifies true physical prefix and tail actions at every finite memory size.
Article: main_krylov, s6:kernel and prop:dict(i).
Proof: finite induction uses the proved product and empty-transfer identities, preserving the existing ordered-product convention. -/
theorem polynomialMemoryMap_ordered (Q : E →ₗ[ℝ] E) (M : ℕ → Matrix ι ι ℝ[X]) (N : ℕ) :
    orderedProduct (fun j => polynomialMemoryMap Q (M j)) N=polynomialMemoryMap Q (orderedProduct M N) := by
  induction N with
  | zero => exact (polynomialMemoryMap_one Q).symm
  | succ N ih => rw [orderedProduct_succ,orderedProduct_succ,polynomialMemoryMap_mul,ih]

/-- The actual fixed linear readout of physical vector-valued memory.
Use: the same scalar readout returns the real physical error, independently of the unknown operator.
Article: main_krylov, s6:kernel, terminal physical error. -/
def memoryReadout (ell : ι → ℝ) : (ι → E) →ₗ[ℝ] E where
  toFun v := ∑ i, ell i • v i
  map_add' v w := by simp only [Pi.add_apply,smul_add,Finset.sum_add_distrib]
  map_smul' c v := by simp only [Pi.smul_apply,Finset.smul_sum,RingHom.id_apply,smul_comm (ell _) c]

omit [DecidableEq ι] in
/-- A physical memory transfer with actual scalar input and readout equals evaluation of its true scalar polynomial contraction.
Use: converts real unperturbed and independent-injection transfers to the printed residual and injection polynomials.
Article: main_krylov, s6:kernel and prop:dict(i).
Proof: move the real scalar input and readout through actual polynomial
operator evaluation, collect finite sums, and use the true constant-polynomial action. -/
theorem memoryReadout_polynomialMemoryMap (Q : E →ₗ[ℝ] E) (M : Matrix ι ι ℝ[X])
    (ell b : ι → ℝ) (v : E) :
    memoryReadout ell (polynomialMemoryMap Q M (fun j => b j • v))=
      (aeval Q (∑ i, ∑ j, C (ell i)*M i j*C (b j))) v := by
  -- Both contractions use the actual physical vector v; no eigenvector restriction is imposed.
  simp only [memoryReadout,polynomialMemoryMap,LinearMap.coe_mk,AddHom.coe_mk,
    map_sum,map_mul,aeval_C,LinearMap.sum_apply,Module.End.mul_apply,
    Algebra.algebraMap_eq_smul_one,LinearMap.smul_apply,Module.End.one_apply,map_smul,Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => smul_comm _ _ _

end
end krylov.Realization
