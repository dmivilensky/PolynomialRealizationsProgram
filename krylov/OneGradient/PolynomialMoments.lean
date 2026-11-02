import krylov.Reference.CompactMeasureIntegral
import jacobi.Finite.Multiplication
set_option autoImplicit false
/-!
Article: main_krylov, s5:moment(b), polynomial integral determined by finite moments.
Use: carry the actual moment constraints on an arbitrary compactly supported
probability measure to every original low-degree polynomial identity.
Source: the finite monomial expansion of a polynomial and the reused genuine
compact-measure polynomial integral; the comparison is proved for linear functionals.
-/

namespace krylov.OneGradient
noncomputable section
open Polynomial Matrix jacobi.Finite
open scoped BigOperators InnerProductSpace

/-- The actual finite spectral probability measure's polynomial integral as a
linear functional on genuine polynomials.
Use: compare original spectral moments with arbitrary supported probability measures.
Article: main_krylov, s5:moment(b).
Proof: finite weighted evaluation preserves polynomial addition and scalar multiplication. -/
def discretePolynomialIntegral {N : ℕ} (M : DiscreteMeasure N) : ℝ[X] →ₗ[ℝ] ℝ where
  toFun p := ∑ i,M.weight i*p.eval (M.node i)
  map_add' p q := by simp only [eval_add,mul_add,Finset.sum_add_distrib]
  map_smul' c p := by
    simp only [eval_smul,smul_eq_mul,RingHom.id_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- The finite spectral polynomial integral is exactly its genuine weighted
polynomial L2 inner product.
Use: transport the existing actual orthogonal polynomial Gram identities.
Article: main_krylov, s5:moment(b).
Proof: the reused actual weighted-evaluation inner product is the same finite sum. -/
theorem discrete_integral_product {N : ℕ} (M : DiscreteMeasure N) (p q : ℝ[X]) :
    discretePolynomialIntegral M (p*q)=inner ℝ (M.evaluate p) (M.evaluate q) := by
  rw [M.inner_evaluate]
  simp only [discretePolynomialIntegral,LinearMap.coe_mk,AddHom.coe_mk,eval_mul,mul_assoc]

/-- Genuine linear polynomial integrals with the same first D moments agree
on every polynomial of degree at most D.
Use: the all-probability-measure moment problem requires no assumed equality
of orthogonal-polynomial integrals or Jacobi entries.
Article: main_krylov, s5:moment(b).
Proof: expand the actual polynomial into its finitely supported monomials;
each exponent lies below its actual degree and scalar linearity transfers its known moment. -/
theorem polynomial_integrals_eq_of_moments (F G : ℝ[X] →ₗ[ℝ] ℝ) (D : ℕ)
    (hm : ∀ k≤D,F (X^k)=G (X^k)) (p : ℝ[X]) (hp : p.natDegree≤D) : F p=G p := by
  have hs : p=∑ k∈p.support,p.coeff k • (X^k : ℝ[X]) := by
    simpa only [Polynomial.sum_def,← smul_X_eq_monomial] using (Polynomial.sum_monomial_eq p).symm
  rw [hs,map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [map_smul,map_smul,hm k ((Polynomial.le_natDegree_of_mem_supp k hk).trans hp)]

/-- The genuine polynomial multiplication form of a supplied actual polynomial integral.
Use: compress multiplication by the spectral coordinate for an arbitrary
probability measure with the original observed moments.
Article: main_krylov, s5:moment(b).
Proof: evaluate the true functional on each actual pair of polynomial basis vectors. -/
def polynomialForm {N : ℕ} (F : ℝ[X] →ₗ[ℝ] ℝ) (q : Fin N → ℝ[X]) (R : ℝ[X]) :
    Matrix (Fin N) (Fin N) ℝ := fun i j => F (R*q i*q j)

/-- The actual multiplication form's quadratic contraction equals its true
polynomial square integral.
Use: actual support positivity implies the real compressed spectral inequalities.
Article: main_krylov, s5:moment(b).
Proof: distribute the two genuine finite polynomial combinations and use
linearity of the actual polynomial integral on each scalar summand. -/
theorem polynomial_form_quadratic {N : ℕ} (F : ℝ[X] →ₗ[ℝ] ℝ)
    (q : Fin N → ℝ[X]) (R : ℝ[X]) (v : Fin N → ℝ) :
    v ⬝ᵥ (polynomialForm F q R*ᵥ v)=F (R*(∑ i,v i • q i)^2) := by
  rw [pow_two]
  simp only [polynomialForm,dotProduct,Matrix.mulVec,Finset.mul_sum,Finset.sum_mul,
    mul_smul_comm,smul_mul_assoc,map_sum,map_smul,smul_eq_mul,mul_assoc]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm (q j) (q i)]
  ring

/-- Every genuine nonnegative polynomial-square functional gives an actual
positive semidefinite compressed multiplication form.
Use: supported arbitrary probability measures supply the two true endpoint localizing forms.
Article: main_krylov, s5:moment(b).
Proof: commutativity gives real symmetry, and the true quadratic contraction
is exactly the assumed nonnegative integral of an actual polynomial square. -/
theorem polynomial_form_positive {N : ℕ} (F : ℝ[X] →ₗ[ℝ] ℝ)
    (q : Fin N → ℝ[X]) (R : ℝ[X]) (hR : ∀ p : ℝ[X],0≤F (R*p^2)) :
    (polynomialForm F q R).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.isHermitian_iff_isSymm.mpr
    ext i j
    change F (R*q j*q i)=F (R*q i*q j)
    congr 1
    ring
  · intro v
    simpa only [star_trivial,polynomial_form_quadratic] using hR (∑ i,v i • q i)

/-- Subtracting real spectral polynomials subtracts their actual multiplication forms.
Use: identify both genuine shifted spectral matrices with their localizing-square forms.
Article: main_krylov, s5:moment(b).
Proof: distribute the real polynomial products and the actual linear integral. -/
theorem polynomial_form_sub {N : ℕ} (F : ℝ[X] →ₗ[ℝ] ℝ)
    (q : Fin N → ℝ[X]) (R S : ℝ[X]) :
    polynomialForm F q (R-S)=polynomialForm F q R-polynomialForm F q S := by
  ext i j
  simp only [polynomialForm,sub_mul,map_sub,Matrix.sub_apply]

/-- A constant spectral polynomial scales the true polynomial Gram form.
Use: known finite moments identify the actual basis Gram with the identity.
Article: main_krylov, s5:moment(b).
Proof: the true constant polynomial action is scalar multiplication, preserved
by the actual linear functional. -/
theorem polynomial_form_constant {N : ℕ} (F : ℝ[X] →ₗ[ℝ] ℝ)
    (q : Fin N → ℝ[X]) (c : ℝ) :
    polynomialForm F q (C c)=c • polynomialForm F q 1 := by
  ext i j
  simp only [polynomialForm,Polynomial.C_mul',smul_mul_assoc,map_smul,one_mul,Matrix.smul_apply]

end
end krylov.OneGradient
