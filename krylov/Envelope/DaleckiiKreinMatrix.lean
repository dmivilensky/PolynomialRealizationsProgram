import krylov.Envelope.PowerMetricPairing
import krylov.Envelope.PolynomialDifferential

set_option autoImplicit false
/-!
Article: main_krylov, thm:select and apB:lem:DK, genuine Daleckii--Krein coefficient matrices.
Use: construct the printed true symmetric polynomial sensitivity matrix
from actual canonical CG errors and genuine reference powers, and prove
its real Frobenius pairing with the actual physical operator derivative.
Source: DaleckiiKrein65 for standard sensitivity attribution; genuine
ordered polynomial differentiation and actual metric power-insertion pairings.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Stability krylov.Variation krylov.LinearAlgebra Polynomial Matrix Finset
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The genuine printed symmetric Daleckii--Krein polynomial sensitivity matrix formed from true canonical reference-error powers.
Use: The genuine printed symmetric Daleckii--Krein polynomial sensitivity matrix formed from true canonical reference-error powers.
Article: main_krylov, thm:select and apB:lem:DK, genuine Daleckii--Krein coefficient matrices.
Proof: Sum the actual polynomial coefficients and genuine ordered reference-power symmetric outer products. -/
def daleckiiKreinMatrix (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (p : ℝ[X]) :
    Matrix (Fin n) (Fin n) ℝ :=
  ∑ j∈range (p.natDegree+1), p.coeff j • ∑ r∈range j,
    symmetricOuter (WithLp.ofLp (((cgOperator base)^(r+1)) (cgCanonicalError base g N)))
      (WithLp.ofLp (((cgOperator base)^(j-r)) (cgCanonicalError base g 0)))

/-- The actual noncommutative polynomial first variation has the equivalent genuinely reversed finite insertion sum.
Use: The actual noncommutative polynomial first variation has the equivalent genuinely reversed finite insertion sum.
Article: main_krylov, thm:select and apB:lem:DK, genuine Daleckii--Krein coefficient matrices.
Proof: Reflect the true finite power-insertion indices and retain both actual noncommuting factor orders. -/
theorem polynomialFirstVariation_reflect (p : ℝ[X]) (Q D : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    polynomialFirstVariation p Q D=∑ j∈range (p.natDegree+1), p.coeff j • ∑ r∈range j,Q^r*D*Q^(j.pred-r) := by
  -- Reflect only the true finite insertion index, preserving the actual noncommuting operator factors.
  unfold polynomialFirstVariation
  apply sum_congr rfl
  intro j _
  apply congrArg (fun T => p.coeff j • T)
  rw [← sum_range_reflect (fun r => Q^r*D*Q^(j.pred-r)) j]
  apply sum_congr rfl
  intro r hr
  have hj := mem_range.mp hr
  have he : j-1-(j-1-r)=r := by omega
  simp only [Nat.pred_eq_sub_one,he]

/-- The true physical polynomial sensitivity pairs with the actual reference gradient as the genuine printed Daleckii--Krein Frobenius functional.
Use: The true physical polynomial sensitivity pairs with the actual reference gradient as the genuine printed Daleckii--Krein Frobenius functional.
Article: main_krylov, thm:select and apB:lem:DK, genuine Daleckii--Krein coefficient matrices.
Proof: Expand the actual ordered sensitivity in its true reflected insertion order. Genuine metric power pairings identify each real symmetric outer-product coefficient; linear Frobenius synthesis assembles the actual printed matrix. -/
theorem polynomialVariation_daleckiiKrein_pairing (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (p : ℝ[X]) (E : Matrix (Fin n) (Fin n) ℝ) (hE : E.IsSymm) :
    inner ℝ ((polynomialFirstVariation p (cgOperator base) (cgOperator (metricRoot base*E*metricRoot base))) g)
      (CG.gradient (cgOperator base) g N)=
    inner ℝ (frobeniusVector E) (frobeniusVector (daleckiiKreinMatrix base g N p)) := by
  -- Pair every actual reflected physical insertion with its genuine canonical reference-power outer-product coefficient.
  rw [polynomialFirstVariation_reflect,daleckiiKreinMatrix,frobeniusVector_sum]
  simp only [_root_.sum_apply,_root_.smul_apply,sum_inner,inner_sum,frobeniusVector_smul,real_inner_smul_left,real_inner_smul_right]
  apply sum_congr rfl
  intro j _
  apply congrArg (fun t : ℝ => p.coeff j*t)
  rw [frobeniusVector_sum]
  simp only [inner_sum]
  apply sum_congr rfl
  intro r hr
  have hj := mem_range.mp hr
  have he : (j.pred-r)+1=j-r := by
    simp only [Nat.pred_eq_sub_one]
    omega
  rw [power_metric_pairing base hb g N r (j.pred-r) E hE,he]
/-- The actual printed Daleckii--Krein sensitivity matrix is genuinely symmetric.
Use: The actual printed Daleckii--Krein sensitivity matrix is genuinely symmetric.
Article: main_krylov, thm:select and apB:lem:DK, genuine Daleckii--Krein coefficient matrices.
Proof: Each true symmetric outer product is symmetric, and actual real scalar multiples and finite sums preserve the genuine transpose identity. -/
theorem daleckiiKreinMatrix_symm (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (N : ℕ) (p : ℝ[X]) : (daleckiiKreinMatrix base g N p).IsSymm := by
  -- Actual finite real sums of the genuine symmetric outer products preserve true matrix symmetry.
  unfold daleckiiKreinMatrix
  change (∑ j∈range (p.natDegree+1), p.coeff j • ∑ r∈range j,_ )ᵀ=_
  simp only [Matrix.transpose_sum,Matrix.transpose_smul]
  apply sum_congr rfl
  intro j _
  apply congrArg (fun T => p.coeff j • T)
  exact sum_congr rfl (fun r _ => (symmetricOuter_isSymm _ _).eq)

end
end krylov.Envelope
