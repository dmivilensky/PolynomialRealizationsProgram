import krylov.Envelope.DaleckiiKreinMatrix

set_option autoImplicit false
/-!
Article: main_krylov, thm:select and apB:lem:DK, literal printed polynomial sensitivity sum.
Use: identify the actual degree-bounded Daleckii--Krein matrix with
the exact source index range from one to horizon minus one.
Source: the proved actual finite power sensitivity kernel, vanishing
coefficients above the true polynomial degree and genuine zero constant-term sensitivity.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.LinearAlgebra Polynomial Matrix Finset
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The actual Daleckii--Krein matrix equals exactly the printed sum over polynomial degrees one through horizon minus one.
Use: The actual Daleckii--Krein matrix equals exactly the printed sum over polynomial degrees one through horizon minus one.
Article: main_krylov, thm:select and apB:lem:DK, literal printed polynomial sensitivity sum.
Proof: Pad the genuine polynomial coefficient sum by its actual zero high-degree terms, then remove the real zero constant-term sensitivity. -/
theorem daleckiiKreinMatrix_source_sum (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (N : ℕ) (p : ℝ[X]) (hdegree : p.natDegree<N) :
    daleckiiKreinMatrix base g N p=∑ j∈Ico 1 N, p.coeff j • ∑ r∈range j,
      symmetricOuter (WithLp.ofLp (((cgOperator base)^(r+1)) (cgCanonicalError base g N)))
        (WithLp.ofLp (((cgOperator base)^(j-r)) (cgCanonicalError base g 0))) := by
  -- Pad only by actual zero polynomial coefficients; the genuine degree-zero insertion sum is empty.
  let f := fun j => p.coeff j • ∑ r∈range j,
    symmetricOuter (WithLp.ofLp (((cgOperator base)^(r+1)) (cgCanonicalError base g N)))
      (WithLp.ofLp (((cgOperator base)^(j-r)) (cgCanonicalError base g 0)))
  have hpad : (∑ j∈range (p.natDegree+1), f j)=∑ j∈range N, f j := by
    apply sum_subset (range_mono (by omega))
    intro j _ hj
    have hz : p.coeff j=0 := coeff_eq_zero_of_natDegree_lt (by simp only [mem_range] at hj;omega)
    simp only [f,hz,zero_smul]
  change (∑ j∈range (p.natDegree+1), f j)=∑ j∈Ico 1 N, f j
  rw [hpad,sum_Ico_eq_sub f (by omega),sum_range_one]
  have hf0 : f 0=0 := by simp only [f,range_zero,sum_empty,smul_zero]
  rw [hf0,sub_zero]
end
end krylov.Envelope
