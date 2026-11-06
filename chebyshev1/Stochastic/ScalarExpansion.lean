import chebyshev1.Realization.Multilinear
import chebyshev1.Realization.Polynomial

/-!
The pathwise square-free expansion for independent scalar Hessian noise.
Independence is unnecessary for this algebraic identity: it is used only when
taking moments, so no higher random moments occur in its coefficients.
-/
namespace chebyshev1
noncomputable section
open scoped BigOperators

namespace Stochastic

variable {A : Type*} [Ring A] [Algebra ℝ A]

theorem insertionTerm_coordinate_smul (C D : ℕ → A) (n : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.range n) (z : ℕ → ℝ) :
    insertionTerm C (fun s => z s • D s) n S =
      (∏ s ∈ S, z s) • insertionTerm C D n S := by
  rw [← insertionMultilinear_apply (K := ℝ) C (fun s => z s • D s) n S hS,
    ← insertionMultilinear_apply (K := ℝ) C D n S hS]
  simpa only [Finset.prod_coe_sort] using (insertionMultilinear (K := ℝ) C n S hS).map_smul_univ
    (fun s => z s.val) (fun s => D s.val)

end Stochastic

namespace Realization

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]

/-- Deterministic coefficient of the square-free noise monomial indexed by `S`. -/
def scalarNoiseCoefficient (R : Realization ι) (n : ℕ) (H : Matrix d d ℝ)
    (B : ℕ → Matrix d d ℝ) (S : Finset ℕ) : Matrix d d ℝ :=
  R.contract (insertionTerm (fun s => R.operatorStep s H)
    (fun s => R.operatorInsertion s (B s)) n S)

/-- Every noise time appears at most once, including when the matrices do not commute. -/
theorem scalarNoise_expansion (R : Realization ι) (n : ℕ) (H : Matrix d d ℝ)
    (B : ℕ → Matrix d d ℝ) (z : ℕ → ℝ) (σ : ℝ) :
    R.operatorTransfer n (fun s => H + (σ * z s) • B s) =
      ∑ S ∈ (Finset.range n).powerset,
        (σ ^ S.card * ∏ s ∈ S, z s) • R.scalarNoiseCoefficient n H B S := by
  unfold operatorTransfer
  simp_rw [operatorStep_add, operatorInsertion_smul]
  rw [orderedProduct_add_expansion]
  change R.contractLinear _ = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro S hS
  rw [Stochastic.insertionTerm_coordinate_smul _ _ n S (Finset.mem_powerset.mp hS)]
  simp [Finset.prod_mul_distrib, scalarNoiseCoefficient, contractLinear_apply]

@[simp] theorem scalarNoiseCoefficient_empty (R : Realization ι) (n : ℕ)
    (H : Matrix d d ℝ) (B : ℕ → Matrix d d ℝ) :
    R.scalarNoiseCoefficient n H B ∅ =
      Polynomial.aeval H (R.residualPolynomial n) := by
  simpa [scalarNoiseCoefficient, operatorTransfer] using
    (R.operatorTransfer_eq_aeval n H)

/-- A singleton coefficient is the causally ordered first-variation insertion. -/
theorem scalarNoiseCoefficient_singleton (R : Realization ι) {n s : ℕ} (hs : s < n)
    (H : Matrix d d ℝ) (B : ℕ → Matrix d d ℝ) :
    R.scalarNoiseCoefficient n H B {s} = R.contract
      (orderedProduct (fun i => R.operatorStep (s+1+i) H) (n-(s+1)) *
        R.operatorInsertion s (B s) * orderedProduct (fun i => R.operatorStep i H) s) := by
  rw [scalarNoiseCoefficient, insertionTerm_singleton _ _ hs]

end Realization
end
end chebyshev1
