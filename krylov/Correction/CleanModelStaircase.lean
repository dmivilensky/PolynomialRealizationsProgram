import krylov.Correction.ObliqueStaircase
import krylov.Correction.TerminalBasisAlgebra
import krylov.Correction.FullBasisAlgebra

/-!
Article: main_krylov, thm:UCq, exact actual clean-model staircase.
Use: Derive the original full model-error factor from actual chronological
column compressions and true canonical increments before bounding measured
secant contamination.
Source: the existing exact canonical flag theorem, genuine inverse congruence
cancellation and true physical column/compression identities.
-/

namespace krylov.Correction
noncomputable section
open Matrix Finset krylov.Methods krylov.Reference krylov.Secant krylov.Stability
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The genuine clean terminal model error is exactly the original oblique curvature staircase after true inverse congruence.
Use: Identify the actual uniform RFC leading curvature factor without an assumed expansion.
Article: main_krylov, thm:UCq.
Proof: Apply the existing canonical flag theorem to the actual compressed symmetric operators. Their genuine consecutive differences cancel through the proved full inverse congruence, leaving precisely the original increment matrices; the true terminal defect adds directly.
-/
theorem clean_model_inverseCongruence (T : Matrix (Fin n) (Fin n) ℝ) (hT : IsUnit T.det)
    (A E : ℕ → Matrix (Fin n) (Fin n) ℝ) (F : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ j, (A j).IsSymm) (hE : ∀ j<n, A (j+1)-A j=E j) :
    inverseCongruence T (Tᵀ*(A n+F)*T-latest (observed (fun j => Tᵀ*A j*T)))=
      obliqueStaircase T E F n := by
  let C := fun j => Tᵀ*A j*T
  have hC j : (C j).IsSymm := by
    simp only [C,Matrix.IsSymm,Matrix.transpose_mul,Matrix.transpose_transpose,(hA j).eq,Matrix.mul_assoc]
  have hflag := (canonical_flag_identities T hT C hC).1
  have hdiff j (hj : j<n) : inverseCongruence T (C (j+1)-C j)=E j := by
    dsimp only [C]
    rw [← Matrix.sub_mul,← Matrix.mul_sub,hE j hj,inverseCongruence_compressed T _ hT]
  have hsum : (∑ l ∈ range n, (transportedFlag T l)ᵀ*inverseCongruence T (C (l+1)-C l)*transportedFlag T l)=
      ∑ l ∈ range n, (transportedFlag T l)ᵀ*E l*transportedFlag T l := by
    apply sum_congr rfl
    intro l hl
    rw [hdiff l (mem_range.mp hl)]
  have hsplit : Tᵀ*(A n+F)*T-latest (observed C)=(C n-latest (observed C))+(Tᵀ*F*T) := by
    dsimp only [C]
    noncomm_ring
  rw [hsplit]
  have hlin : inverseCongruence T ((C n-latest (observed C))+(Tᵀ*F*T))=
      inverseCongruence T (C n-latest (observed C))+inverseCongruence T (Tᵀ*F*T) := by
    simp only [inverseCongruence,Matrix.mul_add,Matrix.add_mul]
  rw [hlin,hflag,hsum,inverseCongruence_compressed T F hT]
  exact add_comm _ _

/-- The genuine clean latest-model error is the actual full-basis compression of its true oblique staircase.
Use: Identify the actual uniform RFC leading curvature factor without an assumed expansion.
Article: main_krylov, thm:UCq.
Proof: Compress the proved exact inverse-congruence staircase identity and cancel the genuine full basis using its actual nonsingular domain.
-/
theorem clean_model_compression (T : Matrix (Fin n) (Fin n) ℝ) (hT : IsUnit T.det)
    (A E : ℕ → Matrix (Fin n) (Fin n) ℝ) (F : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ j, (A j).IsSymm) (hE : ∀ j<n, A (j+1)-A j=E j) :
    Tᵀ*(A n+F)*T-latest (observed (fun j => Tᵀ*A j*T))=Tᵀ*obliqueStaircase T E F n*T := by
  have h := congrArg (fun X => Tᵀ*X*T) (clean_model_inverseCongruence T hT A E F hA hE)
  rw [compress_inverseCongruence T _ hT] at h
  exact h

/-- The actual compressed operator observations are exactly the original chronological cross Gram with each column’s own true image.
Use: Identify the actual uniform RFC leading curvature factor without an assumed expansion.
Article: main_krylov, thm:UCq.
Proof: Read each genuine observed-time column and apply the existing full-basis compression pairing identity.
-/
theorem observed_compression_crossGram (s : Fin n → EuclideanSpace ℝ (Fin n))
    (A : ℕ → Matrix (Fin n) (Fin n) ℝ) :
    observed (fun j => (fullBasisMatrix s)ᵀ*A j*fullBasisMatrix s)=
      crossGram s (fun i => cgOperator (A i.val) (s i)) := by
  ext i j
  exact (congrFun (congrFun (fullBasisMatrix_compression s (A j.val)) i) j).symm

/-- The true clean observed model-error matrix has its exact full-basis staircase factorization.
Use: Identify the actual uniform RFC leading curvature factor without an assumed expansion.
Article: main_krylov, thm:UCq.
Proof: Identify the genuine constant terminal compression and actual own-time image cross Gram, then use the proved exact full compressed staircase identity.
-/
theorem clean_observed_model_factorization (s : Fin n → EuclideanSpace ℝ (Fin n))
    (hT : IsUnit (fullBasisMatrix s).det)
    (A E : ℕ → Matrix (Fin n) (Fin n) ℝ) (F : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ j, (A j).IsSymm) (hE : ∀ j<n, A (j+1)-A j=E j) :
    correctionCompression s (cgOperator (A n+F))-latest (crossGram s (fun i => cgOperator (A i.val) (s i)))=
      (fullBasisMatrix s)ᵀ*obliqueStaircase (fullBasisMatrix s) E F n*fullBasisMatrix s := by
  rw [fullBasisMatrix_compression,← observed_compression_crossGram]
  exact clean_model_compression (fullBasisMatrix s) hT A E F hA hE

end
end krylov.Correction
