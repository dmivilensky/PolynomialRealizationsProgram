import jacobi.Support.CorrectedChain
import jacobi.Finite.Eigenvectors

/-!
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Both actual support matrices have the genuine same positive probability
weights. Their spectral measures are constructed with the earlier finite
inverse-spectral machinery and are proved to reconstruct exactly the
original support matrices, including the corrected, possibly noncontractive
model spectrum. This fixes the actual orthogonal polynomial families.
Use: the original top-node and Volterra estimates concern its actual orthogonal polynomials, and supportMeasure retains the same original probabilities after affine correction.
-/
namespace jacobi.Support
noncomputable section
open Real Matrix Polynomial jacobi.Finite chebyshev1 chebyshev2
set_option backward.isDefEq.respectTransparency false

/-- The actual original natural support spectral measure with its genuine canonical positive weights.
Use: the original top-node and Volterra estimates concern its actual orthogonal polynomials, and supportMeasure retains the same original probabilities after affine correction.
Article: jacobi, Appendix C.3 (support weights and segment bounds).
-/
def naturalMeasure (a b : ℝ) (ha : -1<a) (hb : -1<b) (n : ℕ) : DiscreteMeasure (n+1) :=
  (naturalNodes a b ha hb (n+1)).measure (naturalNodes a b ha hb (n+1)).persymmetricWeights

/-- The actual original natural support measure reconstructs exactly the original sine-coefficient chain.
Use: its canonical spectral orthogonal polynomials are the true original support recurrence polynomials.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Proof: the independently proved original characteristic polynomial and persymmetry identify the original chain with the existing actual canonical positive-weight reconstruction. -/
theorem naturalMeasure_reconstructed (a b : ℝ) (ha : -1<a) (hb : -1<b) (n : ℕ) :
    (naturalMeasure a b ha hb n).reconstructed=naturalChain a b ha hb (n+1) :=
  (naturalChain_canonical a b ha hb n).symm

/-- The actual original natural ordered spectral basis has exactly the original canonical positive support probabilities.
Use: supportBasis_weight proves that the corrected support basis has precisely the same genuine first-site spectral measure.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Proof: the original natural chain has proved actual persymmetry and the exact original full spectrum. The earlier complete reciprocal-weight characterization therefore identifies its actual ordered first-row weights. -/
theorem naturalBasis_weight (a b : ℝ) (ha : -1<a) (hb : -1<b) (n : ℕ) (k:Fin (n+1)) :
    (naturalBasis a b ha hb (n+1)).weight 0 k=(naturalMeasure a b ha hb n).weight k := by
  let J : Fiber (n+1) (naturalNodes a b ha hb (n+1)).polynomial :=
    ⟨naturalChain a b ha hb (n+1),naturalChain_inFiber a b ha hb (n+1)⟩
  have h := symmetric_weights (naturalNodes a b ha hb (n+1)) J (naturalChain_persymmetric a b ha hb (n+1))
  exact congrArg (fun w:WeightSimplex (n+1) => w.val k) h

/-- The actual corrected original support spectral basis has exactly the same original positive probability weights as the natural chain.
Use: the original target/support Gram comparison and weight ratio use this actual common spectral measure.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: the true affine spectral construction keeps the actual original eigenvectors, and their natural first-row weights were independently identified with the actual positive original support probabilities. -/
theorem supportBasis_weight (a b : ℝ) (ha : -1<a) (hb : -1<b) (n : ℕ) (k:Fin (n+1)) :
    (supportBasis a b ha hb (show 0<n+1 by omega)).weight 0 k=(naturalMeasure a b ha hb n).weight k := by
  rw [supportBasis,affineBasis_weight,naturalBasis_weight]

/-- The genuine corrected original model-node family is injective, without any contractivity premise.
Use: supportMeasure is the actual finite positive spectral measure at the original corrected nodes even if its endpoint lies outside (-1,1).
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Proof: the actual original affine scale is strictly positive and the genuine original cosine nodes are distinct. -/
theorem correctedNodes_injective {a b : ℝ} (ha : -1<a) (hb : -1<b) {n : ℕ} (hn:0<n) :
    Function.Injective (fun k:Fin n => jacobi.Jacobi.modelNode a b n k) := by
  intro i j hij
  apply (naturalNodes a b ha hb n).strictAnti.injective
  apply mul_left_cancel₀ (modelScale_pos ha hb hn).ne'
  exact add_right_cancel hij

/-- The actual original corrected support spectral measure, with unchanged genuine positive natural probabilities.
Use: its canonical orthogonal polynomials are the original psi_(n,m)^0 used in the finite Gram matrix and Cholesky limit.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
-/
def supportMeasure (a b : ℝ) (ha : -1<a) (hb : -1<b) (n : ℕ) : DiscreteMeasure (n+1) where
  node k := jacobi.Jacobi.modelNode a b (n+1) k
  distinct := correctedNodes_injective ha hb (by omega)
  weight := (naturalMeasure a b ha hb n).weight
  positive := (naturalMeasure a b ha hb n).positive
  probability := (naturalMeasure a b ha hb n).probability

/-- The actual original corrected support measure reconstructs exactly the original affine sine-coefficient support matrix.
Use: the support polynomial and Gram constructions retain the genuine original finite chain, not an independently postulated comparison family.
Article: jacobi, Appendix C.3 (askey–Wilson comparison chain).
Proof: both actual finite matrices have the original corrected node values and the same genuine original positive first-site weights. The earlier full finite inverse-spectral uniqueness theorem identifies their complete original coefficient records. -/
theorem supportMeasure_reconstructed (a b : ℝ) (ha : -1<a) (hb : -1<b) (n : ℕ) :
    (supportMeasure a b ha hb n).reconstructed=supportChain a b ha hb (n+1) := by
  -- Equality is proved for the actual full finite Jacobi data, including their fixed tails.
  let J := supportChain a b ha hb (n+1)
  let M := supportMeasure a b ha hb n
  let B := supportBasis a b ha hb (show 0<n+1 by omega)
  have he : B.eigenvalues=M.reconstructedBasis.eigenvalues := by
    funext k
    exact supportBasis_values a b ha hb (by omega) k
  have hi : Function.Injective B.eigenvalues := by
    rw [he]
    exact M.distinct
  apply Eq.symm
  apply unique_of_spectral_weights J M.reconstructed (supportChain_irreducible a b ha hb (by omega))
    B M.reconstructedBasis he hi
  intro k
  have hw := M.reconstructed_weight (show 0<n+1 by omega) k
  have hz : (⟨0,show 0<n+1 by omega⟩:Fin (n+1))=0 := by apply Fin.ext; simp only [Fin.val_zero]
  rw [hz] at hw
  rw [hw]
  exact supportBasis_weight a b ha hb n k

end
end jacobi.Support
