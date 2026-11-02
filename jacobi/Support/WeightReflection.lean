import jacobi.Support.Measures
import jacobi.Support.ParameterReflection

/-!
Article: jacobi, Appendix C.3 (support weights and segment bounds).
The original natural and corrected support weights reflect exactly
under parameter exchange. The proof uses their genuine constructed
spectral measures and the exact actual characteristic gap products.
Use: naturalDerivative_reflection proves exact reflection of the actual support probabilities, and the explicit sine-product weight formula starts from these same original gaps.
-/
namespace jacobi.Support
noncomputable section
open Real Polynomial Matrix jacobi.Finite

/-- The genuine natural support characteristic derivative is its exact original gap product.
Use: naturalDerivative_reflection proves exact reflection of the actual support probabilities, and the explicit sine-product weight formula starts from these same original gaps.
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Proof: the actual original natural spectral basis has its complete proved cosine eigenvalues and characteristic polynomial, so the earlier exact finite characteristic derivative formula applies. -/
theorem naturalDerivative_product (a b : ℝ) (ha : -1<a) (hb : -1<b) (n : ℕ) (k:Fin n) :
    (naturalNodes a b ha hb n).polynomial.derivative.eval (naturalNode a b n k)=
      ∏j∈Finset.univ.erase k,(naturalNode a b n k-naturalNode a b n j) := by
  have h := (naturalBasis a b ha hb n).charpoly_derivative k
  rw [naturalChain_charpoly] at h
  simpa only [naturalBasis_values] using h

/-- The absolute original support characteristic derivative reflects exactly under the genuine parameter-swap node pairing.
Use: naturalMeasure_weight_reflection identifies the actual canonical support normalization and probabilities without a separately assumed reflected measure.
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Proof: the actual characteristic derivative is the product of the original gaps. Reverse every genuine finite node index; each gap changes sign, leaving its absolute value unchanged. -/
theorem naturalDerivative_reflection (a b : ℝ) (ha : -1<a) (hb : -1<b) (n : ℕ) (k:Fin n) :
    |(naturalNodes a b ha hb n).polynomial.derivative.eval (naturalNode a b n k.rev)|=
      |(naturalNodes b a hb ha n).polynomial.derivative.eval (naturalNode b a n k)| := by
  -- A genuine finite bijection reverses the erased node set, so no zero gap is inserted into the product.
  rw [naturalDerivative_product,naturalDerivative_product,Finset.abs_prod,Finset.abs_prod]
  apply Finset.prod_bij (fun j _ => j.rev)
  · intro j hj
    have hne : j≠k.rev := (Finset.mem_erase.mp hj).1
    exact Finset.mem_erase.mpr ⟨fun he => hne (by simpa only [Fin.rev_rev] using congrArg Fin.rev he),Finset.mem_univ _⟩
  · intro i hi j hj he
    exact Fin.rev_injective he
  · intro j hj
    refine ⟨j.rev,?_,by simp⟩
    exact Finset.mem_erase.mpr ⟨fun he => (Finset.mem_erase.mp hj).1 (Fin.rev_injective he),Finset.mem_univ _⟩
  · intro j hj
    have he := naturalNode_reflection ha hb j.rev
    simp only [Fin.rev_rev] at he
    rw [naturalNode_reflection ha hb,he,show -naturalNode b a n k- -naturalNode b a n j.rev=
      -(naturalNode b a n k-naturalNode b a n j.rev) by ring,abs_neg]

/-- The actual original support spectral probabilities reverse exactly after exchanging the genuine endpoint parameters.
Use: the left-edge support envelope and Gram expansion reuse the actual right-edge measure and its proved asymptotics.
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Proof: the original canonical reciprocal-characteristic-derivative factors reflect exactly. Reversing the same finite summation also gives identical genuine positive normalizers, hence identical actual original probabilities. -/
theorem naturalMeasure_weight_reflection (a b : ℝ) (ha : -1<a) (hb : -1<b) (n : ℕ) (k:Fin (n+1)) :
    (naturalMeasure a b ha hb n).weight k.rev=(naturalMeasure b a hb ha n).weight k := by
  -- The original finite normalizer is compared as an exact sum, rather than absorbed into an unspecified proportionality constant.
  have hZ : (naturalNodes a b ha hb (n+1)).derivativeNormalizer=
      (naturalNodes b a hb ha (n+1)).derivativeNormalizer := by
    dsimp [Nodes.derivativeNormalizer]
    rw [← Equiv.sum_comp Fin.revPerm]
    apply Finset.sum_congr rfl
    intro j hj
    exact congrArg Inv.inv (naturalDerivative_reflection a b ha hb (n+1) j)
  change |(naturalNodes a b ha hb (n+1)).polynomial.derivative.eval (naturalNode a b (n+1) k.rev)|⁻¹/
      (naturalNodes a b ha hb (n+1)).derivativeNormalizer=
    |(naturalNodes b a hb ha (n+1)).polynomial.derivative.eval (naturalNode b a (n+1) k)|⁻¹/
      (naturalNodes b a hb ha (n+1)).derivativeNormalizer
  rw [hZ,naturalDerivative_reflection]

/-- The actual corrected support spectral probabilities obey the same full original parameter-swap reflection.
Use: the alternating left-edge term of the actual corrected target Gram matrix uses these same original common support probabilities.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Proof: the original affine correction retains exactly the genuine natural spectral probabilities, whose exact reflected pairing is already proved. -/
theorem supportMeasure_weight_reflection (a b : ℝ) (ha : -1<a) (hb : -1<b) (n : ℕ) (k:Fin (n+1)) :
    (supportMeasure a b ha hb n).weight k.rev=(supportMeasure b a hb ha n).weight k :=
  naturalMeasure_weight_reflection a b ha hb n k

end
end jacobi.Support
