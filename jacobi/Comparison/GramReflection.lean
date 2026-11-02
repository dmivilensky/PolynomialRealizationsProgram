import jacobi.Comparison.GramEdgeTerms
import jacobi.Support.PolynomialParity
import jacobi.Support.WeightBounds

/-!
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Exact reflection of the original target probabilities and complete
original Gram summands. The alternating factor comes from the actual
canonical support-polynomial parity, with the true finite node and
weight reflection and the exact n+1 dimension convention.
Use: gramSummand_reflection retains the actual target weight when reducing the left spectral edge to the right edge for the exchanged parameters.
-/
namespace jacobi.Comparison
noncomputable section
open Real Set Filter jacobi.Support jacobi.Reference jacobi.Jacobi
open scoped Topology

/-- The actual original target probability reflects exactly under the original parameter swap.
Use: gramSummand_reflection retains the actual target weight when reducing the left spectral edge to the right edge for the exchanged parameters.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Proof: the original target probability is its actual support probability times its actual target/support ratio. Both factors already have exact genuine reflection identities. -/
theorem targetWeight_reflection {a b:ℝ} (ha:-1<a) (hb:-1<b) {n k:ℕ} (hk:k≤n) :
    targetWeight a b ha hb n (n-k)=targetWeight b a hb ha n k := by
  rw [targetWeight_factor,targetWeight_factor,comparisonWeightAt_reflection ha hb hk,
    naturalWeight_reflection ha hb hk]

/-- Every original finite Gram summand reflects with exactly the canonical alternating row-column sign.
Use: gramPerturbation_two_halves identifies the whole actual opposite spectral half with the strict right half for the exchanged original parameters.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Proof: the true target and support probabilities reflect exactly, both original spectral nodes negate, and each actual corrected support polynomial has its proved canonical degree parity. Multiply the two genuine signs and use their exact exponent sum. -/
theorem gramSummand_reflection (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) (i j k:Fin (n+1)) :
    gramSummand a b ha hb n i j k.rev=
      (-1:ℝ)^(i.val+j.val)*gramSummand b a hb ha n i j k := by
  -- The original finite reversal is the same for the actual nodes and their actual probabilities.
  have hk : k.rev.val=n-k.val := by rw [Fin.val_rev]; omega
  have hw := targetWeight_reflection ha hb (n:=n) (k:=k.val) (by omega)
  rw [← hk] at hw
  have hwt : (targetMeasure a b ha hb n).weight k.rev=(targetMeasure b a hb ha n).weight k := by
    simpa only [targetWeight,dite_eq_left k.rev.isLt,dite_eq_left k.isLt] using hw
  have hws : (supportMeasure a b ha hb n).weight k.rev=(supportMeasure b a hb ha n).weight k :=
    naturalMeasure_weight_reflection a b ha hb n k
  have hmodel : modelNode a b (n+1) k.rev.val= -modelNode b a (n+1) k.val := by
    have he : (n+1)-1-k.val=k.rev.val := by rw [Fin.val_rev]; omega
    rw [← he]
    exact modelNode_reflection (n:=n+1) (k:=k.val) ha hb k.isLt
  rw [gramSummand,gramSummand,hwt,hws,nodes_reflection ha hb k,hmodel,
    supportPolynomial_parity a b ha hb n i,supportPolynomial_parity a b ha hb n j,
    supportPolynomial_parity a b ha hb n i,supportPolynomial_parity a b ha hb n j,pow_add]
  ring

/-- The actual zero-padded scalar Gram summand has the same exact original reflected-edge identity at every valid source index.
Use: gramPerturbation_two_halves applies the literal finite integer half-row partition without carrying a dependent finite spectral index through the reflection.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Proof: both scalar indices belong to the original finite dimension. Their two padded values are the genuine finite Gram summands, and n-k is precisely the actual finite reversal of k. -/
theorem gramSummandAt_reflection {a b:ℝ} (ha:-1<a) (hb:-1<b) (n:ℕ)
    (i j:Fin (n+1)) {k:ℕ} (hk:k≤n) :
    gramSummandAt a b ha hb n i j (n-k)=
      (-1:ℝ)^(i.val+j.val)*gramSummandAt b a hb ha n i j k := by
  have hkN : k<n+1 := by omega
  have hrN : n-k<n+1 := by omega
  rw [gramSummandAt,gramSummandAt,dite_eq_left hkN,dite_eq_left hrN]
  have he : (⟨n-k,hrN⟩:Fin (n+1))=(⟨k,hkN⟩:Fin (n+1)).rev := by
    apply Fin.ext
    simp only [Fin.val_rev]
    omega
  rw [he,gramSummand_reflection]

end
end jacobi.Comparison
