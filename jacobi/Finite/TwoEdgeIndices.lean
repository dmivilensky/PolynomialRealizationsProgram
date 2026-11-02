import jacobi.Jacobi.ZeroModel
import Mathlib.Data.Nat.Dist
import Mathlib.Topology.Instances.Nat

/-!
Article: jacobi, Appendix C.4 (target/support weight ratios).
The original two-edge indices obey the exact pair-gap and distance
inequalities used when summing the finite relative-product logarithms.
Folding the full spectral index set onto its nearer endpoint costs at
most a factor two for every nonnegative summand.
Use: edgeIndex_distance proves the original folded-index distance inequality without losing the small integer gap near the midpoint.
-/
namespace jacobi.Finite
noncomputable section
open Real Finset jacobi.Jacobi

/-- The integer distance of two natural indices has exactly the corresponding real absolute-difference value.
Use: edgeIndex_distance proves the original folded-index distance inequality without losing the small integer gap near the midpoint.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Source: the elementary natural-number distance identity.
Proof: order the indices, evaluate the two natural subtractions and cast the surviving nonnegative difference. -/
theorem nat_distance_real (i j:ℕ) : ((Nat.dist i j:ℕ):ℝ)=|(i:ℝ)-j| := by
  rcases le_total i j with h | h
  · have hR : (i:ℝ)≤j := by exact_mod_cast h
    rw [Nat.dist_eq_sub_of_le h,Nat.cast_sub h,abs_of_nonpos (sub_nonpos.mpr hR)]
    ring
  · have hR : (j:ℝ)≤ i := by exact_mod_cast h
    rw [Nat.dist_eq_sub_of_le_right h,Nat.cast_sub h,abs_of_nonneg (sub_nonneg.mpr hR)]

/-- The original pair-index weight dominates the sum of the two original nearer-edge indices.
Use: the finite logarithmic factor majorant reduces to the already proved inverse-square quadratic-gap series in comparisonWeight_log_bound.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: each nearer-edge index is bounded by either of its two endpoint distances. Both arguments of the original pair minimum therefore dominate their sum. -/
theorem pairIndex_ge_edges {N i j:ℕ} (hi:i<N) (hj:j<N) :
    edgeIndex N i+edgeIndex N j≤pairIndex N i j := by
  dsimp [edgeIndex,pairIndex]
  omega

/-- The original nearer-edge index is a nonexpanding function of the genuine integer spectral index.
Use: the off-diagonal finite logarithm row is bounded by the same actual translated inverse-square majorant as the continuum norming factors.
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
Proof: the original minimum of the two endpoint distances is nonexpanding on the finite integer interval. Natural arithmetic proves the distance inequality; cast its exact real absolute-difference values. -/
theorem edgeIndex_distance {N i j:ℕ} (hi:i<N) (hj:j<N) :
    |(edgeIndex N i:ℝ)-(edgeIndex N j:ℝ)|≤|(i:ℝ)-j| := by
  have h : Nat.dist (edgeIndex N i) (edgeIndex N j)≤Nat.dist i j := by
    dsimp [edgeIndex,Nat.dist]
    omega
  rw [← nat_distance_real,← nat_distance_real]
  exact_mod_cast h

/-- Every nonnegative sum over the actual two-edge fold is at most twice its unfolded positive-index sum.
Use: comparisonWeight_log_bound sums the genuine spectral perturbation majorant over the complete original finite spectrum, with no separate midpoint multiplicity assumption.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: at each original node the folded term is one of its two endpoint terms and is at most their sum. Sum the two original endpoint families; reflecting the second finite range gives precisely the first family. -/
theorem edgeIndex_sum_le (f:ℕ→ℝ) (hf:∀j,0≤f j) (N:ℕ) :
    (∑j∈range N,f (edgeIndex N j-1))≤2*∑j∈range N,f j := by
  -- This bound includes both parities of the original dimension and the possible single middle node.
  have hfold (j:ℕ) (hj:j<N) : f (edgeIndex N j-1)≤f j+f (N-1-j) := by
    have he : edgeIndex N j-1=min j (N-1-j) := by dsimp [edgeIndex]; omega
    rw [he]
    rcases le_total j (N-1-j) with h | h
    · rw [min_eq_left h]
      exact le_add_of_nonneg_right (hf _)
    · rw [min_eq_right h]
      exact le_add_of_nonneg_left (hf _)
  have h := sum_le_sum (fun j hj => hfold j (mem_range.mp hj))
  rw [sum_add_distrib,sum_range_reflect] at h
  linarith

end
end jacobi.Finite
