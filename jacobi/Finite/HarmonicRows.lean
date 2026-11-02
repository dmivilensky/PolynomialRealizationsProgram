import jacobi.Reference.HarmonicSums
import jacobi.Finite.PuncturedProducts
import jacobi.Finite.TwoEdgeIndices

/-!
Article: jacobi, Appendix C.4 (target/support weight ratios).
The complete reciprocal index-gap row is exactly two finite harmonic
prefixes. Its logarithmic bound reuses the earlier genuine community
harmonic-number estimate, with no dimension-dependent hidden constant.
Source: finite harmonic sums and reflection of integer intervals.
Use: harmonic_index_row evaluates the original spectral gap row before applying the already proved harmonic logarithm estimate.
-/
namespace jacobi.Finite
noncomputable section
open Real Finset jacobi.Reference

/-- A finite sum with one omitted natural index splits into its two contiguous index intervals.
Use: harmonic_index_row evaluates the original spectral gap row before applying the already proved harmonic logarithm estimate.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Source: elementary finite interval summation.
Proof: the erased original range is the disjoint union of the two intervals; translate the second interval back to its zero-based range. -/
theorem punctured_sum {M:Type*} [AddCommMonoid M] (f:ℕ→M) {n k:ℕ} (hk:k≤n) :
    (∑j∈(range (n+1)).erase k,f j)=(∑j∈range k,f j)+(∑j∈range (n-k),f (k+1+j)) := by
  -- The omitted point belongs to neither summation interval, including at both original endpoints.
  have hs : (range (n+1)).erase k=range k∪Ico (k+1) (n+1) := by
    ext j
    simp only [mem_erase,mem_range,mem_union,mem_Ico]
    omega
  have hd : Disjoint (range k) (Ico (k+1) (n+1)) := by
    rw [disjoint_left]
    intro j hj hj'
    simp only [mem_range,mem_Ico] at hj hj'
    omega
  rw [hs,sum_union hd,sum_Ico_eq_sum_range,show n+1-(k+1)=n-k by omega]

/-- A finite-index sum with one omitted point equals the same original sum over natural lattice indices.
Use: harmonic_index_row applies the exact interval-splitting identity to the actual finite spectral row.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: the finite-index value map is a bijection onto the original erased natural range. -/
theorem fin_punctured_sum {M:Type*} [AddCommMonoid M] (f:ℕ→M) {n:ℕ} (k:Fin (n+1)) :
    (∑j∈(univ:Finset (Fin (n+1))).erase k,f j)=∑j∈(range (n+1)).erase k.val,f j := by
  -- The value bijection preserves the omitted original diagonal and reaches every remaining lattice point.
  apply sum_bij (fun (j:Fin (n+1)) _ => j.val)
  · intro j hj
    exact mem_erase.mpr ⟨fun he => (mem_erase.mp hj).1 (Fin.ext he),mem_range.mpr j.isLt⟩
  · intro i _ j _ hij
    exact Fin.ext hij
  · intro j hj
    refine ⟨⟨j,mem_range.mp (mem_erase.mp hj).2⟩,?_,rfl⟩
    exact mem_erase.mpr ⟨fun he => (mem_erase.mp hj).1 (congrArg Fin.val he),mem_univ _⟩
  · intro _ _
    rfl

/-- The complete actual reciprocal integer-gap row is exactly the sum of its two genuine harmonic prefixes.
Use: harmonic_index_row_bound supplies the full growing-bulk part of the original finite relative-product logarithm estimate.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: split at the genuine omitted diagonal. Reflect the left prefix and translate the right prefix; both original absolute integer gaps become the positive index j+1. -/
theorem harmonic_index_row {n:ℕ} (i:Fin (n+1)) :
    (∑j∈univ.erase i,1/|(i.val:ℝ)-j.val|)=harmonicSum i.val+harmonicSum (n-i.val) := by
  -- All reciprocals are finite and off the actual diagonal before the harmonic bound is invoked.
  rw [fin_punctured_sum (fun j:ℕ => 1/|(i.val:ℝ)-j|) i,punctured_sum _ (show i.val≤n by omega)]
  congr 1
  · unfold harmonicSum
    rw [← sum_range_reflect (fun j:ℕ => 1/(j+1:ℝ)) i.val]
    apply sum_congr rfl
    intro j hj
    have hj' := mem_range.mp hj
    have hcast : ((i.val-1-j:ℕ):ℝ)+1=(i.val:ℝ)-j := by
      have he : (((i.val-1-j:ℕ):ℝ)+1)+(j:ℝ)=i.val := by exact_mod_cast (show i.val-1-j+1+j=i.val by omega)
      linarith
    have hjr : (j:ℝ)≤ i.val := by exact_mod_cast hj'.le
    rw [abs_of_nonneg (sub_nonneg.mpr hjr),hcast]
  · unfold harmonicSum
    apply sum_congr rfl
    intro j _
    have hj0 := Nat.cast_nonneg j (α:=ℝ)
    simp only [Nat.cast_add,Nat.cast_one]
    rw [abs_of_nonpos (by linarith)]
    congr 1
    ring

/-- Every full reciprocal spectral index-gap row has the original dimension-uniform logarithmic bound.
Use: comparisonWeight_log_bound sums the growing-bulk term of the actual finite relative-gap logarithm majorant.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: both exact harmonic prefixes are bounded by the same full-dimensional harmonic sum, which has the earlier proved community logarithmic estimate. -/
theorem harmonic_index_row_bound {n:ℕ} (i:Fin (n+1)) :
    (∑j∈univ.erase i,1/|(i.val:ℝ)-j.val|)≤2*(1+log (n+1:ℝ)) := by
  rw [harmonic_index_row]
  have h₁ := harmonicSum_mono (show i.val≤n+1 by omega)
  have h₂ := harmonicSum_mono (show n-i.val≤n+1 by omega)
  have h₃ := harmonicSum_log_bound (n+1)
  push_cast at h₃
  linarith

/-- The full growing-bulk row in the original two-edge logarithm estimate has the same dimension-uniform harmonic bound.
Use: comparisonWeight_log_bound controls the frequency-squared remainder in the original finite relative product.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: the original pair-index weight dominates the sum of the two original edge distances. Each off-diagonal summand is therefore at most the reciprocal genuine integer gap, whose exact complete harmonic row is already bounded. -/
theorem twoEdge_harmonic_row {n:ℕ} (i:Fin (n+1)) :
    (∑j∈univ.erase i,((jacobi.Jacobi.edgeIndex (n+1) i.val:ℝ)+
      (jacobi.Jacobi.edgeIndex (n+1) j.val:ℝ))/
        (|(i.val:ℝ)-j.val| *(jacobi.Jacobi.pairIndex (n+1) i.val j.val:ℝ)))≤2*(1+log (n+1:ℝ)) := by
  -- The two original edge distances are kept together before using the common pair lower bound.
  apply le_trans _ (harmonic_index_row_bound i)
  apply sum_le_sum
  intro j hj
  have hne : i.val≠j.val := fun he => (mem_erase.mp hj).1 (Fin.ext he).symm
  have hd : 0< (|(i.val:ℝ)-j.val|) := abs_pos.mpr (sub_ne_zero.mpr (by exact_mod_cast hne))
  have hm : (jacobi.Jacobi.edgeIndex (n+1) i.val:ℝ)+(jacobi.Jacobi.edgeIndex (n+1) j.val:ℝ)≤
      (jacobi.Jacobi.pairIndex (n+1) i.val j.val:ℝ) := by exact_mod_cast pairIndex_ge_edges i.isLt j.isLt
  have hp : 0<(jacobi.Jacobi.pairIndex (n+1) i.val j.val:ℝ) := by
    exact_mod_cast (show 0< jacobi.Jacobi.pairIndex (n+1) i.val j.val by dsimp [jacobi.Jacobi.pairIndex]; omega)
  apply (div_le_div_iff₀ (mul_pos hd hp) hd).mpr
  have h := mul_le_mul_of_nonneg_left hm hd.le
  nlinarith only [h]

end
end jacobi.Finite
