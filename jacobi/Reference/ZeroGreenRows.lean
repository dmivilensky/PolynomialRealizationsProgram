import jacobi.Reference.ZeroGreenSeries
import jacobi.Reference.Parseval
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
For a fixed physical half-interval source, the original Green series
converges in the uniform norm on the entire unit interval. Exact
reference parity extends the proved half-square majorant. This norm
series can then be mapped to the original full reference L2 space.
Use: zeroGreenTerm_full_bound extends the proved original half-square Green bound to a full spatial row, needed for the complete reference Hilbert expansion.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Filter MeasureTheory
open scoped Topology
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false

/-- Reflection preserves the absolute value of every actual reference eigenfunction.
Use: zeroGreenTerm_full_bound extends the proved original half-square Green bound to a full spatial row, needed for the complete reference Hilbert expansion.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
Proof: the exact original eigenfunction reflection has sign (-1)^k, whose absolute value is one. -/
theorem eigenfunction_abs_reflection {a : ℝ} (ha : -1<a) (k : ℕ) (t : ℝ) :
    |eigenfunction a k (1-t)|=|eigenfunction a k t| := by
  rw [eigenfunction_reflection ha,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul]

/-- Every original reference Green term satisfies its common inverse-square bound on each complete spatial row with a physical half-interval source.
Use: zeroGreenRowTerm_summable gives a genuine uniformly convergent full-interval continuous-function expansion, which can be compared with the complete reference L2 expansion.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
Proof: in the left half use the proved all-index half-square bound; in the right half exact reference reflection preserves the absolute value of the summand. -/
theorem zeroGreenTerm_full_bound {a : ℝ} (ha : -1<a) :
    ∃ B : ℝ,0<B ∧ ∀ k : ℕ,∀ t∈Icc (0:ℝ) 1,∀ s∈Icc (0:ℝ) (1/2),
      |zeroGreenTerm a k t s|≤B/(k+1:ℝ)^2 := by
  -- Full-interval extension uses the true reference parity and keeps the same original spectral enumeration.
  obtain ⟨B,hB,hbound⟩ := zeroGreenTerm_uniform_bound ha
  refine ⟨B,hB,fun k t ht s hs => ?_⟩
  by_cases hh : t≤1/2
  · exact hbound k t ⟨ht.1,hh⟩ s hs
  · have hr : 1-t∈Icc (0:ℝ) (1/2) := ⟨by linarith [ht.2],by linarith⟩
    have he : |zeroGreenTerm a k t s|=|zeroGreenTerm a k (1-t) s| := by
      simp only [zeroGreenTerm,abs_div,abs_mul,realSolution_at_reference,eigenfunction_abs_reflection ha]
    exact he.trans_le (hbound k (1-t) hr s hs)

/-- An actual reference Green summand as a continuous function on the complete original unit interval.
Use: its genuine norm series maps continuously into the actual full reference L2 space for Green factorization.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
-/
def zeroGreenRowTerm (a : ℝ) (ha : -1<a) (k : ℕ) (s : ℝ) : C(Interval,ℝ) :=
  ⟨fun t => zeroGreenTerm a k t s,by
    simp only [zeroGreenTerm,realSolution_at_reference]
    exact (((eigenfunction_properties ha k).1.comp continuous_subtype_val).mul continuous_const).div_const _⟩

/-- The full original reference Green row series converges in the actual uniform norm on the entire unit interval.
Use: its continuous-function sum can be mapped to L2 without any pointwise or completeness assumption about a proposed Green factorization.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
Proof: the same proved inverse-square majorant bounds each genuine continuous row term in supremum norm. -/
theorem zeroGreenRowTerm_summable {a s : ℝ} (ha : -1<a) (hs : s∈Icc (0:ℝ) (1/2)) :
    Summable (fun k : ℕ => zeroGreenRowTerm a ha k s) := by
  obtain ⟨B,hB,hbound⟩ := zeroGreenTerm_full_bound ha
  have hm : Summable (fun k : ℕ => B/(k+1:ℝ)^2) := by
    simpa only [one_pow,mul_one_div] using (jacobi.Bessel.inverse_square_majorant_summable 1).mul_left B
  exact hm.of_norm_bounded (fun k => (ContinuousMap.norm_le _ (by positivity)).mpr
    (fun t => by change |zeroGreenTerm a k t s|≤_; exact hbound k t t.property s hs))

/-- The norm sum of the actual original Green row series on the entire physical unit interval.
Use: zeroGreenRow_apply identifies it pointwise with the original Green kernel, while its continuous L2 image is compared with the complete original Hilbert expansion.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
-/
def zeroGreenRow (a : ℝ) (ha : -1<a) (s : ℝ) : C(Interval,ℝ) :=
  ∑' k : ℕ,zeroGreenRowTerm a ha k s

/-- The actual continuous full reference Green row evaluates to the original spectral Green series at every original spatial point.
Use: after identifying its L2 class with the selected-solution factor, continuity transfers that identity to the original pointwise Green kernel.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
Proof: genuine norm summability allows the community continuous point-evaluation functional to commute with the actual series. -/
theorem zeroGreenRow_apply {a s : ℝ} (ha : -1<a) (hs : s∈Icc (0:ℝ) (1/2)) (t : Interval) :
    zeroGreenRow a ha s t=zeroGreenKernel a t s :=
  (ContinuousMap.evalCLM ℝ t).map_tsum (zeroGreenRowTerm_summable ha hs)

end
end jacobi.Reference
