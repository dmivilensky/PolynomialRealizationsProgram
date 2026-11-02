import jacobi.Reference.ZeroGreenCoefficients
import jacobi.Reference.ContinuousExpansion

/-!
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
The full original Green spectral series equals the printed selected
left/right factor. The coefficient calculation, complete reference
Hilbert expansion, uniform original continuous-function series and
injectivity of its true L2 embedding all concern the original objects.
Use: zeroGreen_factorization matches the complete original Hilbert expansion term by term with the independently proved uniformly convergent original Green series.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Filter MeasureTheory
open scoped Topology
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] realSolution zeroGreenFactor zeroGreenConstant

/-- The actual selected-solution Green factor has exactly its original coefficient in the actual full reference L2 basis.
Use: zeroGreen_factorization matches the complete original Hilbert expansion term by term with the independently proved uniformly convergent original Green series.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
Proof: the continuous L2 embedding has the original pointwise factor as representative. Its actual subtype Lebesgue integral equals the original unit-interval integral; divide the proved exact Green coefficient identity by the genuine positive squared phase. -/
theorem zeroGreenFactor_referenceCoefficient {a s : ℝ} (ha : -1<a)
    (hs : s∈Ioo (0:ℝ) 1) (k : ℕ) :
    referenceCoefficient a k (ContinuousMap.toLp (𝕜 := ℝ) (p := 2) volume (zeroGreenFactorRow a ha s hs))=
      eigenfunction a k s/(jacobi.Bessel.phaseGrid a k)^2 := by
  -- The full original physical measure, with only null endpoint changes, is used on both sides.
  rw [continuous_referenceCoefficient]
  change (∫ t : Interval,zeroGreenFactor a t s*eigenfunction a k t)=_
  rw [integral_subtype (s := Icc (0:ℝ) 1) measurableSet_Icc
    (fun t : ℝ => zeroGreenFactor a t s*eigenfunction a k t),integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
  apply (eq_div_iff (pow_ne_zero 2 (jacobi.Bessel.phaseGrid_pos ha k).ne')).mpr
  simpa only [mul_comm] using zeroGreenFactor_coefficient ha hs k

/-- The actual complete original reference Green series equals its original selected left/right factor throughout each full unit-interval row with a positive physical half-interval source.
Use: zeroGreen_factorization includes the zero source by genuine endpoint vanishing, completing Structure of F (b) and fixing the diagonal kink in the kernel used for Differentiability of K.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
Proof: expand the actual continuous factor row in the independently proved complete original reference Hilbert basis. Its exact original coefficients match the L2 images of the actual Green summands. Their original continuous-function norm series converges; injectivity of the community continuous L2 embedding identifies the continuous rows, hence their pointwise values. -/
theorem zeroGreen_factorization_pos {a s : ℝ} (ha : -1<a)
    (hs : s∈Ioc (0:ℝ) (1/2)) (t : Interval) :
    zeroGreenKernel a t s=zeroGreenFactor a t s := by
  -- Equality is first obtained in the actual complete Hilbert space, then for the genuine continuous representatives.
  have hs' : s∈Ioo (0:ℝ) 1 := ⟨hs.1,by linarith [hs.2]⟩
  let g := zeroGreenFactorRow a ha s hs'
  let L := ContinuousMap.toLp (𝕜 := ℝ) (p := 2) (E := ℝ) (α := Interval) volume
  have hb := reference_vector_expansion a ha (L g)
  have hterms (k : ℕ) : L (zeroGreenRowTerm a ha k s)=
      (referenceCoefficient a k (L g)/norming a k) • waveVector a ha k := by
    rw [zeroGreenRowTerm_toLp,zeroGreenFactor_referenceCoefficient ha hs']
    congr 1
    ring
  have hactual : HasSum (fun k : ℕ => L (zeroGreenRowTerm a ha k s)) (L g) := by
    simpa only [hterms] using hb
  have hcontinuous := L.hasSum (zeroGreenRowTerm_summable ha ⟨hs.1.le,hs.2⟩).hasSum
  have hrows : zeroGreenRow a ha s=g :=
    continuous_toLp_injective (hcontinuous.unique hactual)
  rw [← zeroGreenRow_apply ha ⟨hs.1.le,hs.2⟩ t,hrows]
  rfl

/-- The full original reference Green series has exactly the printed selected-solution factorization on the entire closed physical half square.
Use: combines with the fully proved original regularized derivative series to give the true triangular first and second derivatives of F required by Differentiability of K and the general target-operator Proposition C.2.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
Proof: the positive-source case follows from the complete actual Hilbert expansion and original uniform Green series. At source zero, every genuine spectral term vanishes, and the actual selected factor vanishes at the same endpoint. -/
theorem zeroGreen_factorization {a t s : ℝ} (ha : -1<a)
    (ht : t∈Icc (0:ℝ) (1/2)) (hs : s∈Icc (0:ℝ) (1/2)) :
    zeroGreenKernel a t s=zeroGreenFactor a t s := by
  by_cases hs0 : s=0
  · subst s
    rw [zeroGreenKernel,zeroGreenFactor,min_eq_right ht.1,max_eq_left ht.1]
    simp only [zeroGreenTerm,realSolution,solution_zero ha,Complex.zero_re,mul_zero,zero_mul,
      zero_div,tsum_zero]
  · exact zeroGreen_factorization_pos ha ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0),hs.2⟩ ⟨t,⟨ht.1,by linarith [ht.2]⟩⟩

end
end jacobi.Reference
