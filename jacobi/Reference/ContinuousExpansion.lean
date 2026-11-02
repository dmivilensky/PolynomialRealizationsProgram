import jacobi.Reference.ZeroGreenRows
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
The proved actual complete reference Hilbert basis expands every
continuous full-interval row through its original spatial integrals.
This fixes the bridge between the selected Green factor coefficients
and the genuine uniformly convergent original Green series.
Use: zeroGreen_factorization transfers the proved equality of the actual full L2 Green rows to their original continuous pointwise representatives.
-/
namespace jacobi.Reference
noncomputable section
open Real Set MeasureTheory
open scoped Topology InnerProductSpace
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false

/-- The genuine continuous-function embedding into the actual unit-interval L2 space is injective.
Use: zeroGreen_factorization transfers the proved equality of the actual full L2 Green rows to their original continuous pointwise representatives.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
Source: continuous functions equal almost everywhere on a nondegenerate real interval are equal everywhere, mathlib MeasureTheory.Measure.OpenPos.
Proof: the genuine L2 representatives agree almost everywhere. Continuously clamp both functions to the real unit interval, transfer the subtype almost-everywhere identity to restricted Lebesgue measure, and apply the community closed-interval uniqueness theorem. -/
theorem continuous_toLp_injective :
    Function.Injective (ContinuousMap.toLp (𝕜 := ℝ) (p := 2) (E := ℝ) (α := Interval) volume) := by
  -- The full physical interval has no isolated endpoint masses; continuity fixes both null endpoints as well.
  intro f g hfg
  have hf := ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 2) volume f
  have hg := ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 2) volume g
  rw [hfg] at hf
  have hAE : (fun t : Interval => f t)=ᵐ[volume] (fun t : Interval => g t) := hf.symm.trans hg
  let P : ℝ → Interval := Set.projIcc (0:ℝ) 1 (by norm_num)
  have hP : Continuous P := continuous_projIcc
  have he : (fun x => f (P x))=ᵐ[volume.restrict (Icc (0:ℝ) 1)] (fun x => g (P x)) := by
    apply (ae_restrict_iff_subtype measurableSet_Icc).mpr
    filter_upwards [hAE] with t ht
    simpa only [P,Set.projIcc_of_mem (by norm_num : (0:ℝ)≤1) t.property] using ht
  have hpoint := Measure.eqOn_Icc_of_ae_eq volume (by norm_num : (0:ℝ)≠1) he
    (f.continuous.comp hP).continuousOn (g.continuous.comp hP).continuousOn
  ext t
  simpa only [P,Set.projIcc_of_mem (by norm_num : (0:ℝ)≤1) t.property] using hpoint t.property

/-- The original continuous reference eigenfunction on the genuine full unit interval.
Use: continuousEigenfunction_toLp identifies the continuous original Green row summands with the genuine reference basis vectors.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
-/
def continuousEigenfunction (a : ℝ) (ha : -1<a) (k : ℕ) : C(Interval,ℝ) :=
  ⟨fun t => eigenfunction a k t,(eigenfunction_properties ha k).1.comp continuous_subtype_val⟩

/-- The continuous original reference eigenfunction has exactly the previously constructed genuine reference L2 vector.
Use: maps the original continuous Green summands to the actual basis vectors without assuming equality of pointwise and spectral constructions.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
Proof: both original L2 vectors have the same independently proved genuine eigenfunction representative almost everywhere. -/
theorem continuousEigenfunction_toLp (a : ℝ) (ha : -1<a) (k : ℕ) :
    ContinuousMap.toLp (𝕜 := ℝ) (p := 2) volume (continuousEigenfunction a ha k)=waveVector a ha k := by
  apply Lp.ext
  exact (ContinuousMap.coeFn_toLp volume (continuousEigenfunction a ha k)).trans (waveVector_ae a ha k).symm

/-- The original coefficient of a continuous full-interval function is its genuine spatial integral against the original reference eigenfunction.
Use: zeroGreen_factorization applies the independently proved Green factor coefficient formula to the actual full reference Hilbert expansion.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
Proof: replace the continuous function's L2 vector by its genuine almost-everywhere representative and identify the subtype measure with the original real interval measure. -/
theorem continuous_referenceCoefficient (a : ℝ) (k : ℕ) (g : C(Interval,ℝ)) :
    referenceCoefficient a k (ContinuousMap.toLp (𝕜 := ℝ) (p := 2) volume g)=
      ∫ t : Interval,g t*eigenfunction a k t := by
  unfold referenceCoefficient
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 2) volume g] with t ht
  rw [ht]

/-- Every actual full reference L2 vector has its genuine unnormalized eigenfunction expansion with the original reference integral coefficients.
Use: zeroGreen_factorization evaluates these exact coefficients for the selected-solution Green factor and compares the result with the independently proved continuous Green norm series.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
Source: Hilbert basis expansion, mathlib Analysis.InnerProductSpace.l2Space, HilbertBasis.hasSum_repr.
Proof: use the already proved complete original reference Hilbert basis. Its genuine normalization divides both the coefficient and the vector by sqrt(N_k); the actual positive squared norm cancels their product exactly. -/
theorem reference_vector_expansion (a : ℝ) (ha : -1<a) (v : Space) :
    HasSum (fun k : ℕ => (referenceCoefficient a k v/norming a k) • waveVector a ha k) v := by
  -- The basis and its normalization are the actual original functions and their independently evaluated norms.
  convert (hilbertBasis a ha).hasSum_repr v using 1
  funext k
  rw [HilbertBasis.repr_apply_apply,hilbertBasis_apply,normalizedWave,real_inner_smul_left,
    ← referenceCoefficient_inner,smul_smul]
  congr 1
  have hN := norming_pos ha k
  have hs := Real.sq_sqrt hN.le
  field_simp [(Real.sqrt_pos.mpr hN).ne',hN.ne']
  nlinarith [congrArg (fun x : ℝ => referenceCoefficient a k v*x) hs]

/-- Each actual continuous Green summand maps to precisely its true reference L2 basis term.
Use: zeroGreen_factorization compares the continuous norm series with the complete original Hilbert expansion term by term.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
Proof: the original continuous summand is its fixed genuine coefficient times the original continuous reference eigenfunction. Linearity of the community L2 embedding and the proved representative identity give the true reference vector. -/
theorem zeroGreenRowTerm_toLp (a : ℝ) (ha : -1<a) (k : ℕ) (s : ℝ) :
    ContinuousMap.toLp (𝕜 := ℝ) (p := 2) volume (zeroGreenRowTerm a ha k s)=
      (eigenfunction a k s/(norming a k*(jacobi.Bessel.phaseGrid a k)^2)) • waveVector a ha k := by
  have he : zeroGreenRowTerm a ha k s=
      (eigenfunction a k s/(norming a k*(jacobi.Bessel.phaseGrid a k)^2)) • continuousEigenfunction a ha k := by
    ext t
    change zeroGreenTerm a k t s=_
    simp only [zeroGreenTerm,realSolution_at_reference,ContinuousMap.smul_apply,smul_eq_mul,continuousEigenfunction,ContinuousMap.coe_mk]
    ring
  rw [he,map_smul,continuousEigenfunction_toLp]

end
end jacobi.Reference
