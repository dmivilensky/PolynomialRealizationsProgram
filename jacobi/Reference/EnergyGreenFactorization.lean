import jacobi.Reference.EnergyGreenFactor
import jacobi.Reference.EnergyGreenSeries

/-!
Article: jacobi, Proposition C.4.
The actual selected-solution factor equals the original Green spectral
series on the full closed square at every E<tau_1. Its joint boundary
continuity and uniform expansion follow from the already proved series,
using the existing complete reference Hilbert basis only once.
Use: energyGreen_factorization_interior identifies the actual selected factor and original spectral series without a completeness or coefficient hypothesis.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Filter MeasureTheory
open scoped Topology
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] realSolution energyGreenFactor energyGreenConstant

/-- The original selected Green row has precisely its true coefficient in the complete reference Hilbert basis.
Use: energyGreen_factorization_interior identifies the actual selected factor and original spectral series without a completeness or coefficient hypothesis.
Article: jacobi, Proposition C.4.
Proof: use the genuine real Green coefficient identity, transfer the actual unit-interval integral to its subtype measure, and divide by the proved positive original energy gap. -/
theorem energyGreenFactor_referenceCoefficient {a E s : ℝ} (ha : -1<a)
    (hE : E<eigenvalue a 0) (hs : s∈Ioo (0:ℝ) 1) (k : ℕ) :
    referenceCoefficient a k (ContinuousMap.toLp (𝕜 := ℝ) (p := 2) volume
      (energyGreenFactorRow a E ha s hs))=eigenfunction a k s/(eigenvalue a k-E) := by
  -- The original physical integral and normalization are unchanged in the actual L2 embedding.
  rw [continuous_referenceCoefficient]
  change (∫ t : Interval,energyGreenFactor a E t s*eigenfunction a k t)=_
  rw [integral_subtype (s := Icc (0:ℝ) 1) measurableSet_Icc
    (fun t : ℝ => energyGreenFactor a E t s*eigenfunction a k t),integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
  apply (eq_div_iff (energy_gap_pos ha hE k).ne').mpr
  simpa only [mul_comm] using energyGreenFactor_coefficient ha hE hs k

/-- The full actual reference Green series equals its true selected-solution factor in every continuous row with an interior source.
Use: energyGreen_factorization adds the genuine boundary sources and proves the source's complete zero-energy Green identity.
Article: jacobi, Proposition C.4.
Proof: expand the actual selected row in the already proved complete original Hilbert basis. Its computed coefficients match the true continuous Green norm series term by term. Injectivity of the original continuous L2 embedding gives pointwise equality of the same continuous rows. -/
theorem energyGreen_factorization_interior {a E s : ℝ} (ha : -1<a)
    (hE : E<eigenvalue a 0) (hs : s∈Ioo (0:ℝ) 1) (t : Interval) :
    energyGreenKernel a E t s=energyGreenFactor a E t s := by
  -- The same true continuous functions are compared first in L2, then pointwise.
  let g := energyGreenFactorRow a E ha s hs
  let L := ContinuousMap.toLp (𝕜 := ℝ) (p := 2) (E := ℝ) (α := Interval) volume
  have hb := reference_vector_expansion a ha (L g)
  have hterms (k : ℕ) : L (energyGreenRowTerm a E ha k s)=
      (referenceCoefficient a k (L g)/norming a k) • waveVector a ha k := by
    rw [energyGreenRowTerm_toLp,energyGreenFactor_referenceCoefficient ha hE hs]
    congr 1
    field_simp [(norming_pos ha k).ne',(energy_gap_pos ha hE k).ne']
  have hactual : HasSum (fun k : ℕ => L (energyGreenRowTerm a E ha k s)) (L g) := by
    simpa only [hterms] using hb
  have hsum := energyGreenRowTerm_summable ha hE ⟨hs.1.le,hs.2.le⟩
  have hcontinuous := L.hasSum hsum.hasSum
  have hrows : (∑' k : ℕ,energyGreenRowTerm a E ha k s)=g :=
    continuous_toLp_injective (hcontinuous.unique hactual)
  have hev : (∑' k : ℕ,energyGreenRowTerm a E ha k s) t=energyGreenKernel a E t s :=
    (ContinuousMap.evalCLM ℝ t).map_tsum hsum
  rw [← hev,hrows]
  rfl

/-- The actual Green kernel vanishes on the two physical boundary source rows.
Use: energyGreen_factorization includes every genuine boundary point in the full original square.
Article: jacobi, Proposition C.4.
Proof: each original eigenfunction vanishes at both endpoints, hence every actual spectral summand does. -/
theorem energyGreenKernel_boundary {a : ℝ} (ha : -1<a) (E t : ℝ) :
    energyGreenKernel a E t 0=0 ∧ energyGreenKernel a E t 1=0 := by
  constructor <;> simp only [energyGreenKernel,energyGreenTerm,
    (eigenfunction_properties ha _).2.1,(eigenfunction_properties ha _).2.2,
    mul_zero,zero_div,tsum_zero]

/-- The original spectral Green kernel equals the exact selected left/right factor on the entire closed unit square.
Use: the E=0 specialization proves Appendix C.5's full factorization, rather than only the different c_0 formula used earlier for F.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
Proof: the genuine complete-basis argument handles interior sources. At source zero or one, both the original spectral series and the actual selected factor vanish by their proved endpoint values. -/
theorem energyGreen_factorization {a E t s : ℝ} (ha : -1<a) (hE : E<eigenvalue a 0)
    (ht : t∈Icc (0:ℝ) 1) (hs : s∈Icc (0:ℝ) 1) :
    energyGreenKernel a E t s=energyGreenFactor a E t s := by
  -- Endpoint cases retain the source's original totalized selected formula as well as its continuous representative.
  by_cases hs0 : s=0
  · subst s
    rw [(energyGreenKernel_boundary ha E t).1,energyGreenFactor,
      min_eq_right ht.1,max_eq_left ht.1]
    simp only [realSolution,solution_zero ha,Complex.zero_re,zero_mul,zero_div]
  by_cases hs1 : s=1
  · subst s
    rw [(energyGreenKernel_boundary ha E t).2,energyGreenFactor,
      min_eq_left ht.2,max_eq_right ht.2,sub_self]
    simp only [realSolution,solution_zero ha,Complex.zero_re,mul_zero,zero_div]
  exact energyGreen_factorization_interior ha hE
    ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0),lt_of_le_of_ne hs.2 hs1⟩ ⟨t,ht⟩

/-- The original selected-solution factor is jointly continuous up to every boundary point of the full physical square.
Use: completes the boundary regularity assertion of the zero-energy Green lemma without a separate unproved opposite-end singular expansion.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
Proof: on this square the genuine factor equals the independently proved uniformly convergent original continuous spectral series. -/
theorem energyGreenFactor_continuousOn_square {a E : ℝ} (ha : -1<a)
    (hE : E<eigenvalue a 0) :
    ContinuousOn (fun p : ℝ × ℝ => energyGreenFactor a E p.1 p.2)
      (Icc (0:ℝ) 1×ˢIcc (0:ℝ) 1) :=
  (energyGreenKernel_continuousOn ha hE).congr
    (fun _p hp => (energyGreen_factorization ha hE hp.1 hp.2).symm)

end
end jacobi.Reference
