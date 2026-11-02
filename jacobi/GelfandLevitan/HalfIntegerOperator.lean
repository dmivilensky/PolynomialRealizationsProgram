import jacobi.GelfandLevitan.HalfInteger
import jacobi.GelfandLevitan.TargetSpectralOperator
import jacobi.GelfandLevitan.FullWaveMaps
import jacobi.Reference.Operator

/-!
Article: jacobi, Appendix C.2.
At alpha=±1/2 the actual full target basis equals the actual reference
basis, with the unchanged eigenvalue enumeration. Consequently H_alpha
and L_alpha are equal as full unbounded operators, including their entire
graph domains, rather than merely sharing finite eigenfunction formulas.
Use: half_integer_fullWaveMap identifies the actual normalized continuous target eigenfunctions, preserving their signs.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set MeasureTheory jacobi.Reference
open scoped Topology
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false

/-- The genuine full wave normalization reduces to the original reference normalization at both special orders.
Use: half_integer_fullWaveMap identifies the actual normalized continuous target eigenfunctions, preserving their signs.
Article: jacobi, Appendix C.2.
Proof: substitute the proved actual norming ratio one and cancel the genuine positive sqrt(2) factor. -/
theorem half_integer_targetWaveScale {a : ℝ} (ha : -1<a)
    (hs : a=(1/2:ℝ) ∨ a= -(1/2:ℝ)) (n : ℕ) :
    targetWaveScale a ha n=1/Real.sqrt (norming a n) := by
  rw [targetWaveScale,half_integer_normingRatio ha hs,Real.sqrt_one,mul_one,halfNormalization]
  field_simp

/-- At both special orders the actual continuous full target wave is exactly the original normalized reference eigenfunction on the whole closed physical interval.
Use: half_integer_fullTargetBasis identifies the actual original L2 quotient vectors before equating their full unbounded spectral operators.
Article: jacobi, Appendix C.2.
Proof: the proved actual transformation is the identity and the spectra coincide. On the second physical half the actual reference parity cancels the original reflection sign. The true normalization is the unchanged reference norm. -/
theorem half_integer_fullWaveMap {a : ℝ} (ha : -1<a)
    (hs : a=(1/2:ℝ) ∨ a= -(1/2:ℝ)) (n : ℕ) (t : Interval) :
    fullWaveMap a ha n t=eigenfunction a n (t:ℝ)/Real.sqrt (norming a n) := by
  -- The pointwise identity includes the original midpoint and endpoints; no representative is chosen from an L2 equivalence class.
  change targetWaveScale a ha n*(if (t:ℝ)≤1/2 then
    (transformedSolution a ha (halfClamp t) (jacobi.Bessel.sigma a ha n:ℂ)).re else
      (-1:ℝ)^n*(transformedSolution a ha (halfClamp (physicalReflection t)) (jacobi.Bessel.sigma a ha n:ℂ)).re)=_
  rw [half_integer_targetWaveScale ha hs,half_integer_spectra ha hs]
  simp only [half_integer_transformedSolution ha hs,solution_at_eigenvalue,Complex.ofReal_re]
  by_cases ht : (t:ℝ)≤1/2
  · rw [ite_eq_left ht]
    change (1/Real.sqrt (norming a n))*eigenfunction a n (min (t:ℝ) (1/2))=_
    rw [min_eq_left ht]
    ring
  · rw [ite_eq_right ht]
    change (1/Real.sqrt (norming a n))*((-1:ℝ)^n*eigenfunction a n (min (1-(t:ℝ)) (1/2)))=_
    rw [min_eq_left (by linarith : 1-(t:ℝ)≤1/2),eigenfunction_reflection ha]
    have hsign : ((-1:ℝ)^n)^2=1 := by rw [← pow_mul,Nat.mul_comm,pow_mul]; norm_num
    calc
      _ = (eigenfunction a n (t:ℝ)/Real.sqrt (norming a n))*((-1:ℝ)^n)^2 := by ring
      _ = _ := by rw [hsign,mul_one]

/-- The actual complete full target Hilbert basis equals the actual original reference basis at both special orders.
Use: half_integer_targetOperator proves equality of the genuine full unbounded spectral realizations and their entire domains.
Article: jacobi, Appendix C.2.
Proof: the genuine target and reference quotient vectors have the same independently proved actual continuous representatives. Equality almost everywhere identifies every basis vector, and extensionality identifies the complete Hilbert bases. -/
theorem half_integer_fullTargetBasis {a : ℝ} (ha : -1<a)
    (hs : a=(1/2:ℝ) ∨ a= -(1/2:ℝ)) : fullTargetBasis a ha=hilbertBasis a ha := by
  apply DFunLike.ext
  intro n
  apply Lp.ext
  filter_upwards [fullTargetBasis_wave_ae a ha n,hilbertBasis_ae a ha n] with t ht hr
  rw [ht,hr,half_integer_fullWaveMap ha hs]

/-- At each of the two actual half-integer orders, the genuine full target and reference unbounded operators are exactly equal, including their entire spectral graph domains.
Use: completes the literal special-order operator assertion accompanying general Proposition C.2; the already proved special profiles and constants therefore belong to the same actual H_alpha.
Article: jacobi, Appendix C.2.
Proof: the actual Hilbert bases coincide and the original sigma and tau sequences coincide pointwise. The same reused full unbounded-diagonal construction therefore gives equal partial linear operators. -/
theorem half_integer_targetOperator {a : ℝ} (ha : -1<a)
    (hs : a=(1/2:ℝ) ∨ a= -(1/2:ℝ)) : targetOperator a ha=referenceOperator a ha := by
  unfold targetOperator referenceOperator
  rw [half_integer_fullTargetBasis ha hs,half_integer_spectra ha hs]

end
end jacobi.GelfandLevitan
