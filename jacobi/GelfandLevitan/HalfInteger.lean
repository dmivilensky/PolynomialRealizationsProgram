import jacobi.Reference.HalfIntegerCharacteristics
import jacobi.GelfandLevitan.ExistenceUniqueness
import jacobi.GelfandLevitan.ProfileSeries

/-!
Article: jacobi, Proposition C.4.
For each of the two actual half-integer orders the original spectra
coincide in their original enumeration. Consequently the original
norming products are one, every original GL summand and F vanish,
the actual constructed K vanishes, and the actual transformed solution
equals its original reference solution at every complex energy.
The whole-interval reflected profiles are the true normalized
reference eigenfunction squares.
Use: half_integer_normingRatio evaluates the original infinite product without replacing its definition.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set MeasureTheory jacobi.Reference
set_option backward.isDefEq.respectTransparency false

/-- Every original norming factor is one at either special order.
Use: half_integer_normingRatio evaluates the original infinite product without replacing its definition.
Article: jacobi, Proposition C.4.
Proof: the actual spectra agree in their genuine enumeration. Off the
omitted diagonal their identical reference gaps are nonzero by strict ordering. -/
theorem half_integer_normingFactor {a : ℝ} (ha : -1<a)
    (hs : a=(1/2:ℝ) ∨ a= -(1/2:ℝ)) (k l : ℕ) : normingFactor a ha k l=1 := by
  rw [normingFactor,half_integer_spectra ha hs]
  by_cases hl : l=k
  · rw [ite_eq_left hl]
  · rw [ite_eq_right hl,div_self (sub_ne_zero.mpr ((eigenvalue_strictMono ha).injective.ne hl))]

/-- The original positive norming-ratio product is exactly one at either special order.
Use: half_integer_kernelTerm and half_integer_spectralProfile evaluate the actual GL data and profiles.
Article: jacobi, Proposition C.4.
Proof: every genuine factor in its defining convergent infinite product is one. -/
theorem half_integer_normingRatio {a : ℝ} (ha : -1<a)
    (hs : a=(1/2:ℝ) ∨ a= -(1/2:ℝ)) (k : ℕ) : normingRatio a ha k=1 := by
  simp only [normingRatio,half_integer_normingFactor ha hs,tprod_one]

/-- Every actual original GL summand vanishes at either special order.
Use: half_integer_kernel identifies the genuine complete source kernel as zero before evaluating its inverse construction.
Article: jacobi, Proposition C.4.
Proof: substitute the proved genuine spectral coincidence and original norming product value in the literal original summand. -/
theorem half_integer_kernelTerm {a : ℝ} (ha : -1<a)
    (hs : a=(1/2:ℝ) ∨ a= -(1/2:ℝ)) (k : ℕ) (t s : ℝ) : kernelTerm a ha k t s=0 := by
  simp only [kernelTerm,half_integer_normingRatio ha hs,half_integer_spectra ha hs,
    one_mul,sub_self,zero_div]

/-- The original complete GL kernel is zero at either special order, at every point of its definition.
Use: half_integer_transformationKernel proves the actual inverse GL construction is zero, without an additional uniqueness premise.
Article: jacobi, Proposition C.4.
Proof: every summand of the actual defining original series is zero. -/
theorem half_integer_kernel {a : ℝ} (ha : -1<a)
    (hs : a=(1/2:ℝ) ∨ a= -(1/2:ℝ)) (t s : ℝ) : kernel a ha t s=0 := by
  simp only [kernel,half_integer_kernelTerm ha hs,tsum_zero]

/-- The actual constructed transformation kernel vanishes identically at either special order.
Use: half_integer_transformedSolution removes the true transformation integral and fixes the special-case potential and midpoint identity in Proposition C.2.
Article: jacobi, Proposition C.4.
Proof: the actual pointwise GL equation becomes K(t,s)=0 because its original F and its whole integral term vanish. -/
theorem half_integer_transformationKernel {a : ℝ} (ha : -1<a)
    (hs : a=(1/2:ℝ) ∨ a= -(1/2:ℝ)) (t s : HalfInterval) :
    transformationKernel a ha t s=0 := by
  have h := transformationKernel_GL a ha t s
  simpa only [half_integer_kernel ha hs,mul_zero,integral_zero,add_zero] using h

/-- At either special order the actual transformed solution equals the original reference solution at every genuine spatial point and complex energy.
Use: identifies the actual special-case midpoint data, differential equation and whole-interval spectral profiles for Proposition C.2.
Article: jacobi, Proposition C.4.
Proof: the original transformation integral has the proved zero actual K, hence is zero. -/
theorem half_integer_transformedSolution {a : ℝ} (ha : -1<a)
    (hs : a=(1/2:ℝ) ∨ a= -(1/2:ℝ)) (t : HalfInterval) (z : ℂ) :
    transformedSolution a ha t z=solution a z (t:ℝ) := by
  simp only [transformedSolution_integral,half_integer_transformationKernel ha hs,
    Complex.ofReal_zero,zero_mul,integral_zero,add_zero]

/-- The actual reference eigenfunction square is unchanged by the original physical fold.
Use: half_integer_spectralProfile identifies the actual reflected profiles on the entire original interval, including the midpoint and both endpoints.
Article: jacobi, Proposition C.4.
Proof: the fold is either the original point or its reflection.
The proved actual reference parity has square one. -/
theorem eigenfunction_square_fold {a : ℝ} (ha : -1<a) (k : ℕ) (t : Interval) :
    (eigenfunction a k (physicalFold t:ℝ))^2=(eigenfunction a k (t:ℝ))^2 := by
  -- Squaring removes the original signed parity factor without changing the eigenfunction normalization.
  change (eigenfunction a k (min (t:ℝ) (1-(t:ℝ))))^2=_
  by_cases ht : (t:ℝ)≤1-(t:ℝ)
  · rw [min_eq_left ht]
  · rw [min_eq_right (le_of_not_ge ht),eigenfunction_reflection ha,mul_pow]
    have hsign : ((-1:ℝ)^k)^2=1 := by
      rw [← pow_mul,Nat.mul_comm,pow_mul]
      norm_num
    rw [hsign,one_mul]

/-- Every actual whole-interval reflected profile at either special order is the genuine normalized reference eigenfunction square.
Use: the special-case profile and constant reduce to the already constructed reference spectral realization, rather than to a separately chosen formal sine or Legendre series.
Article: jacobi, Proposition C.4.
Proof: the actual rho is one, sigma=tau and u=f. Reference spectral
specialization gives the original real eigenfunction; its square is unchanged by the actual physical fold. -/
theorem half_integer_spectralProfile {a : ℝ} (ha : -1<a)
    (hs : a=(1/2:ℝ) ∨ a= -(1/2:ℝ)) (k : ℕ) (t : Interval) :
    spectralProfile a ha k t=(eigenfunction a k (t:ℝ))^2/norming a k := by
  change normingRatio a ha k/norming a k*
    (transformedSolution a ha (physicalFold t) (jacobi.Bessel.sigma a ha k:ℂ)).re^2=_
  rw [half_integer_normingRatio ha hs,half_integer_spectra ha hs,
    half_integer_transformedSolution ha hs,solution_at_eigenvalue,Complex.ofReal_re,
    eigenfunction_square_fold ha]
  ring

end
end jacobi.GelfandLevitan
