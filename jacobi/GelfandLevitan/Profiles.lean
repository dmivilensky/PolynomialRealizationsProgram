import jacobi.GelfandLevitan.SpatialSolution

/-!
Article: jacobi, Theorem 2.1.
The actual transformed real-energy solutions give the original Phi_k.
They are reflected from the physical half interval to the shared unit
interval exactly as in the article. Their continuity, nonnegativity
and reflection identity are proved directly for these constructed
functions. Their spectral norm bound and series are separate proofs.
Use: implements exactly the article's reflection extension Phi_k(1-t)=Phi_k(t).
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set jacobi.Reference
open scoped Topology

/-- The continuous folding of the original unit interval onto its physical left half.
Use: implements exactly the article's reflection extension Phi_k(1-t)=Phi_k(t).
Article: jacobi, Theorem 2.1.
-/
def physicalFold : C(Interval,HalfInterval) where
  toFun t := ⟨min (t:ℝ) (1-(t:ℝ)),
    ⟨le_min t.property.1 (sub_nonneg.mpr t.property.2),by
      linarith [min_le_left (t:ℝ) (1-(t:ℝ)),min_le_right (t:ℝ) (1-(t:ℝ))]⟩⟩
  continuous_toFun := (continuous_subtype_val.min (continuous_const.sub continuous_subtype_val)).subtype_mk _

/-- The genuine continuous spatial reflection of the original shared unit interval.
Use: expresses the exact source symmetry of each original spectral profile and their uniformly convergent sum.
Article: jacobi, Proposition C.4.
-/
def physicalReflection : C(Interval,Interval) where
  toFun t := ⟨1-(t:ℝ),⟨sub_nonneg.mpr t.property.2,by linarith [t.property.1]⟩⟩
  continuous_toFun := (continuous_const.sub continuous_subtype_val).subtype_mk _

/-- Folding preserves every original physical half-domain coordinate exactly.
Use: identifies the reflected whole-interval profile with the literal source formula on its defining left half.
Article: jacobi, Proposition 2.2.
Proof: a physical coordinate at most one half is at most its reflection, so the actual folding minimum is that coordinate. -/
theorem physicalFold_halfInclusion (t : HalfInterval) :
    physicalFold (halfInclusion t)=t := by
  apply Subtype.ext
  change min (t:ℝ) (1-(t:ℝ))=(t:ℝ)
  exact min_eq_left (by linarith [t.property.2])

/-- Folding the original unit coordinate is unchanged by its true source reflection.
Use: proves reflection symmetry for every constructed source spectral profile and their actual sum.
Article: jacobi, Theorem 2.1.
Proof: reflection interchanges the two entries of the actual minimum defining the physical folded coordinate. -/
theorem physicalFold_reflection (t : Interval) :
    physicalFold (physicalReflection t)=physicalFold t := by
  apply Subtype.ext
  change min (1-(t:ℝ)) (1-(1-(t:ℝ)))=min (t:ℝ) (1-(t:ℝ))
  rw [show 1-(1-(t:ℝ))=(t:ℝ) by ring,min_comm]

/-- The true real transformed solution as a continuous function on the physical half interval.
Use: defines the original source squared spectral profiles using the real value of the actual complex-energy solution.
Article: jacobi, Proposition 2.2.
-/
def realTransformedSolution (a : ℝ) (ha : -1<a) (E : ℝ) : C(HalfInterval,ℝ) where
  toFun t := (transformedSolution a ha t (E:ℂ)).re
  continuous_toFun := Complex.continuous_re.comp (transformedSolution_continuous a ha (E:ℂ))

/-- The real spatial transformed solution is exactly the real value of the actual complex-energy solution.
Use: the original squared profile uses the same actual u as the entire transformation construction, without discarding a possible imaginary component.
Article: jacobi, Theorem 2.1.
Proof: the proved real-energy identity makes the actual complex solution the inclusion of a real number; taking and reincluding its real part preserves that same value. -/
theorem realTransformedSolution_cast (a : ℝ) (ha : -1<a) (E : ℝ) (t : HalfInterval) :
    (realTransformedSolution a ha E t:ℂ)=transformedSolution a ha t (E:ℂ) := by
  change ((transformedSolution a ha t (E:ℂ)).re:ℂ)=transformedSolution a ha t (E:ℂ)
  rw [transformedSolution_real,Complex.ofReal_re]

/-- The original normalized squared spectral profile, with its actual reflection extension to the whole unit interval.
Use: the uniformly convergent original Lambda-weighted series defines phi_alpha and the actual persymmetric constant.
Article: jacobi, Proposition C.4.
-/
def spectralProfile (a : ℝ) (ha : -1<a) (k : ℕ) : C(Interval,ℝ) where
  toFun t := (normingRatio a ha k/norming a k)*
    (realTransformedSolution a ha (jacobi.Bessel.sigma a ha k) (physicalFold t))^2
  continuous_toFun := continuous_const.mul
    (((realTransformedSolution a ha (jacobi.Bessel.sigma a ha k)).continuous.comp physicalFold.continuous).pow 2)

/-- The reflected whole-interval profile restricts to exactly the original norming-weighted transformed solution square on the physical half interval.
Use: verifies the defining article-to-Lean profile formula before proving its uniform convergence and Green-diagonal identification.
Article: jacobi, Theorem 2.1.
Proof: the proved physical folding identity leaves the original half-domain coordinate unchanged in the actual profile definition. -/
theorem spectralProfile_half (a : ℝ) (ha : -1<a) (k : ℕ) (t : HalfInterval) :
    spectralProfile a ha k (halfInclusion t)=(normingRatio a ha k/norming a k)*
      (realTransformedSolution a ha (jacobi.Bessel.sigma a ha k) t)^2 := by
  change (normingRatio a ha k/norming a k)*
    (realTransformedSolution a ha (jacobi.Bessel.sigma a ha k) (physicalFold (halfInclusion t)))^2=_
  rw [physicalFold_halfInclusion]

/-- Every actual reflected source spectral profile vanishes at the original physical left endpoint.
Use: uniform convergence gives the original zero endpoint value of phi_alpha; reflection gives the corresponding right endpoint.
Article: jacobi, Proposition 2.2.
Proof: the exact half-domain profile formula contains the actual transformed solution at zero, already proved to vanish for every complex energy. -/
theorem spectralProfile_zero (a : ℝ) (ha : -1<a) (k : ℕ) :
    spectralProfile a ha k (halfInclusion halfZero)=0 := by
  rw [spectralProfile_half]
  change (normingRatio a ha k/norming a k)*
    ((transformedSolution a ha halfZero (jacobi.Bessel.sigma a ha k:ℂ)).re)^2=0
  rw [transformedSolution_zero,Complex.zero_re]
  ring

/-- Every original constructed squared spectral profile is nonnegative at every actual physical point.
Use: the original persymmetric profile series and its squared-integral constant have genuine nonnegative terms.
Article: jacobi, Proposition 2.2.
Proof: the original norming ratio and actual reference squared norm are positive; multiply their positive quotient by the actual real solution square. -/
theorem spectralProfile_nonneg (a : ℝ) (ha : -1<a) (k : ℕ) (t : Interval) :
    0≤spectralProfile a ha k t := by
  change 0≤(normingRatio a ha k/norming a k)*
    (realTransformedSolution a ha (jacobi.Bessel.sigma a ha k) (physicalFold t))^2
  exact mul_nonneg (div_pos (normingRatio_properties ha k).2 (norming_pos ha k)).le (sq_nonneg _)

/-- Each actual source spectral profile has exactly the article's reflection symmetry.
Use: the original uniformly convergent persymmetric profile and its integral constant retain the prescribed source normalization on both halves.
Article: jacobi, Theorem 2.1.
Proof: the actual folded coordinate is unchanged by reflection, so the defining original real solution square and its true spectral coefficient are unchanged. -/
theorem spectralProfile_reflection (a : ℝ) (ha : -1<a) (k : ℕ) (t : Interval) :
    spectralProfile a ha k (physicalReflection t)=spectralProfile a ha k t := by
  change (normingRatio a ha k/norming a k)*
    (realTransformedSolution a ha (jacobi.Bessel.sigma a ha k) (physicalFold (physicalReflection t)))^2=_
  rw [physicalFold_reflection]
  rfl

end
end jacobi.GelfandLevitan
