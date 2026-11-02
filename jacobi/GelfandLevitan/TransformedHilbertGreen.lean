import jacobi.GelfandLevitan.TransformedBases
import jacobi.GelfandLevitan.TransformedGreenIdentity

/-!
Article: jacobi, Proposition 2.2.
The original full Green identity is expressed using the same genuine
Hilbert vectors as the two proved transformed bases. Consequently the
boundary states in each original parity class are collinear, with no
orthogonality or integral-identification premise supplied separately.
Use: transformedVector_inner_integral identifies the Hilbert basis pairings with the actual Green integrals in Proposition C.2.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference
open scoped Topology InnerProductSpace
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] transformedSolution

/-- The actual transformed half-space vector has the literal normalized-domain continuous u representative with genuine zero extension.
Use: transformedVector_inner_integral identifies the Hilbert basis pairings with the actual Green integrals in Proposition C.2.
Article: jacobi, Proposition C.2.
Proof: the actual vector is the original continuous-to-L2 half-projection of its genuine continuous real-energy transformed solution. -/
theorem transformedVector_ae (a : ℝ) (ha : -1<a) (E : ℝ) :
    (transformedVector a ha E:Space)=ᵐ[volume]
      (prefixSet (1/2)).indicator (transformedRealWave a ha E) :=
  halfProjection_toLp_ae (transformedRealWave a ha E)

/-- At a real energy the actual transformed solution equals the complex inclusion of its genuine real part.
Use: the original complex Green product integral is exactly the real Hilbert inner product in transformedVector_inner_integral.
Article: jacobi, Proposition C.2.
Proof: the actual original reference-plus-integral formula is already proved to be a real complex inclusion. -/
theorem transformedSolution_cast_re (a : ℝ) (ha : -1<a) (E : ℝ) (t : HalfInterval) :
    ((transformedSolution a ha t (E:ℂ)).re:ℂ)=transformedSolution a ha t (E:ℂ) := by
  rw [transformedSolution_real]
  rfl

/-- The original transformed Hilbert pairing is exactly the genuine complex Green product integral on the physical half interval.
Use: midpoint_hilbert_green and the actual two transformed bases determine the original midpoint boundary states.
Article: jacobi, Proposition C.2.
Proof: insert both genuine zero-extended continuous representatives in the original L2 integral. The same actual half indicator restricts the integral, and real-energy reality identifies the complex product. The proved original subtype-prefix identity gives the unchanged real interval integral. -/
theorem transformedVector_inner_integral (a : ℝ) (ha : -1<a) (E D : ℝ) :
    (inner ℝ (transformedVector a ha E) (transformedVector a ha D):ℂ)=
      ∫ r in (0:ℝ)..(1/2:ℝ),transformedSolution a ha (halfParameterClamp r) (E:ℂ)*
        transformedSolution a ha (halfParameterClamp r) (D:ℂ) := by
  -- Only almost-everywhere representatives of the original L2 vectors are used under integration.
  change (inner ℝ (transformedVector a ha E:Space) (transformedVector a ha D:Space):ℂ)=_
  rw [L2.inner_def,← integral_complex_ofReal,← prefix_integral
    (fun r => transformedSolution a ha (halfParameterClamp r) (E:ℂ)*
      transformedSolution a ha (halfParameterClamp r) (D:ℂ)) (by norm_num : (1/2:ℝ)∈Icc (0:ℝ) 1),
    ← integral_indicator (prefixSet_measurable (1/2))]
  apply integral_congr_ae
  filter_upwards [transformedVector_ae a ha E,transformedVector_ae a ha D] with r hE hD
  rw [hE,hD]
  by_cases hp : r∈prefixSet (1/2)
  · rw [indicator_of_mem hp,indicator_of_mem hp,indicator_of_mem hp]
    change (((transformedSolution a ha (halfClamp r) (D:ℂ)).re*
      (transformedSolution a ha (halfClamp r) (E:ℂ)).re:ℝ):ℂ)=_
    rw [Complex.ofReal_mul,transformedSolution_cast_re,transformedSolution_cast_re,halfParameterClamp_unit]
    ring
  · rw [indicator_of_notMem hp,indicator_of_notMem hp,indicator_of_notMem hp,
      inner_zero_left,Complex.ofReal_zero]

/-- The genuine original midpoint Green identity uses the actual half-interval Hilbert inner product.
Use: the independently proved transformed parity orthogonality gives the common boundary condition in each original parity class.
Article: jacobi, Proposition C.2.
Proof: substitute the independently proved true transformed Hilbert integral identity into the original full midpoint Green identity. -/
theorem midpoint_hilbert_green (a : ℝ) (ha : -1<a) (E D : ℝ) :
    ((E:ℂ)-(D:ℂ))*(inner ℝ (transformedVector a ha E) (transformedVector a ha D):ℂ)=
      midpointValue a ha (E:ℂ)*midpointSlope a ha (D:ℂ)-
        midpointSlope a ha (E:ℂ)*midpointValue a ha (D:ℂ) := by
  rw [transformedVector_inner_integral]
  exact midpoint_green_identity a ha (E:ℂ) (D:ℂ)

/-- All genuine midpoint boundary states within either original spectral parity class are collinear.
Use: together with nonvanishing of these actual states this supplies the common separated midpoint boundary condition in general Proposition C.2.
Article: jacobi, Proposition C.2.
Proof: distinct same-parity actual waves are orthogonal by the two proved transformed bases, so their genuine Green identity has zero left side. Equal indices have zero determinant algebraically. -/
theorem midpoint_parity_collinear (a : ℝ) (ha : -1<a) (p : Fin 2) (i j : ℕ) :
    midpointValue a ha (jacobi.Bessel.sigma a ha (parityIndex p i):ℂ)*
      midpointSlope a ha (jacobi.Bessel.sigma a ha (parityIndex p j):ℂ)-
    midpointSlope a ha (jacobi.Bessel.sigma a ha (parityIndex p i):ℂ)*
      midpointValue a ha (jacobi.Bessel.sigma a ha (parityIndex p j):ℂ)=0 := by
  by_cases hij : i=j
  · subst j
    ring
  · rw [← midpoint_hilbert_green,transformedVector_parity_orthogonal a ha p hij,
      Complex.ofReal_zero,mul_zero]

end
end jacobi.GelfandLevitan
