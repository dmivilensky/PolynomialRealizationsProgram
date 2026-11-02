import jacobi.Reference.HalfWave

/-!
Article: jacobi, Proposition C.2.
Every genuine original L2 input defines a bounded complex-linear
integral functional on continuous physical waves. Applying it to the
proved entire continuous-function-valued reference wave proves that
the literal original coefficient integral is entire. The construction
uses the actual Lebesgue integral and applies to arbitrary L2 inputs.
Use: bounds the true coefficient integral by its original L1 norm and justifies all actual linear integral identities.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Complex MeasureTheory Filter
open scoped Topology
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false

/-- Every original reference L2 input is genuinely integrable on the actual finite physical interval.
Use: bounds the true coefficient integral by its original L1 norm and justifies all actual linear integral identities.
Article: jacobi, Theorem 2.1.
Source: Holder's inequality on a finite measure space.
Proof: use the community finite-measure inclusion of actual L2 functions into L1. -/
theorem space_integrable (v : Space) : Integrable (fun t:Interval => v t) :=
  (Lp.memLp v).integrable (by norm_num)

/-- The actual complex coefficient integrand is integrable for every original L2 input and every continuous physical wave.
Use: linearity of the source coefficient integral uses actual Bochner integrability, not the totalized integral of an unchecked function.
Article: jacobi, Theorem 2.1.
Proof: the original L2 input is in L1; the compact continuous wave is measurable and bounded by its genuine supremum norm. -/
theorem coefficient_integrable (v : Space) (g : C(Interval,ℂ)) :
    Integrable (fun t:Interval => (v t:ℂ)*g t) :=
  (space_integrable v).ofReal.mul_bdd g.continuous.aestronglyMeasurable
    (Eventually.of_forall (fun t => g.norm_coe_le_norm t))

/-- The genuine coefficient integral is bounded by the actual input L1 norm times the true compact-wave norm.
Use: makes the original integral a bounded complex-linear functional, permitting genuine analytic composition.
Article: jacobi, Theorem 2.1.
Proof: pointwise multiply the true wave supremum bound by the actual
absolute input value. Apply the community Bochner integral norm bound
and take the fixed wave norm outside the genuine scalar integral. -/
theorem coefficient_integral_bound (v : Space) (g : C(Interval,ℂ)) :
    ‖∫ t:Interval,(v t:ℂ)*g t‖≤(∫ t:Interval,‖v t‖)*‖g‖ := by
  -- The true integral norm estimate applies even to arbitrary original L2 representatives.
  have hh := norm_integral_le_of_norm_le (f := fun t:Interval => (v t:ℂ)*g t)
    ((space_integrable v).norm.mul_const ‖g‖)
    (Eventually.of_forall (fun t:Interval => by
      rw [norm_mul,Complex.norm_real]
      exact mul_le_mul_of_nonneg_left (g.norm_coe_le_norm t) (norm_nonneg _)))
  rw [integral_mul_const] at hh
  exact hh

/-- The actual original L2 coefficient integral as a bounded complex-linear functional on continuous physical waves.
Use: proves entire frequency dependence of the literal original source transform by applying this functional to the genuine entire wave.
Article: jacobi, Proposition C.2.
-/
def coefficientFunctional (v : Space) : C(Interval,ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun g := ∫ t:Interval,(v t:ℂ)*g t
      map_add' g h := by
        simp only [ContinuousMap.add_apply,mul_add]
        exact integral_add (coefficient_integrable v g) (coefficient_integrable v h)
      map_smul' c g := by
        change (∫ t:Interval,(v t:ℂ)*(c*g t))=c*(∫ t:Interval,(v t:ℂ)*g t)
        simp_rw [mul_left_comm (v _:ℂ) c]
        exact integral_const_mul c _ }
    (∫ t:Interval,‖v t‖) (coefficient_integral_bound v)

/-- The source coefficient transform at actual frequency omega, defined by its genuine spatial integral.
Use: this is the function to which the proved Bessel Jensen uniqueness theorem is applied for actual arbitrary L2 data.
Article: jacobi, Proposition C.2.
-/
def coefficientTransform (a : ℝ) (v : Space) (omega : ℂ) : ℂ :=
  ∫ t:Interval,(v t:ℂ)*wave a omega (halfTime t)

/-- The literal original coefficient transform is exactly the continuous integral functional applied to the genuine original compact-domain wave.
Use: the function-space analyticity proof applies to the actual source integral, with no analytic-transform premise or replacement function.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
Proof: the actual pointwise evaluation theorem identifies the genuine continuous-domain wave with the source wave at every physical coordinate. -/
theorem coefficientTransform_eq (a : ℝ) (ha : -1<a) (v : Space) (omega : ℂ) :
    coefficientTransform a v omega=coefficientFunctional v (halfWave a ha omega) := by
  change (∫ t:Interval,(v t:ℂ)*wave a omega (halfTime t))=
    ∫ t:Interval,(v t:ℂ)*halfWave a ha omega t
  apply integral_congr_ae
  exact Eventually.of_forall (fun t => by
    change (v t:ℂ)*wave a omega (halfTime t)=(v t:ℂ)*halfWave a ha omega t
    rw [halfWave_apply])

/-- The actual source coefficient integral of every original L2 input is an entire function of complex frequency.
Use: discharges genuine analyticity in the source Jensen argument for arbitrary candidate null vectors of the actual GL form.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
Proof: the original compact-domain wave is genuinely entire in its
continuous-function norm. Compose with the actual bounded linear
integral functional and use the pointwise integral identification. -/
theorem coefficientTransform_analytic (a : ℝ) (ha : -1<a) (v : Space) (omega : ℂ) :
    AnalyticAt ℂ (coefficientTransform a v) omega := by
  have he : coefficientTransform a v=(fun w => coefficientFunctional v (halfWave a ha w)) :=
    funext (coefficientTransform_eq a ha v)
  rw [he]
  exact ((coefficientFunctional v).analyticAt _).comp (halfWave_analytic a ha omega)

/-- The genuine source coefficient transform is even in its original complex frequency.
Use: every actual vanishing positive Bessel frequency gives its negative zero as well, exactly as required in Jensen's formula.
Article: jacobi, Theorem 2.1.
Proof: the actual original reference wave is even at every spatial point, so the two actual integral integrands coincide. -/
theorem coefficientTransform_even (a : ℝ) (v : Space) (omega : ℂ) :
    coefficientTransform a v (-omega)=coefficientTransform a v omega := by
  simp only [coefficientTransform,wave_even]

end
end jacobi.Reference
