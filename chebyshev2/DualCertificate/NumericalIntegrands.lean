import chebyshev2.DualCertificate.ObservationContinuity
import chebyshev2.DualCertificate.PriceCost

/-!
Article: chebyshev2, Lemma 16.
Actual compact integrands for Table 2 and (34).
Result: `chebyshev2.DualCertificate.Data.price_cost_integrands` supplies the stated article
conclusion.
-/
namespace chebyshev2.DualCertificate.NormalizedCalibration
noncomputable section
open Set MeasureTheory Real chebyshev2.Calibration chebyshev2.Comparison
open scoped ContDiff
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable (N : chebyshev2.DualCertificate.NormalizedCalibration) {κ : ℝ} (hκ : 0<κ)

/--
Defines `massIntegrand` of type `ℝ` by `(t*N.root κ t)^2*N.velocity κ t`.

Use: `chebyshev2.DualCertificate.NormalizedCalibration.massIntegrand_smooth` uses this
definition to establish smoothness to the stated order: `ContDiffOn ℝ ∞ (N.massIntegrand (κ :=
κ)) (Icc (0:ℝ) 1)`.

Article: chebyshev2, Lemma 16.
-/
def massIntegrand (t : ℝ) : ℝ := (t*N.root κ t)^2*N.velocity κ t

/--
Defines `HIntegrand` of type `ℝ` by `N.filter hκ s t*N.velocity κ t`.

Use: `chebyshev2.DualCertificate.NormalizedCalibration.HIntegrand_smooth` uses this
definition to establish smoothness to the stated order: `ContDiffOn ℝ ∞ (N.HIntegrand hκ s)
(Icc (0:ℝ) 1)`.

Article: chebyshev2, Lemma 16.
-/
def HIntegrand (s t : ℝ) : ℝ := N.filter hκ s t*N.velocity κ t

/--
Defines `SIntegrand` of type `ℝ` by `(N.linear hκ t)^2*N.velocity κ t`.

Use: `chebyshev2.DualCertificate.NormalizedCalibration.SIntegrand_smooth` uses this
definition to establish smoothness to the stated order: `ContDiffOn ℝ ∞ (N.SIntegrand hκ) (Icc
(0:ℝ) 1)`.

Article: chebyshev2, Lemma 16.
-/
def SIntegrand (t : ℝ) : ℝ := (N.linear hκ t)^2*N.velocity κ t

/--
Defines `priceIntegrand` of type `ℝ` by `3*t^2*(t*N.root κ t)*((intercept:ℝ)+(slope:ℝ)*t)`.

Use: `chebyshev2.DualCertificate.Data.price_cost_integrands` rewrites with this definition
to establish the identity stated in that declaration.

Article: chebyshev2, Lemma 16 via
`chebyshev2.DualCertificate.Data.price_cost_integrands`.
-/
def priceIntegrand (intercept slope : ℚ) (t : ℝ) : ℝ :=
  3*t^2*(t*N.root κ t)*((intercept:ℝ)+(slope:ℝ)*t)

include hκ in
/--
Smoothness to the stated order: `ContDiffOn ℝ ∞ (N.massIntegrand (κ := κ)) (Icc (0:ℝ) 1)`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 16.

Proof: Use the identities/estimates
`chebyshev2.DualCertificate.NormalizedCalibration.root_smooth_fixed`,
`chebyshev2.DualCertificate.NormalizedCalibration.velocity_smooth` with the arguments shown
in the proof.
-/
theorem massIntegrand_smooth : ContDiffOn ℝ ∞ (N.massIntegrand (κ := κ)) (Icc (0:ℝ) 1) :=
  ((contDiffOn_id.mul (N.root_smooth_fixed hκ)).pow 2).mul (N.velocity_smooth hκ)

/--
Smoothness to the stated order: `ContDiffOn ℝ ∞ (N.HIntegrand hκ s) (Icc (0:ℝ) 1)`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 16.

Proof: Use the identities/estimates
`chebyshev2.DualCertificate.NormalizedCalibration.filter_smooth`,
`chebyshev2.DualCertificate.NormalizedCalibration.velocity_smooth` with the arguments shown
in the proof.
-/
theorem HIntegrand_smooth {s : ℝ} (hs : 0≤s) :
    ContDiffOn ℝ ∞ (N.HIntegrand hκ s) (Icc (0:ℝ) 1) :=
  (N.filter_smooth hκ hs).mul (N.velocity_smooth hκ)

/--
Smoothness to the stated order: `ContDiffOn ℝ ∞ (N.SIntegrand hκ) (Icc (0:ℝ) 1)`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 16.

Proof: Use the identities/estimates
`chebyshev2.DualCertificate.NormalizedCalibration.linear_smooth`,
`chebyshev2.DualCertificate.NormalizedCalibration.velocity_smooth` with the arguments shown
in the proof.
-/
theorem SIntegrand_smooth : ContDiffOn ℝ ∞ (N.SIntegrand hκ) (Icc (0:ℝ) 1) :=
  ((N.linear_smooth hκ).pow 2).mul (N.velocity_smooth hκ)

include hκ in
/--
Smoothness to the stated order: `ContDiffOn ℝ ∞ (N.priceIntegrand (κ := κ) intercept slope)
(Icc (0:ℝ) 1)`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 16.

Proof: Use the identities/estimates
`chebyshev2.DualCertificate.NormalizedCalibration.root_smooth_fixed` with the arguments
shown in the proof.
-/
theorem priceIntegrand_smooth (intercept slope : ℚ) :
    ContDiffOn ℝ ∞ (N.priceIntegrand (κ := κ) intercept slope) (Icc (0:ℝ) 1) := by
  unfold priceIntegrand
  exact ((contDiffOn_const.mul (contDiffOn_id.pow 2)).mul
    (contDiffOn_id.mul (N.root_smooth_fixed hκ))).mul (by fun_prop)

 /--
Exact identity `N.H hκ s=2*(∫ t in Icc (0:ℝ) 1,N.HIntegrand hκ s t)+log (1+N.filter hκ s 1)`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 16.

Proof: The identity follows by unfolding the definitions; no estimate or limiting argument is
involved.
-/
theorem H_integrand_identity (s : ℝ) :
    N.H hκ s=2*(∫ t in Icc (0:ℝ) 1,N.HIntegrand hκ s t)+log (1+N.filter hκ s 1) := rfl

 /--
Exact identity `N.S hκ=2*(∫ t in Icc (0:ℝ) 1,N.SIntegrand hκ t)+(N.linear hκ 1)^2`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 16.

Proof: The identity follows by unfolding the definitions; no estimate or limiting argument is
involved.
-/
theorem S_integrand_identity :
    N.S hκ=2*(∫ t in Icc (0:ℝ) 1,N.SIntegrand hκ t)+(N.linear hκ 1)^2 := rfl

variable (hΓ : ∀ q∈Icc (0:ℝ) 2,N.calibration.Gamma (2-q)=N.calibration.Gamma q)

include hΓ in
/--
Exact identity `(∫ x,N.calibration.comparisonDensity hκ x)=2*(∫ t in Icc (0:ℝ)
1,N.massIntegrand (κ := κ) t)`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 16.

Proof: Use the identities/estimates
`chebyshev2.PrescribedSpeed.SpeedData.density_integrable`,
`chebyshev2.Calibration.Data.comparisonDensity_reflection`,
`chebyshev2.Comparison.halfLine_eq_support_interval` with the arguments shown in the proof.
-/
theorem mass_integrand_identity :
    (∫ x,N.calibration.comparisonDensity hκ x)=2*(∫ t in Icc (0:ℝ) 1,N.massIntegrand (κ := κ) t) := by
  -- Use the identities/estimates
  -- `chebyshev2.PrescribedSpeed.SpeedData.density_integrable`,
  -- `chebyshev2.Calibration.Data.comparisonDensity_reflection`,
  -- `chebyshev2.Comparison.halfLine_eq_support_interval` with the arguments shown in the
  -- proof.
  let C := N.calibration
  -- Establish hi as the integrability justification for the later integral estimates or
  -- changes of order.
  have hi : Integrable (C.comparisonDensity hκ) := (C.comparisonSpeed hκ).density_integrable hκ
  have hs : (∫ x in Iic (0:ℝ),C.comparisonDensity hκ x)=
      ∫ x in Ioi (0:ℝ),C.comparisonDensity hκ x := by
    have h := integral_comp_neg_Iic (0:ℝ) (C.comparisonDensity hκ)
    simp only [neg_zero,C.comparisonDensity_reflection hκ hΓ] at h
    exact h
  have hm : (∫ x,C.comparisonDensity hκ x)=2*(∫ x in Iic (0:ℝ),C.comparisonDensity hκ x) := by
    rw [← intervalIntegral.integral_Iic_add_Ioi hi.integrableOn hi.integrableOn (b := 0),← hs]
    ring
  rw [hm,halfLine_eq_support_interval hi ((C.comparisonSpeed hκ).X 0)]
  · rw [N.compact_integral hκ (C.comparisonDensity hκ)]
    congr 1
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    change C.comparisonDensity hκ (N.X hκ t)*N.velocity κ t=_
    rw [C.comparisonDensity_formula hκ]
    change (C.amplitude κ ((C.comparisonSpeed hκ).q ((C.comparisonSpeed hκ).X (t^3))))^2*_= _
    rw [(C.comparisonSpeed hκ).q_X (show t^3∈Icc (0:ℝ) 2 from
      ⟨(cube_mem ht).1,(cube_mem ht).2.trans (by norm_num)⟩),N.root_amplitude hκ ht]
    rfl
  · intro x hx
    exact (C.comparisonSpeed hκ).density_zero_outside κ (fun h => (not_lt_of_ge hx) h.1)

end
end chebyshev2.DualCertificate.NormalizedCalibration

namespace chebyshev2.DualCertificate.Data
noncomputable section
open Set MeasureTheory chebyshev2.Calibration chebyshev2.Residual
set_option autoImplicit false

 /--
The precise assertion is `priceCost κ (D.τ:ℝ) (D.price hκ).value= ((∑ i,∫ t in Icc ((D.cells
Side.left).lo i:ℝ) ((D.cells Side.left).hi i:ℝ), D.normalization.priceIntegrand (κ := κ)
((D.cells Side.left).intercept i) ((D.cells Side.left).slope i) t)+ (∑ i,∫ t in Icc ((D.cells
Side.right).lo i:ℝ) ((D.cells Side.right).hi i:ℝ), D.normalization.priceIntegrand (κ := κ)
((D.cells Side.right).intercept i) ((D.cells Side.right).slope i) t))/κ+ (D.τ:ℝ)*(1-∫
x,D.calibration.comparisonDensity hκ x)`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev2, Lemma 16.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem price_cost_integrands (D : chebyshev2.DualCertificate.Data) {κ : ℝ} (hκ : 0<κ) :
    priceCost κ (D.τ:ℝ) (D.price hκ).value=
      ((∑ i,∫ t in Icc ((D.cells Side.left).lo i:ℝ) ((D.cells Side.left).hi i:ℝ),
        D.normalization.priceIntegrand (κ := κ) ((D.cells Side.left).intercept i)
          ((D.cells Side.left).slope i) t)+
       (∑ i,∫ t in Icc ((D.cells Side.right).lo i:ℝ) ((D.cells Side.right).hi i:ℝ),
        D.normalization.priceIntegrand (κ := κ) ((D.cells Side.right).intercept i)
          ((D.cells Side.right).slope i) t))/κ+
        (D.τ:ℝ)*(1-∫ x,D.calibration.comparisonDensity hκ x) := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  have he (side : Side) (i : Fin (D.cells side).count) :
      (fun t => 3*t^3*D.normalization.root κ t*(D.cells side).affine i t)=
      D.normalization.priceIntegrand (κ := κ) ((D.cells side).intercept i)
        ((D.cells side).slope i) := by
    funext t
    simp only [NormalizedCalibration.priceIntegrand,Cells.affine]
    ring
  simpa only [he] using D.price_cost_cells hκ

end
end chebyshev2.DualCertificate.Data
