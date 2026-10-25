import chebyshev2.Comparison.RightFilters
import chebyshev2.Filters.JostFunction

/-!
Article: chebyshev2, Lemma 11.
The right Jost solution and its actual Fredholm growing coefficient in Lemma 11.
Result: `chebyshev2.Calibration.Data.rightJost_left_expansion` supplies the stated article
conclusion.
-/
namespace chebyshev2.Calibration.Data
noncomputable section
open Set MeasureTheory Filter Real chebyshev2.PrescribedSpeed chebyshev2.GroundState chebyshev2.Filters chebyshev2.Continuum
open scoped Topology
set_option backward.isDefEq.respectTransparency false
variable (C : chebyshev2.Calibration.Data) {κ : ℝ} (hκ : 0 < κ)

/--
Defines `rightJost` of type `ℝ` by `jostFunction s (reflected (C.comparisonDensity hκ)) (-x)`.

Use: `chebyshev2.Calibration.Data.rightFilter_jost_quotient` uses this definition to
establish the precise assertion is `C.rightFilter hκ s q= -C.rightJostSlope hκ s
((C.comparisonSpeed hκ).X q)/ C.rightJost hκ s ((C.comparisonSpeed hκ).X q)-1`.

Article: chebyshev2, Lemma 11 via `chebyshev2.Calibration.Data.rightJost_left_expansion`.
-/
def rightJost (s x : ℝ) : ℝ := jostFunction s (reflected (C.comparisonDensity hκ)) (-x)
/--
Defines `rightJostSlope` of type `ℝ` by `-jostFunctionSlope s (reflected (C.comparisonDensity
hκ)) (-x)`.

Use: `chebyshev2.Calibration.Data.rightFilter_jost_quotient` uses this definition to
establish the precise assertion is `C.rightFilter hκ s q= -C.rightJostSlope hκ s
((C.comparisonSpeed hκ).X q)/ C.rightJost hκ s ((C.comparisonSpeed hκ).X q)-1`.

Article: chebyshev2, Lemma 11.
-/
def rightJostSlope (s x : ℝ) : ℝ := -jostFunctionSlope s (reflected (C.comparisonDensity hκ)) (-x)

/--
The stated quantitative bound `0 < C.rightJost hκ s x`.

Use: a standalone supporting bound for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 11.

Proof: Use the identities/estimates `chebyshev2.Filters.jost_positive`,
`chebyshev2.Filters.reflected_integrable`,
`chebyshev2.PrescribedSpeed.SpeedData.density_integrable` with the arguments shown in the
proof.
-/
theorem rightJost_positive {s : ℝ} (hs : 0 ≤ s) (x : ℝ) : 0 < C.rightJost hκ s x :=
  mul_pos (exp_pos _) (jost_positive
    (reflected_integrable ((C.comparisonSpeed hκ).density_integrable hκ))
    (reflected_nonneg ((C.comparisonSpeed hκ).density_nonneg hκ)) hs _)

/--
The actual derivative at the stated point: `HasDerivAt (C.rightJost hκ s) (C.rightJostSlope hκ
s x) x`.

Use: a standalone supporting derivative formula for the article chain below; no retained
declaration currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 11.

Proof: Use the identities/estimates `chebyshev2.Filters.jostFunction_hasDerivAt`,
`chebyshev2.Filters.reflected_integrable`,
`chebyshev2.PrescribedSpeed.SpeedData.density_integrable` with the arguments shown in the
proof.
-/
theorem rightJost_derivative {s : ℝ} (hs : 0 ≤ s) (x : ℝ) :
    HasDerivAt (C.rightJost hκ s) (C.rightJostSlope hκ s x) x := by
  -- Use the identities/estimates `chebyshev2.Filters.jostFunction_hasDerivAt`,
  -- `chebyshev2.Filters.reflected_integrable`,
  -- `chebyshev2.PrescribedSpeed.SpeedData.density_integrable` with the arguments shown in
  -- the proof.
  have h := (jostFunction_hasDerivAt
    (reflected_integrable ((C.comparisonSpeed hκ).density_integrable hκ))
    (reflected_nonneg ((C.comparisonSpeed hκ).density_nonneg hκ)) hs (-x)).comp x (hasDerivAt_neg x)
  convert h using 1
  · rfl
  · dsimp only [rightJostSlope,comparisonDensity]
    ring

/--
The actual derivative at the stated point: `HasDerivAt (C.rightJostSlope hκ s)
((1+s*C.comparisonDensity hκ x)*C.rightJost hκ s x) x`.

Use: a standalone supporting derivative formula for the article chain below; no retained
declaration currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 11.

Proof: Use the identities/estimates `chebyshev2.Filters.reflected_integrable`,
`chebyshev2.PrescribedSpeed.SpeedData.density_integrable`,
`chebyshev2.Filters.reflected_nonneg` with the arguments shown in the proof.
-/
theorem rightJost_ode {s : ℝ} (hs : 0 ≤ s) (x : ℝ) :
    HasDerivAt (C.rightJostSlope hκ s)
      ((1+s*C.comparisonDensity hκ x)*C.rightJost hκ s x) x := by
  -- Use the identities/estimates `chebyshev2.Filters.reflected_integrable`,
  -- `chebyshev2.PrescribedSpeed.SpeedData.density_integrable`,
  -- `chebyshev2.Filters.reflected_nonneg` with the arguments shown in the proof.
  let mr := reflected (C.comparisonDensity hκ)
  have hm := reflected_integrable ((C.comparisonSpeed hκ).density_integrable hκ)
  have hn := reflected_nonneg ((C.comparisonSpeed hκ).density_nonneg hκ)
  have hc := reflected_continuous (C.comparisonDensity_continuous hκ)
  -- Establish continuity hy before using the function at limits or in calculus arguments.
  have hy : Continuous (jostFunction s mr) := by
    exact continuous_exp.mul (jost_continuous hm hn hs)
  have hd (t : ℝ) := locallyAC_hasDerivAt_of_continuous
    (jostFunctionSlope_locallyAC hm hn hs) (jostFunction_ode hm hn hs)
    ((continuous_const.add (continuous_const.mul hc)).mul hy) t
  have h := (hd (-x)).comp x (hasDerivAt_neg x) |>.neg
  convert h using 1
  · rfl
  · dsimp only [mr,reflected,neg_neg,rightJost,comparisonDensity]
    ring_nf

/--
The precise assertion is `C.rightFilter hκ s q= -C.rightJostSlope hκ s ((C.comparisonSpeed
hκ).X q)/ C.rightJost hκ s ((C.comparisonSpeed hκ).X q)-1`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 11.

Proof: Use the identities/estimates `chebyshev2.Filters.nonlinear_jostFunction_quotient`,
`chebyshev2.Filters.reflected_integrable`,
`chebyshev2.PrescribedSpeed.SpeedData.density_integrable` with the arguments shown in the
proof.
-/
theorem rightFilter_jost_quotient {s : ℝ} (hs : 0 ≤ s) (q : ℝ) :
    C.rightFilter hκ s q=
      -C.rightJostSlope hκ s ((C.comparisonSpeed hκ).X q)/
        C.rightJost hκ s ((C.comparisonSpeed hκ).X q)-1 := by
  -- Use the identities/estimates `chebyshev2.Filters.nonlinear_jostFunction_quotient`,
  -- `chebyshev2.Filters.reflected_integrable`,
  -- `chebyshev2.PrescribedSpeed.SpeedData.density_integrable` with the arguments shown in
  -- the proof.
  have h := nonlinear_jostFunction_quotient
    (reflected_integrable ((C.comparisonSpeed hκ).density_integrable hκ))
    (reflected_nonneg ((C.comparisonSpeed hκ).density_nonneg hκ)) hs
    (-((C.comparisonSpeed hκ).X q))
  change C.rightFilter hκ s q=_ at h
  simpa only [rightJostSlope,rightJost,neg_neg,comparisonDensity] using h

/--
Exact identity `C.rightJost hκ s x=exp (-x)`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 11.

Proof: Use the identities/estimates
`chebyshev2.PrescribedSpeed.SpeedData.density_zero_outside`,
`chebyshev2.Filters.jost_left_of_density_zero`,
`chebyshev2.Filters.reflected_integrable` with the arguments shown in the proof.
-/
theorem rightJost_normalization {s : ℝ} (hs : 0 ≤ s) {x : ℝ}
    (hx : (C.comparisonSpeed hκ).X 2 ≤ x) : C.rightJost hκ s x=exp (-x) := by
  -- Use the identities/estimates
  -- `chebyshev2.PrescribedSpeed.SpeedData.density_zero_outside`,
  -- `chebyshev2.Filters.jost_left_of_density_zero`,
  -- `chebyshev2.Filters.reflected_integrable` with the arguments shown in the proof.
  have hz : ∀ t ≤ -x, reflected (C.comparisonDensity hκ) t=0 := by
    intro t ht
    change (C.comparisonSpeed hκ).density κ (-t)=0
    exact (C.comparisonSpeed hκ).density_zero_outside κ
      (fun h => (not_lt_of_ge (le_trans hx (by linarith))) h.2)
  change exp (-x)*jost s (reflected ((C.comparisonSpeed hκ).density κ)) (-x)=exp (-x)
  rw [jost_left_of_density_zero (reflected_integrable ((C.comparisonSpeed hκ).density_integrable hκ))
    (reflected_nonneg ((C.comparisonSpeed hκ).density_nonneg hκ)) hs (-x) hz,mul_one]

/--
Defines `rightJostDecayingCoefficient` of type `ℝ` by `-s/2*∫ t, exp (2*t)* (reflected
(C.comparisonDensity hκ) t*jost s (reflected (C.comparisonDensity hκ)) t)`.

Use: `chebyshev2.Calibration.Data.rightJost_left_expansion` uses this definition to
establish the identity stated in that declaration.

Article: chebyshev2, Lemma 11 via `chebyshev2.Calibration.Data.rightJost_left_expansion`.
-/
def rightJostDecayingCoefficient (s : ℝ) : ℝ := -s/2*∫ t, exp (2*t)*
  (reflected (C.comparisonDensity hκ) t*jost s (reflected (C.comparisonDensity hκ)) t)

/--
The precise assertion is `C.rightJost hκ s x= exp (logDeterminant (kernelEigenvalue
((C.comparisonSpeed hκ).density_integrable hκ) ((C.comparisonSpeed hκ).density_nonneg hκ))
s)*exp (-x)+ C.rightJostDecayingCoefficient hκ s*exp x`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev2, Lemma 11.

Proof: Use the identities/estimates
`chebyshev2.PrescribedSpeed.SpeedData.density_integrable`,
`chebyshev2.PrescribedSpeed.SpeedData.density_nonneg`,
`chebyshev2.PrescribedSpeed.SpeedData.density_zero_outside` with the arguments shown in the
proof.
-/
theorem rightJost_left_expansion {s : ℝ} (hs : 0 ≤ s) {x : ℝ}
    (hx : x ≤ (C.comparisonSpeed hκ).X 0) :
    C.rightJost hκ s x=
      exp (logDeterminant (kernelEigenvalue ((C.comparisonSpeed hκ).density_integrable hκ)
        ((C.comparisonSpeed hκ).density_nonneg hκ)) s)*exp (-x)+
          C.rightJostDecayingCoefficient hκ s*exp x := by
  -- Use the identities/estimates
  -- `chebyshev2.PrescribedSpeed.SpeedData.density_integrable`,
  -- `chebyshev2.PrescribedSpeed.SpeedData.density_nonneg`,
  -- `chebyshev2.PrescribedSpeed.SpeedData.density_zero_outside` with the arguments shown
  -- in the proof.
  have hz : ∀ t, -x<t → reflected (C.comparisonDensity hκ) t=0 := by
    intro t ht
    change (C.comparisonSpeed hκ).density κ (-t)=0
    exact (C.comparisonSpeed hκ).density_zero_outside κ (fun h =>
      (not_lt_of_ge (le_trans (by linarith : -t ≤ x) hx)) h.1)
  have h := jost_right_of_density_zero
    (reflected_integrable ((C.comparisonSpeed hκ).density_integrable hκ))
    (reflected_nonneg ((C.comparisonSpeed hκ).density_nonneg hκ)) hs (-x) hz
  have ht : transmission s (reflected ((C.comparisonSpeed hκ).density κ))=
      exp (logDeterminant (kernelEigenvalue ((C.comparisonSpeed hκ).density_integrable hκ)
        ((C.comparisonSpeed hκ).density_nonneg hκ)) s) := by
    rw [transmission_reflection ((C.comparisonSpeed hκ).density_integrable hκ)
      ((C.comparisonSpeed hκ).density_nonneg hκ) (C.comparisonDensity_continuous hκ) hs,
      ← log_transmission_eq_logDeterminant ((C.comparisonSpeed hκ).density_integrable hκ)
        ((C.comparisonSpeed hκ).density_nonneg hκ) hs]
    exact (exp_log (zero_lt_one.trans_le (transmission_ge_one
      ((C.comparisonSpeed hκ).density_integrable hκ) ((C.comparisonSpeed hκ).density_nonneg hκ) hs))).symm
  rw [ht,neg_neg] at h
  change C.rightJost hκ s x=_ at h
  rw [h]
  dsimp only [rightJostDecayingCoefficient,comparisonDensity]
  ring

end
end chebyshev2.Calibration.Data
