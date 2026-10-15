import «2610.05164v2».Comparison.ProfileFilters
import «2610.05164v2».Filters.JostFunction

/-!
Article: 2610.05164v2, Lemma 11.
The right Jost solution and its actual Fredholm growing coefficient in Lemma 11.
Result: `«2610.05164v2».Comparison.Profile.rightJost_ode` supplies the stated article conclusion.
-/
namespace «2610.05164v2».Comparison.Profile
noncomputable section
open Set MeasureTheory Filter Real «2610.05164v2».PrescribedSpeed «2610.05164v2».GroundState «2610.05164v2».Filters «2610.05164v2».Continuum
open scoped Topology
set_option backward.isDefEq.respectTransparency false
variable {κ : ℝ} (P : «2610.05164v2».Comparison.Profile κ) (hκ : 0 < κ)

/--
Defines `rightJost` of type `ℝ` by `jostFunction s (reflected (P.density hκ)) (-x)`.

Use: `«2610.05164v2».Comparison.Profile.rightFilter_jost_quotient` uses this definition to
establish the precise assertion is `P.rightFilter hκ s q= -P.rightJostSlope hκ s ((P.speedData
hκ).X q)/ P.rightJost hκ s ((P.speedData hκ).X q)-1`.

Article: 2610.05164v2, Lemma 11 via `«2610.05164v2».Comparison.Profile.rightJost_ode`.
-/
def rightJost (s x : ℝ) : ℝ := jostFunction s (reflected (P.density hκ)) (-x)
/--
Defines `rightJostSlope` of type `ℝ` by `-jostFunctionSlope s (reflected (P.density hκ)) (-x)`.

Use: `«2610.05164v2».Comparison.Profile.rightFilter_jost_quotient` uses this definition to
establish the precise assertion is `P.rightFilter hκ s q= -P.rightJostSlope hκ s ((P.speedData
hκ).X q)/ P.rightJost hκ s ((P.speedData hκ).X q)-1`.

Article: 2610.05164v2, Lemma 11 via `«2610.05164v2».Comparison.Profile.rightJost_ode`.
-/
def rightJostSlope (s x : ℝ) : ℝ := -jostFunctionSlope s (reflected (P.density hκ)) (-x)

/--
The stated quantitative bound `0 < P.rightJost hκ s x`.

Use: a standalone supporting bound for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Lemma 11.

Proof: Use the identities/estimates `«2610.05164v2».Filters.jost_positive`,
`«2610.05164v2».Filters.reflected_integrable`,
`«2610.05164v2».PrescribedSpeed.SpeedData.density_integrable` with the arguments shown in the
proof.
-/
theorem rightJost_positive {s : ℝ} (hs : 0 ≤ s) (x : ℝ) : 0 < P.rightJost hκ s x :=
  mul_pos (exp_pos _) (jost_positive
    (reflected_integrable ((P.speedData hκ).density_integrable hκ))
    (reflected_nonneg ((P.speedData hκ).density_nonneg hκ)) hs _)

/--
The actual derivative at the stated point: `HasDerivAt (P.rightJost hκ s) (P.rightJostSlope hκ
s x) x`.

Use: a standalone supporting derivative formula for the article chain below; no retained
declaration currently has an explicit proof dependency on it.

Article: 2610.05164v2, Lemma 11.

Proof: Use the identities/estimates `«2610.05164v2».Filters.jostFunction_hasDerivAt`,
`«2610.05164v2».Filters.reflected_integrable`,
`«2610.05164v2».PrescribedSpeed.SpeedData.density_integrable` with the arguments shown in the
proof.
-/
theorem rightJost_derivative {s : ℝ} (hs : 0 ≤ s) (x : ℝ) :
    HasDerivAt (P.rightJost hκ s) (P.rightJostSlope hκ s x) x := by
  -- Use the identities/estimates `«2610.05164v2».Filters.jostFunction_hasDerivAt`,
  -- `«2610.05164v2».Filters.reflected_integrable`,
  -- `«2610.05164v2».PrescribedSpeed.SpeedData.density_integrable` with the arguments shown in
  -- the proof.
  have h := (jostFunction_hasDerivAt
    (reflected_integrable ((P.speedData hκ).density_integrable hκ))
    (reflected_nonneg ((P.speedData hκ).density_nonneg hκ)) hs (-x)).comp x (hasDerivAt_neg x)
  convert h using 1
  · rfl
  · dsimp only [rightJostSlope,density]
    ring

/--
The actual derivative at the stated point: `HasDerivAt (P.rightJostSlope hκ s) ((1+s*P.density
hκ x)*P.rightJost hκ s x) x`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2610.05164v2, Lemma 11.

Proof: Use the identities/estimates `«2610.05164v2».Filters.reflected_integrable`,
`«2610.05164v2».PrescribedSpeed.SpeedData.density_integrable`,
`«2610.05164v2».Filters.reflected_nonneg` with the arguments shown in the proof.
-/
theorem rightJost_ode {s : ℝ} (hs : 0 ≤ s) (x : ℝ) :
    HasDerivAt (P.rightJostSlope hκ s)
      ((1+s*P.density hκ x)*P.rightJost hκ s x) x := by
  -- Use the identities/estimates `«2610.05164v2».Filters.reflected_integrable`,
  -- `«2610.05164v2».PrescribedSpeed.SpeedData.density_integrable`,
  -- `«2610.05164v2».Filters.reflected_nonneg` with the arguments shown in the proof.
  let mr := reflected (P.density hκ)
  have hm := reflected_integrable ((P.speedData hκ).density_integrable hκ)
  have hn := reflected_nonneg ((P.speedData hκ).density_nonneg hκ)
  have hc := reflected_continuous (P.density_continuous hκ)
  -- Establish continuity hy before using the function at limits or in calculus arguments.
  have hy : Continuous (jostFunction s mr) := by
    exact continuous_exp.mul (jost_continuous hm hn hs)
  have hd (t : ℝ) := locallyAC_hasDerivAt_of_continuous
    (jostFunctionSlope_locallyAC hm hn hs) (jostFunction_ode hm hn hs)
    ((continuous_const.add (continuous_const.mul hc)).mul hy) t
  have h := (hd (-x)).comp x (hasDerivAt_neg x) |>.neg
  convert h using 1
  · rfl
  · dsimp only [mr,reflected,neg_neg,rightJost,density]
    ring_nf

/--
The precise assertion is `P.rightFilter hκ s q= -P.rightJostSlope hκ s ((P.speedData hκ).X q)/
P.rightJost hκ s ((P.speedData hκ).X q)-1`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Lemma 11.

Proof: Use the identities/estimates `«2610.05164v2».Filters.nonlinear_jostFunction_quotient`,
`«2610.05164v2».Filters.reflected_integrable`,
`«2610.05164v2».PrescribedSpeed.SpeedData.density_integrable` with the arguments shown in the
proof.
-/
theorem rightFilter_jost_quotient {s : ℝ} (hs : 0 ≤ s) (q : ℝ) :
    P.rightFilter hκ s q=
      -P.rightJostSlope hκ s ((P.speedData hκ).X q)/
        P.rightJost hκ s ((P.speedData hκ).X q)-1 := by
  -- Use the identities/estimates `«2610.05164v2».Filters.nonlinear_jostFunction_quotient`,
  -- `«2610.05164v2».Filters.reflected_integrable`,
  -- `«2610.05164v2».PrescribedSpeed.SpeedData.density_integrable` with the arguments shown in
  -- the proof.
  have h := nonlinear_jostFunction_quotient
    (reflected_integrable ((P.speedData hκ).density_integrable hκ))
    (reflected_nonneg ((P.speedData hκ).density_nonneg hκ)) hs
    (-((P.speedData hκ).X q))
  change P.rightFilter hκ s q=_ at h
  simpa only [rightJostSlope,rightJost,neg_neg,density] using h

/--
Exact identity `P.rightJost hκ s x=exp (-x)`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Lemma 11.

Proof: Use the identities/estimates
`«2610.05164v2».PrescribedSpeed.SpeedData.density_zero_outside`,
`«2610.05164v2».Filters.jost_left_of_density_zero`,
`«2610.05164v2».Filters.reflected_integrable` with the arguments shown in the proof.
-/
theorem rightJost_normalization {s : ℝ} (hs : 0 ≤ s) {x : ℝ}
    (hx : (P.speedData hκ).X 2 ≤ x) : P.rightJost hκ s x=exp (-x) := by
  -- Use the identities/estimates
  -- `«2610.05164v2».PrescribedSpeed.SpeedData.density_zero_outside`,
  -- `«2610.05164v2».Filters.jost_left_of_density_zero`,
  -- `«2610.05164v2».Filters.reflected_integrable` with the arguments shown in the proof.
  have hz : ∀ t ≤ -x, reflected (P.density hκ) t=0 := by
    intro t ht
    change (P.speedData hκ).density κ (-t)=0
    exact (P.speedData hκ).density_zero_outside κ
      (fun h => (not_lt_of_ge (le_trans hx (by linarith))) h.2)
  change exp (-x)*jost s (reflected ((P.speedData hκ).density κ)) (-x)=exp (-x)
  rw [jost_left_of_density_zero (reflected_integrable ((P.speedData hκ).density_integrable hκ))
    (reflected_nonneg ((P.speedData hκ).density_nonneg hκ)) hs (-x) hz,mul_one]

/--
Defines `rightJostDecayingCoefficient` of type `ℝ` by `-s/2*∫ t, exp (2*t)* (reflected
(P.density hκ) t*jost s (reflected (P.density hκ)) t)`.

Use: `«2610.05164v2».Comparison.Profile.rightJost_left_expansion` uses this definition to
establish the identity stated in that declaration.

Article: 2610.05164v2, Lemma 11.
-/
def rightJostDecayingCoefficient (s : ℝ) : ℝ := -s/2*∫ t, exp (2*t)*
  (reflected (P.density hκ) t*jost s (reflected (P.density hκ)) t)

/--
The precise assertion is `P.rightJost hκ s x= exp (logDeterminant (kernelEigenvalue
((P.speedData hκ).density_integrable hκ) ((P.speedData hκ).density_nonneg hκ)) s)*exp (-x)+
P.rightJostDecayingCoefficient hκ s*exp x`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Lemma 11.

Proof: Use the identities/estimates
`«2610.05164v2».PrescribedSpeed.SpeedData.density_integrable`,
`«2610.05164v2».PrescribedSpeed.SpeedData.density_nonneg`,
`«2610.05164v2».PrescribedSpeed.SpeedData.density_zero_outside` with the arguments shown in the
proof.
-/
theorem rightJost_left_expansion {s : ℝ} (hs : 0 ≤ s) {x : ℝ}
    (hx : x ≤ (P.speedData hκ).X 0) :
    P.rightJost hκ s x=
      exp (logDeterminant (kernelEigenvalue ((P.speedData hκ).density_integrable hκ)
        ((P.speedData hκ).density_nonneg hκ)) s)*exp (-x)+
          P.rightJostDecayingCoefficient hκ s*exp x := by
  -- Use the identities/estimates
  -- `«2610.05164v2».PrescribedSpeed.SpeedData.density_integrable`,
  -- `«2610.05164v2».PrescribedSpeed.SpeedData.density_nonneg`,
  -- `«2610.05164v2».PrescribedSpeed.SpeedData.density_zero_outside` with the arguments shown
  -- in the proof.
  have hz : ∀ t, -x<t → reflected (P.density hκ) t=0 := by
    intro t ht
    change (P.speedData hκ).density κ (-t)=0
    exact (P.speedData hκ).density_zero_outside κ (fun h =>
      (not_lt_of_ge (le_trans (by linarith : -t ≤ x) hx)) h.1)
  have h := jost_right_of_density_zero
    (reflected_integrable ((P.speedData hκ).density_integrable hκ))
    (reflected_nonneg ((P.speedData hκ).density_nonneg hκ)) hs (-x) hz
  have ht : transmission s (reflected ((P.speedData hκ).density κ))=
      exp (logDeterminant (kernelEigenvalue ((P.speedData hκ).density_integrable hκ)
        ((P.speedData hκ).density_nonneg hκ)) s) := by
    rw [transmission_reflection ((P.speedData hκ).density_integrable hκ)
      ((P.speedData hκ).density_nonneg hκ) (P.density_continuous hκ) hs,
      ← log_transmission_eq_logDeterminant ((P.speedData hκ).density_integrable hκ)
        ((P.speedData hκ).density_nonneg hκ) hs]
    exact (exp_log (zero_lt_one.trans_le (transmission_ge_one
      ((P.speedData hκ).density_integrable hκ) ((P.speedData hκ).density_nonneg hκ) hs))).symm
  rw [ht,neg_neg] at h
  change P.rightJost hκ s x=_ at h
  rw [h]
  dsimp only [rightJostDecayingCoefficient,density]
  ring

end
end «2610.05164v2».Comparison.Profile
