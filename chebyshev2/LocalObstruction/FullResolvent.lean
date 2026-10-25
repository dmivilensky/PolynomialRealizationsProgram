import chebyshev2.HalfLine.FeatureResolvent
import chebyshev2.LocalObstruction.CompactPerturbation
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
Article: chebyshev2, Theorem 6.1.
The actual full Sobolev positive pencil: analytic inverse and its scale variation.
Use: `chebyshev2.LocalObstruction.fullResolvent_norm` feeds
`chebyshev2.LocalObstruction.resolventGreen_abs_bound` (resolvent Green abs bound).
Proof chain: `chebyshev2.LocalObstruction.sine_green_scale_tail` — chebyshev2, Theorem 6.1; No
locally sharp C1 bound from finitely many spectral observations.
-/
namespace chebyshev2.LocalObstruction
noncomputable section
open MeasureTheory chebyshev2.Continuum chebyshev2.HalfLine
open scoped InnerProductSpace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/--
Defines `FeatureOperator` of type `` by `FeatureSpace →L[ℝ] FeatureSpace`.

Use: `chebyshev2.LocalObstruction.fullPencil` uses this definition in the displayed
construction of `fullPencil`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Lemma 26 via
`chebyshev2.LocalObstruction.resolventGreen_density_derivative`.
-/
abbrev FeatureOperator := FeatureSpace →L[ℝ] FeatureSpace

/--
Defines `fullPencil` of type `FeatureOperator` by `ContinuousLinearMap.id ℝ FeatureSpace+(s/2)
• densityOperator m`.

Use: `chebyshev2.LocalObstruction.fullResolvent` uses this definition in the displayed
construction of `fullResolvent`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Lemma 26 via
`chebyshev2.LocalObstruction.resolventGreen_density_derivative`.
-/
def fullPencil (m : ℝ → ℝ) (s : ℝ) : FeatureOperator :=
  ContinuousLinearMap.id ℝ FeatureSpace+(s/2) • densityOperator m

/--
Defines `fullResolvent` of type `FeatureOperator` by `Ring.inverse (fullPencil m s)`.

Use: `chebyshev2.LocalObstruction.fullResolvent_derivative` rewrites with this definition
to establish the actual derivative at the stated point: `HasDerivAt (fullResolvent m)
(-((fullResolvent m s) ∘L ((1/2:ℝ) • densityOperator m) ∘L (fullResolvent m s))) s`.

Article: chebyshev2, Lemma 26 via
`chebyshev2.LocalObstruction.resolventGreen_density_derivative`.
-/
def fullResolvent (m : ℝ → ℝ) (s : ℝ) : FeatureOperator := Ring.inverse (fullPencil m s)

/--
The precise assertion is `IsUnit (fullPencil m s)`.

Use: `chebyshev2.LocalObstruction.fullResolvent_analytic` uses this assertion to establish
the precise assertion is `AnalyticAt ℝ (fullResolvent m) s`.

Article: chebyshev2, Lemma 26 via
`chebyshev2.LocalObstruction.resolventGreen_density_derivative`.

Proof: Use the identities/estimates `chebyshev2.HalfLine.positive_pencil_unit`,
`chebyshev2.Continuum.densityOperator_positive` with the arguments shown in the proof.
-/
theorem fullPencil_unit {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0≤m x)
    {s : ℝ} (hs : 0≤s) : IsUnit (fullPencil m s) :=
  positive_pencil_unit (densityOperator_positive hm hn) (div_nonneg hs (by norm_num))

/--
Exact identity `fullResolvent m s=inverseOfUnit (fullPencil m s) (fullPencil_unit hm hn hs)`.

Use: `chebyshev2.LocalObstruction.fullResolvent_norm` rewrites with this identity to
establish the stated quantitative bound `‖fullResolvent m s u‖≤‖u‖`.

Article: chebyshev2, Lemma 26 via
`chebyshev2.LocalObstruction.resolventGreen_density_derivative`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem fullResolvent_eq_inverseOfUnit {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0≤m x)
    {s : ℝ} (hs : 0≤s) :
    fullResolvent m s=inverseOfUnit (fullPencil m s) (fullPencil_unit hm hn hs) :=
  Ring.inverse_of_isUnit _

/--
The precise assertion is `AnalyticAt ℝ (fullResolvent m) s`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Theorem 6.1.

Proof: Use the identities/estimates `chebyshev2.LocalObstruction.fullPencil_unit` with the
arguments shown in the proof.
-/
theorem fullResolvent_analytic {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0≤m x)
    {s : ℝ} (hs : 0≤s) : AnalyticAt ℝ (fullResolvent m) s := by
  have hi : AnalyticAt ℝ Ring.inverse (fullPencil m s) := by
    simpa only [IsUnit.unit_spec] using
      (analyticAt_inverse (𝕜 := ℝ) (fullPencil_unit hm hn hs).unit)
  apply hi.comp
  exact analyticAt_const.add ((analyticAt_id.div_const (c := (2:ℝ))).smul analyticAt_const)

/--
The actual derivative at the stated point: `HasDerivAt (fullResolvent m) (-((fullResolvent m s)
∘L ((1/2:ℝ) • densityOperator m) ∘L (fullResolvent m s))) s`.

Use: `chebyshev2.LocalObstruction.green_density_gradient_scale_derivative` uses this
derivative formula to establish the actual derivative at the stated point: `HasDerivAt (fun t :
ℝ => t*(∫ x,greenKernel t m x x*v x)) (∫ x,(greenKernel s m x x+s*greenScaleGradient s m x)*v
x) s`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Use the identities/estimates `chebyshev2.LocalObstruction.fullPencil_unit` with the
arguments shown in the proof.
-/
theorem fullResolvent_derivative {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0≤m x)
    {s : ℝ} (hs : 0≤s) :
    HasDerivAt (fullResolvent m)
      (-((fullResolvent m s) ∘L ((1/2:ℝ) • densityOperator m) ∘L (fullResolvent m s))) s := by
  -- Use the identities/estimates `chebyshev2.LocalObstruction.fullPencil_unit` with the
  -- arguments shown in the proof.
  let hunit := fullPencil_unit hm hn hs
  have hp : HasDerivAt (fullPencil m) ((1/2:ℝ) • densityOperator m) s := by
    convert! (((hasDerivAt_id s).div_const 2).smul_const (densityOperator m)).const_add
      (ContinuousLinearMap.id ℝ FeatureSpace) using 1
  have hi := hasFDerivAt_ringInverse (𝕜 := ℝ) hunit.unit
  rw [IsUnit.unit_spec] at hi
  convert! hi.comp_hasDerivAt s hp using 1
  simp only [neg_apply,ContinuousLinearMap.mulLeftRight_apply,
    fullResolvent,Ring.inverse_of_isUnit hunit]
  rfl

/--
The stated quantitative bound `‖fullResolvent m s u‖≤‖u‖`.

Use: `chebyshev2.LocalObstruction.resolventGreen_abs_bound` uses this bound to establish
the stated quantitative bound `|resolventGreen m s x y|≤1/2`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.sine_green_scale_tail`.

Proof: Use the identities/estimates
`chebyshev2.LocalObstruction.fullResolvent_eq_inverseOfUnit`,
`chebyshev2.HalfLine.positive_inverse_norm`,
`chebyshev2.Continuum.densityOperator_positive` with the arguments shown in the proof.
-/
theorem fullResolvent_norm {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0≤m x)
    {s : ℝ} (hs : 0≤s) (u : FeatureSpace) : ‖fullResolvent m s u‖≤‖u‖ := by
  rw [fullResolvent_eq_inverseOfUnit hm hn hs]
  exact positive_inverse_norm (densityOperator_positive hm hn) (div_nonneg hs (by norm_num)) _ u

end
end chebyshev2.LocalObstruction
