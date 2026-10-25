import chebyshev2.LocalObstruction.GreenConvolution
import chebyshev2.LocalObstruction.FullGreenEquation

/-!
Article: chebyshev2, Theorem 6.1.
Identification of the actual two-sided Jost Green kernel with the full Sobolev resolvent kernel,
using the scalar free-kernel integral equation.
Use: `chebyshev2.LocalObstruction.greenScaleGradient_continuous` feeds
`chebyshev2.LocalObstruction.theorem_6_1` (theorem 6 1).
Proof chain: `chebyshev2.LocalObstruction.theorem_6_1` — chebyshev2, Theorem 6.1; No locally
sharp C1 bound from finitely many spectral observations.
-/
namespace chebyshev2.LocalObstruction
noncomputable section
open MeasureTheory Real chebyshev2.Filters chebyshev2.HalfLine chebyshev2.GroundState chebyshev2.Continuum
open scoped InnerProductSpace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x,0≤m x)
    (hc : Continuous m) {s : ℝ} (hs : 0≤s) (he : ∀ x,m (-x)=m x)
include hm hn hc hs he

 /--
Exact identity `inner ℝ (feature y) (fullResolvent m s (feature x))=2*greenKernel s m x y`.

Use: `chebyshev2.LocalObstruction.greenKernel_eq_resolventGreen` rewrites with this
identity to establish the identity `greenKernel s m x y=resolventGreen m s x y`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.sine_green_scale_tail`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem fullResolvent_feature_green (x y : ℝ) :
    inner ℝ (feature y) (fullResolvent m s (feature x))=2*greenKernel s m x y := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  let j := fun z => m z*greenKernel s m x z
  let v : FeatureSpace := ∫ z,j z • feature z
  let w := feature x-s • v
  have hj := greenColumn_integrable hm hn hc hs he x
  have hv := synthesisL1_integrable hj
  have hinner (z : ℝ) : inner ℝ (feature z) w=2*greenKernel s m x z := by
    change inner ℝ (feature z) (feature x-s • v)=_
    rw [inner_sub_right,real_inner_smul_right,feature_inner]
    have hi : inner ℝ (feature z) v=∫ a,exp (-|z-a|)*(m a*greenKernel s m x a) := by
      dsimp only [v]
      rw [← integral_inner hv (feature z)]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun a => by
        dsimp only
        rw [real_inner_smul_right,feature_inner]
        ring)
    rw [hi,abs_sub_comm z x]
    linear_combination -2*greenColumn_fredholm hm hn hc hs he x z
  have hTw : densityOperator m w=(2:ℝ) • v := by
    unfold densityOperator
    rw [ContinuousLinearMap.integral_apply (densityOperator_integrable hm) w]
    dsimp only [v]
    rw [← integral_smul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun z => by
      change m z • (inner ℝ (feature z) w • feature z)=(2:ℝ) • (j z • feature z)
      rw [hinner]
      dsimp only [j]
      module)
  have hp : fullPencil m s w=feature x := by
    change w+(s/2) • densityOperator m w=feature x
    rw [hTw]
    dsimp only [w]
    module
  have hw : fullResolvent m s (feature x)=w := by
    rw [fullResolvent_eq_inverseOfUnit hm hn hs]
    exact inverseOfUnit_apply_of_eq _ _ hp
  rw [hw]
  exact hinner y

 /--
Exact identity `greenKernel s m x y=resolventGreen m s x y`.

Use: `chebyshev2.LocalObstruction.greenKernel_scale_derivative` rewrites with this identity
to establish the derivative within the stated domain: `HasDerivWithinAt (fun t => greenKernel t
m x y) (-(∫ z,greenKernel s m x z*greenKernel s m z y*m z)) (Set.Ici (0:ℝ)) s`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.sine_green_scale_tail`.

Proof: Use the identities/estimates `chebyshev2.LocalObstruction.resolventGreen_symmetric`,
`chebyshev2.LocalObstruction.fullResolvent_feature_green` with the arguments shown in the
proof.
-/
theorem greenKernel_eq_resolventGreen (x y : ℝ) :
    greenKernel s m x y=resolventGreen m s x y := by
  rw [resolventGreen_symmetric hm hn hs x y]
  unfold resolventGreen
  rw [fullResolvent_feature_green hm hn hc hs he x y]
  ring

 /--
The derivative within the stated domain: `HasDerivWithinAt (fun t => greenKernel t m x y) (-(∫
z,greenKernel s m x z*greenKernel s m z y*m z)) (Set.Ici (0:ℝ)) s`.

Use: `chebyshev2.LocalObstruction.greenKernel_hasDerivAt` uses this derivative formula to
establish the actual derivative at the stated point: `HasDerivAt (fun t => greenKernel t m x y)
(-(∫ z,greenKernel s m x z*greenKernel s m z y*m z)) s`.

Article: chebyshev2, Theorem 6.1.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem greenKernel_scale_derivative (x y : ℝ) :
    HasDerivWithinAt (fun t => greenKernel t m x y)
      (-(∫ z,greenKernel s m x z*greenKernel s m z y*m z)) (Set.Ici (0:ℝ)) s := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  have h := (resolventGreen_derivative hm hn hs x y).hasDerivWithinAt (s := Set.Ici (0:ℝ))
  have heq : Set.EqOn (fun t => greenKernel t m x y) (fun t => resolventGreen m t x y) (Set.Ici (0:ℝ)) := by
    intro t ht
    exact greenKernel_eq_resolventGreen hm hn hc ht he x y
  convert! h.congr heq (heq hs) using 1
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z => by
    dsimp only
    rw [greenKernel_eq_resolventGreen hm hn hc hs he x z,
      greenKernel_eq_resolventGreen hm hn hc hs he z y])

omit hs in
 /--
The actual derivative at the stated point: `HasDerivAt (fun t => greenKernel t m x y) (-(∫
z,greenKernel s m x z*greenKernel s m z y*m z)) s`.

Use: `chebyshev2.LocalObstruction.green_diagonal_hasDerivAt` uses this derivative formula
to establish the actual derivative at the stated point: `HasDerivAt (fun t => greenKernel t m x
x) (greenScaleGradient s m x) s`.

Article: chebyshev2, Theorem 6.1.

Proof: Use the identities/estimates
`chebyshev2.LocalObstruction.greenKernel_scale_derivative` with the arguments shown in the
proof.
-/
theorem greenKernel_hasDerivAt (hpos : 0<s) (x y : ℝ) :
    HasDerivAt (fun t => greenKernel t m x y)
      (-(∫ z,greenKernel s m x z*greenKernel s m z y*m z)) s :=
  (greenKernel_scale_derivative hm hn hc hpos.le he x y).hasDerivAt (Ici_mem_nhds hpos)

 /--
Defines `greenScaleGradient` of type `ℝ` by `-(∫ z,greenKernel s m x z^2*m z)`.

Use: `chebyshev2.LocalObstruction.greenScaleGradient_continuous` uses this definition to
establish continuity of the displayed function: `Continuous (greenScaleGradient s m)`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.sine_green_scale_tail`.
-/
def greenScaleGradient (s : ℝ) (m : ℝ → ℝ) (x : ℝ) : ℝ :=
  -(∫ z,greenKernel s m x z^2*m z)

 /--
The precise assertion is `greenScaleGradient s m x= -(1/4:ℝ)* inner ℝ (fullResolvent m s
(feature x)) (densityOperator m (fullResolvent m s (feature x)))`.

Use: `chebyshev2.LocalObstruction.greenScaleGradient_continuous` uses this identity to
establish continuity of the displayed function: `Continuous (greenScaleGradient s m)`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem greenScaleGradient_operator (x : ℝ) :
    greenScaleGradient s m x= -(1/4:ℝ)*
      inner ℝ (fullResolvent m s (feature x))
        (densityOperator m (fullResolvent m s (feature x))) := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  rw [densityOperator_inner hm,← integral_const_mul]
  unfold greenScaleGradient
  rw [← integral_neg]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z => by
    dsimp only
    rw [fullResolvent_feature_green hm hn hc hs he x z]
    ring)

 /--
Continuity of the displayed function: `Continuous (greenScaleGradient s m)`.

Use: `chebyshev2.LocalObstruction.greenScaleTailGradient` uses this continuity result in
the displayed construction of `greenScaleTailGradient`. Its inputs and component formulas are
fixed by that definition.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem greenScaleGradient_continuous : Continuous (greenScaleGradient s m) := by
  -- Establish continuity hR before using the function at limits or in calculus arguments.
  have hR : Continuous (fun x => fullResolvent m s (feature x)) :=
    (fullResolvent m s).continuous.comp feature_continuous
  have heq : greenScaleGradient s m=fun x => -(1/4:ℝ)*
      inner ℝ (fullResolvent m s (feature x))
        (densityOperator m (fullResolvent m s (feature x))) :=
    funext (greenScaleGradient_operator hm hn hc hs he)
  rw [heq]
  exact continuous_const.mul (hR.inner ((densityOperator m).continuous.comp hR))

omit hs in
 /--
The actual derivative at the stated point: `HasDerivAt (fun t => greenKernel t m x x)
(greenScaleGradient s m x) s`.

Use: a standalone supporting derivative formula for the article chain below; no retained
declaration currently has an explicit proof dependency on it.

Article: chebyshev2, Theorem 6.1.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem green_diagonal_hasDerivAt (hpos : 0<s) (x : ℝ) :
    HasDerivAt (fun t => greenKernel t m x x) (greenScaleGradient s m x) s := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  convert! greenKernel_hasDerivAt hm hn hc he hpos x x using 1
  unfold greenScaleGradient
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z => by
    dsimp only
    rw [greenKernel_symmetric s m z x]
    ring)

end
end chebyshev2.LocalObstruction
