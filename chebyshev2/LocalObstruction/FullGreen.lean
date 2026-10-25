import chebyshev2.LocalObstruction.FullResolvent
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
Article: chebyshev2, Theorem 6.1.
Scale variation of the full Sobolev resolvent kernel.
Use: `chebyshev2.LocalObstruction.resolventGreen_symmetric` feeds
`chebyshev2.LocalObstruction.greenKernel_eq_resolventGreen` (green Kernel eq resolvent Green).
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
Defines `resolventGreen` of type `ℝ` by `inner ℝ (feature x) (fullResolvent m s (feature
y))/2`.

Use: `chebyshev2.LocalObstruction.resolventGreen_derivative` uses this definition to
establish the actual derivative at the stated point: `HasDerivAt (fun t => resolventGreen m t x
y) (-(∫ z, resolventGreen m s x z*resolventGreen m s z y*m z)) s`.

Article: chebyshev2, Lemma 26 via
`chebyshev2.LocalObstruction.resolventGreen_density_derivative`.
-/
def resolventGreen (m : ℝ → ℝ) (s x y : ℝ) : ℝ :=
  inner ℝ (feature x) (fullResolvent m s (feature y))/2

 /--
Exact identity `fullPencil m s (fullResolvent m s u)=u`.

Use: `chebyshev2.LocalObstruction.fullResolvent_symmetric` rewrites with this identity to
establish exact identity `inner ℝ (fullResolvent m s u) v=inner ℝ u (fullResolvent m s v)`.

Article: chebyshev2, Lemma 26 via
`chebyshev2.LocalObstruction.resolventGreen_density_derivative`.

Proof: Use the identities/estimates `chebyshev2.LocalObstruction.fullPencil_unit`,
`chebyshev2.LocalObstruction.fullResolvent_eq_inverseOfUnit`,
`chebyshev2.HalfLine.inverseOfUnit_right` with the arguments shown in the proof.
-/
theorem fullResolvent_right {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x,0≤m x)
    {s : ℝ} (hs : 0≤s) (u : FeatureSpace) :
    fullPencil m s (fullResolvent m s u)=u := by
  rw [fullResolvent_eq_inverseOfUnit hm hn hs]
  exact DFunLike.congr_fun (inverseOfUnit_right (fullPencil m s) (fullPencil_unit hm hn hs)) u

 /--
Exact identity `inner ℝ (fullPencil m s u) v=inner ℝ u (fullPencil m s v)`.

Use: `chebyshev2.LocalObstruction.fullResolvent_symmetric` uses this identity to establish
exact identity `inner ℝ (fullResolvent m s u) v=inner ℝ u (fullResolvent m s v)`.

Article: chebyshev2, Lemma 26 via
`chebyshev2.LocalObstruction.resolventGreen_density_derivative`.

Proof: Use the identities/estimates `chebyshev2.Continuum.densityOperator_positive` with
the arguments shown in the proof.
-/
theorem fullPencil_symmetric {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x,0≤m x)
    (s : ℝ) (u v : FeatureSpace) :
    inner ℝ (fullPencil m s u) v=inner ℝ u (fullPencil m s v) := by
  have h := (densityOperator_positive hm hn).isSymmetric u v
  change inner ℝ (densityOperator m u) v=inner ℝ u (densityOperator m v) at h
  simp only [fullPencil,add_apply,ContinuousLinearMap.id_apply,
    smul_apply,inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right,h]

 /--
Exact identity `inner ℝ (fullResolvent m s u) v=inner ℝ u (fullResolvent m s v)`.

Use: `chebyshev2.LocalObstruction.resolventGreen_derivative` rewrites with this identity to
establish the actual derivative at the stated point: `HasDerivAt (fun t => resolventGreen m t x
y) (-(∫ z, resolventGreen m s x z*resolventGreen m s z y*m z)) s`.

Article: chebyshev2, Lemma 26 via
`chebyshev2.LocalObstruction.resolventGreen_density_derivative`.

Proof: Use the identities/estimates `chebyshev2.LocalObstruction.fullPencil_symmetric`,
`chebyshev2.LocalObstruction.fullResolvent_right` with the arguments shown in the proof.
-/
theorem fullResolvent_symmetric {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x,0≤m x)
    {s : ℝ} (hs : 0≤s) (u v : FeatureSpace) :
    inner ℝ (fullResolvent m s u) v=inner ℝ u (fullResolvent m s v) := by
  have h := fullPencil_symmetric hm hn s (fullResolvent m s u) (fullResolvent m s v)
  rw [fullResolvent_right hm hn hs,fullResolvent_right hm hn hs] at h
  exact h.symm

 /--
Exact identity `resolventGreen m s x y=resolventGreen m s y x`.

Use: `chebyshev2.LocalObstruction.resolventGreen_diagonal_derivative` rewrites with this
identity to establish the actual derivative at the stated point: `HasDerivAt (fun t =>
resolventGreen m t x x) (-(∫ z, resolventGreen m s x z^2*m z)) s`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.sine_green_scale_tail`.

Proof: Use the identities/estimates `chebyshev2.LocalObstruction.fullResolvent_symmetric`
with the arguments shown in the proof.
-/
theorem resolventGreen_symmetric {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x,0≤m x)
    {s : ℝ} (hs : 0≤s) (x y : ℝ) : resolventGreen m s x y=resolventGreen m s y x := by
  unfold resolventGreen
  rw [← fullResolvent_symmetric hm hn hs,real_inner_comm]

 /--
Continuity of the displayed function: `Continuous (fun p : ℝ × ℝ => resolventGreen m s p.1
p.2)`.

Use: a standalone supporting continuity result for the article chain below; no retained
declaration currently has an explicit proof dependency on it.

Article: chebyshev2, Theorem 6.1.

Proof: Use the identities/estimates `chebyshev2.Continuum.feature_continuous` with the
arguments shown in the proof.
-/
theorem resolventGreen_continuous (m : ℝ → ℝ) (s : ℝ) :
    Continuous (fun p : ℝ × ℝ => resolventGreen m s p.1 p.2) := by
  exact ((feature_continuous.comp continuous_fst).inner
    ((fullResolvent m s).continuous.comp (feature_continuous.comp continuous_snd))).div_const 2

 /--
The actual derivative at the stated point: `HasDerivAt (fun t => resolventGreen m t x y) (-(∫
z, resolventGreen m s x z*resolventGreen m s z y*m z)) s`.

Use: `chebyshev2.LocalObstruction.resolventGreen_diagonal_derivative` uses this derivative
formula to establish the actual derivative at the stated point: `HasDerivAt (fun t =>
resolventGreen m t x x) (-(∫ z, resolventGreen m s x z^2*m z)) s`.

Article: chebyshev2, Theorem 6.1.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem resolventGreen_derivative {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x,0≤m x)
    {s : ℝ} (hs : 0≤s) (x y : ℝ) :
    HasDerivAt (fun t => resolventGreen m t x y)
      (-(∫ z, resolventGreen m s x z*resolventGreen m s z y*m z)) s := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  have hR := (fullResolvent_derivative hm hn hs).clm_apply (hasDerivAt_const s (feature y))
  have hd := ((hasDerivAt_const s (feature x)).inner ℝ hR).div_const 2
  have he : (inner ℝ (feature x)
      ((-((fullResolvent m s) ∘L ((1/2:ℝ) • densityOperator m) ∘L (fullResolvent m s)))
        (feature y)))/2=
      -(∫ z, resolventGreen m s x z*resolventGreen m s z y*m z) := by
    simp only [neg_apply,ContinuousLinearMap.comp_apply,smul_apply,
      map_smul,inner_neg_right,real_inner_smul_right]
    rw [← fullResolvent_symmetric hm hn hs,densityOperator_inner hm]
    rw [← integral_const_mul]
    rw [neg_div]
    congr 1
    rw [← integral_div]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun z => by
      dsimp only
      unfold resolventGreen
      rw [← fullResolvent_symmetric hm hn hs (feature x) (feature z),
        real_inner_comm (fullResolvent m s (feature x)) (feature z)]
      ring)
  convert! hd using 1
  simpa only [map_zero,zero_add,zero_mul,add_zero,inner_zero_left] using he.symm

 /--
The actual derivative at the stated point: `HasDerivAt (fun t => resolventGreen m t x x) (-(∫
z, resolventGreen m s x z^2*m z)) s`.

Use: a standalone supporting derivative formula for the article chain below; no retained
declaration currently has an explicit proof dependency on it.

Article: chebyshev2, Theorem 6.1.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem resolventGreen_diagonal_derivative {m : ℝ → ℝ} (hm : Integrable m)
    (hn : ∀ x,0≤m x) {s : ℝ} (hs : 0≤s) (x : ℝ) :
    HasDerivAt (fun t => resolventGreen m t x x)
      (-(∫ z, resolventGreen m s x z^2*m z)) s := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  convert! resolventGreen_derivative hm hn hs x x using 1
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z => by
    dsimp only
    rw [resolventGreen_symmetric hm hn hs z x]
    ring)

end
end chebyshev2.LocalObstruction
