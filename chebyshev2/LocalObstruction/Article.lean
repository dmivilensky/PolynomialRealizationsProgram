import chebyshev2.LocalObstruction.MovingObservation
import chebyshev2.LocalObstruction.FiniteObstruction
import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported

/-!
Article: chebyshev2, Theorem 6.1.
Theorem 6.1, including omitted coordinates and C1 scales depending on the actual ground coupling.
Result: `chebyshev2.LocalObstruction.theorem_6_1` supplies the stated article conclusion.
-/
namespace chebyshev2.LocalObstruction
noncomputable section
open Set MeasureTheory Real Filter chebyshev2.SineContinuum
open scoped Topology ContDiff
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

 /--
Exact identity `densityEnergy f=(∫ x,(sqrt (f x))^3)`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Theorem 6.1.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem densityEnergy_eq_cube {f : ℝ → ℝ} (hn : ∀ x,0≤f x) :
    densityEnergy f=(∫ x,(sqrt (f x))^3) := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    change f x*sqrt (f x)=(sqrt (f x))^3
    rw [show (3:ℕ)=2+1 from rfl,pow_succ,sq_sqrt (hn x)])

 /--
Exact identity `densityEnergy m=chebyshev2.SineJacobi.energy`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Theorem 6.1.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.energy` with the arguments
shown in the proof.
-/
theorem densityEnergy_sine : densityEnergy m=chebyshev2.SineJacobi.energy := chebyshev2.SineContinuum.energy

 /--
Defines the alternatives used to distinguish the cases in the subsequent construction.

Use: `chebyshev2.LocalObstruction.ObservationSpec.scalePositive` uses this definition in
the displayed construction of `ObservationSpec.scalePositive`. Its inputs and component
formulas are fixed by that definition.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.
-/
inductive ObservationSpec where
  /-- The actual leading-eigenvalue ground-coupling observation. -/
  | ground
  /-- The kernel square-trace observation, expressed through the density pairing. -/
  | squareTrace
  /-- The spectral log determinant at a positive C¹ scale that may depend on the ground coupling. -/
  | fredholm (σ : ℝ → ℝ) (regular : ContDiffAt ℝ 1 σ (groundCoupling m)) (positive : 0<σ (groundCoupling m))
  /-- The scale derivative of the spectral log determinant at such a moving positive C¹ scale. -/
  | fredholmSlope (σ : ℝ → ℝ) (regular : ContDiffAt ℝ 1 σ (groundCoupling m)) (positive : 0<σ (groundCoupling m))

 /--
Defines `ObservationSpec.value` by pattern matching with result type `ObservationSpec → (ℝ → ℝ)
→ ℝ`. The displayed branches determine the recursive cases and their returned values.

Use: `chebyshev2.LocalObstruction.ObservationSpec.witness` uses this definition in the
displayed construction of `ObservationSpec.witness`. Its inputs and component formulas are
fixed by that definition.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.
-/
def ObservationSpec.value : ObservationSpec → (ℝ → ℝ) → ℝ
  | .ground => groundCoupling
  | .squareTrace => fun f => pairing f f
  | .fredholm σ _ _ => fun f => observationH f (σ (groundCoupling f))
  | .fredholmSlope σ _ _ => fun f => observationS f (σ (groundCoupling f))

 /--
Defines `ObservationSpec.witness` by pattern matching with result type `(o : ObservationSpec) →
ObservationWitness o.value`. The displayed branches determine the recursive cases and their
returned values.

Use: `chebyshev2.LocalObstruction.theorem_6_1` uses this definition to establish the
identity stated in that declaration.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.
-/
def ObservationSpec.witness : (o : ObservationSpec) → ObservationWitness o.value
  | .ground => groundObservationWitness
  | .squareTrace => traceObservationWitness
  | .fredholm σ hσ hs => movingObservationWitness observationH σ hσ (hObservationWitness _ hs)
      (fun _ v => (observationH_finite_joint_analytic m_integrable m_continuous m_positive
        (fun i => smoothTest_integrable (v i)) (fun i => (v i).property.1.continuous)
        (fun i => (v i).property.2) hs).contDiffAt)
  | .fredholmSlope σ hσ hs => movingObservationWitness observationS σ hσ (sObservationWitness _ hs)
      (fun _ v => observationS_finite_joint_c1 m_integrable m_continuous m_positive
        (fun i => smoothTest_integrable (v i)) (fun i => (v i).property.1.continuous)
        (fun i => (v i).property.2) hs)

 /--
Defines `ObservationSpec.scalePositive` by pattern matching with result type `ObservationSpec →
ℝ → Prop`. The displayed branches determine the recursive cases and their returned values.

Use: `chebyshev2.LocalObstruction.ObservationSpec.scalePositive_near` uses this definition
to prove the eventual or almost-everywhere assertion `∀ᶠ κ in 𝓝
(groundCoupling m), o.scalePositive κ`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.
-/
def ObservationSpec.scalePositive : ObservationSpec → ℝ → Prop
  | .ground | .squareTrace => fun _ => True
  | .fredholm σ _ _ | .fredholmSlope σ _ _ => fun κ => 0<σ κ

 /--
Establishes the stated eventual or almost-everywhere assertion `∀ᶠ κ in 𝓝 (groundCoupling m),
o.scalePositive κ`.

Use: `chebyshev2.LocalObstruction.theorem_6_1` uses this assertion to establish the
identity stated in that declaration.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
theorem ObservationSpec.scalePositive_near (o : ObservationSpec) :
    ∀ᶠ κ in 𝓝 (groundCoupling m), o.scalePositive κ := by
  cases o with
  | ground | squareTrace => exact Filter.Eventually.of_forall (fun _ => trivial)
  | fredholm σ hc hs | fredholmSlope σ hc hs =>
    exact hc.continuousAt.eventually (Ioi_mem_nhds hs)

 /--
Defines `SmoothTest.uniformNorm` of type `ℝ` by `‖ofCompactSupport (v:ℝ → ℝ)
v.property.1.continuous v.property.2‖`.

Use: `chebyshev2.LocalObstruction.theorem_6_1` uses this definition to establish the
identity stated in that declaration.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.
-/
def SmoothTest.uniformNorm (v : SmoothTest) : ℝ :=
  ‖ofCompactSupport (v:ℝ → ℝ) v.property.1.continuous v.property.2‖

 /--
Constructs witnesses with the exact properties `∃ v : SmoothTest, SmoothTest.uniformNorm v<ε ∧
(∀ x,0≤m x+v x) ∧ (∫ x,m x+v x)=1 ∧ (∫ x,sqrt (m x+v x))=1 ∧ (fun i => (o i).value (m+(v:ℝ →
ℝ)))∈U ∧ (∀ i, (o i).scalePositive (groundCoupling (m+(v:ℝ → ℝ)))) ∧ densityEnergy (m+(v:ℝ →
ℝ))<Φ (fun i => (o i).value (m+(v:ℝ → ℝ)))`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev2, Theorem 6.1.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem theorem_6_1 {ι : Type*} [Fintype ι] (o : ι → ObservationSpec)
    {U : Set (ι → ℝ)} (hU : U∈𝓝 (fun i => (o i).value m)) (Φ : (ι → ℝ) → ℝ)
    (hΦ : ContDiffOn ℝ 1 Φ U) (heq : Φ (fun i => (o i).value m)=densityEnergy m)
    {ε : ℝ} (hε : 0<ε) :
    ∃ v : SmoothTest, SmoothTest.uniformNorm v<ε ∧
      (∀ x,0≤m x+v x) ∧ (∫ x,m x+v x)=1 ∧ (∫ x,sqrt (m x+v x))=1 ∧
      (fun i => (o i).value (m+(v:ℝ → ℝ)))∈U ∧
      (∀ i, (o i).scalePositive (groundCoupling (m+(v:ℝ → ℝ)))) ∧
      densityEnergy (m+(v:ℝ → ℝ))<Φ (fun i => (o i).value (m+(v:ℝ → ℝ))) := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  have hscales : ∀ v w : SmoothTest, 0<(∫ x,n x*w x) →
      ∀ᶠ t in 𝓝 (0:ℝ),∀ i,(o i).scalePositive
        (groundCoupling (curveDensity (amplitudeDirection v) w t)) := by
    intro v w hw
    have ht := (groundObservationWitness.curve_derivative v w hw).continuousAt.tendsto
    -- Record the convergence ht with its source filter and target limit before taking limits
    -- in the subsequent identities/bounds.
    have ht' : Tendsto (fun t => groundCoupling (curveDensity (amplitudeDirection v) w t))
        (𝓝 0) (𝓝 (groundCoupling m)) := by simpa only [curveDensity_zero] using ht
    exact ht'.eventually (Filter.eventually_all.mpr (fun i => (o i).scalePositive_near))
  obtain ⟨f,hfc,hfs,hfn,hfm,hfr,hsmall,⟨hobs,hsc⟩,hless⟩ :=
    finite_observation_no_local_bound_with_property
      (fun i => (o i).value) (fun i => (o i).witness) hU Φ (hΦ.contDiffAt hU) heq
      (fun f => ∀ i,(o i).scalePositive (groundCoupling f)) hscales hε
  let v : SmoothTest := ⟨fun x => f x-m x,hfc,hfs⟩
  have hv : m+(v:ℝ → ℝ)=f := by funext x;change m x+(f x-m x)=f x;ring
  have hnorm : SmoothTest.uniformNorm v<ε := by
    apply (norm_lt_iff_of_compactlySupported
      (ofCompactSupport_mem (v:ℝ → ℝ) hfc.continuous hfs) hε).mpr
    intro x
    exact hsmall x
  refine ⟨v,hnorm,?_,?_,?_,?_,?_,?_⟩
  · intro x
    change (m+(v:ℝ → ℝ)) x≥0
    rw [hv]
    exact hfn x
  · change (∫ x,(m+(v:ℝ → ℝ)) x)=1
    rw [hv]
    exact hfm
  · change (∫ x,sqrt ((m+(v:ℝ → ℝ)) x))=1
    rw [hv]
    exact hfr
  · rw [hv]
    exact hobs
  · rw [hv]
    exact hsc
  · rw [hv]
    exact hless

 /--
Defines `fixedObservationSpecs` by pattern matching with result type `Bool ⊕ (Fin r × Bool) →
ObservationSpec`. The displayed branches determine the recursive cases and their returned
values.

Use: a standalone supporting definition for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Theorem 6.1.
-/
def fixedObservationSpecs {r : ℕ} (σ : Fin r → ℝ) (hs : ∀ j,0<σ j) :
    Bool ⊕ (Fin r × Bool) → ObservationSpec
  | .inl true => .ground
  | .inl false => .squareTrace
  | .inr (j,true) => .fredholm (fun _ => σ j) contDiffAt_const (hs j)
  | .inr (j,false) => .fredholmSlope (fun _ => σ j) contDiffAt_const (hs j)

end
end chebyshev2.LocalObstruction
