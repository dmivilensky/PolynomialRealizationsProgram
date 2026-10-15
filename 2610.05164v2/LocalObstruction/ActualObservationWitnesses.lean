import «2610.05164v2».LocalObstruction.TailGradient
import «2610.05164v2».LocalObstruction.ObservationFunctions
import «2610.05164v2».LocalObstruction.GroundVariation
import «2610.05164v2».LocalObstruction.PairingFinite
import «2610.05164v2».LocalObstruction.GreenTail
import «2610.05164v2».LocalObstruction.GreenScaleTail

/-!
Article: 2610.05164v2, Theorem 6.1.
Constructed witnesses for every fixed-scale observation in Theorem 6.1.
Use: `«2610.05164v2».LocalObstruction.sObservationWitness` feeds
`«2610.05164v2».LocalObstruction.theorem_6_1` (theorem 6 1).
Proof chain: `«2610.05164v2».LocalObstruction.theorem_6_1` — 2610.05164v2, Theorem 6.1; No locally
sharp C1 bound from finitely many spectral observations.
-/
namespace «2610.05164v2».LocalObstruction
noncomputable section
open Set MeasureTheory Real Filter «2610.05164v2».SineContinuum «2610.05164v2».GroundState «2610.05164v2».Sobolev «2610.05164v2».Filters
open scoped Topology ContDiff
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

 /--
Integrability of the displayed function: `Integrable (v:ℝ → ℝ)`.

Use: `«2610.05164v2».LocalObstruction.groundObservationWitness` uses this integrability result
in the displayed construction of `groundObservationWitness`. Its inputs and component formulas
are fixed by that definition.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.groundObservationWitness`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem smoothTest_integrable (v : SmoothTest) : Integrable (v:ℝ → ℝ) :=
  v.property.1.continuous.integrable_of_hasCompactSupport v.property.2

 /--
Integrability of the displayed function: `Integrable (fun x => exp (-x)*m x)`.

Use: `«2610.05164v2».LocalObstruction.groundObservationWitness` uses this integrability result
in the displayed construction of `groundObservationWitness`. Its inputs and component formulas
are fixed by that definition.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.groundObservationWitness`.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.m_even`,
`«2610.05164v2».LocalObstruction.sine_first_moment_integrable` with the arguments shown in the
proof.
-/
theorem sine_left_moment_integrable : Integrable (fun x => exp (-x)*m x) := by simpa only [m_even] using sine_first_moment_integrable.comp_neg

 /--
Defines `sineGround` of type `GroundWitness m_integrable (fun x => (m_positive x).le)` by
`Classical.choice (ground_state m_integrable (fun x => (m_positive x).le) (by intro hz have hm0
: (∫ x,m x)=0 := by rw [integral_congr_ae hz];simp exact (positive_continuous_mass m_integrable
m_continuous m_positive).ne' hm0))`.

Use: `«2610.05164v2».LocalObstruction.groundGradient` uses this definition in the displayed
construction of `groundGradient`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.groundObservationWitness`.
-/
def sineGround : GroundWitness m_integrable (fun x => (m_positive x).le) :=
  Classical.choice (ground_state m_integrable (fun x => (m_positive x).le) (by
    intro hz
    have hm0 : (∫ x,m x)=0 := by rw [integral_congr_ae hz];simp
    exact (positive_continuous_mass m_integrable m_continuous m_positive).ne' hm0))

 /--
Constructs `groundSquareGradient` of type `TailGradient` by the displayed record fields. Data
fields specify the construction; proof fields discharge its required properties.

Use: `«2610.05164v2».LocalObstruction.groundGradient` uses this definition in the displayed
construction of `groundGradient`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.groundObservationWitness`.
-/
def groundSquareGradient : TailGradient where
  value x := (H1.rep sineGround.u x)^2
  continuous := (H1.continuous_rep sineGround.u).pow 2
  constant := 0
  exponential := Classical.choose (sine_ground_square_tail sineGround)
  tail := by simpa only [sub_zero] using Classical.choose_spec (sine_ground_square_tail sineGround)

 /--
Defines `groundGradient` of type `TailGradient` by `groundSquareGradient.smul (-groundParameter
m_integrable (fun x => (m_positive x).le)/ (∫ x,m x*(H1.rep sineGround.u x)^2))`.

Use: `«2610.05164v2».LocalObstruction.groundObservationWitness` uses this definition in the
displayed construction of `groundObservationWitness`. Its inputs and component formulas are
fixed by that definition.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.groundObservationWitness`.
-/
def groundGradient : TailGradient := groundSquareGradient.smul
  (-groundParameter m_integrable (fun x => (m_positive x).le)/
    (∫ x,m x*(H1.rep sineGround.u x)^2))

 /--
Constructs `groundObservationWitness` of type `ObservationWitness groundCoupling` by the
displayed record fields. Data fields specify the construction; proof fields discharge its
required properties.

Use: `«2610.05164v2».LocalObstruction.theorem_6_1` uses this definition to establish the
identity stated in that declaration.

Article: 2610.05164v2, Theorem 6.1.
-/
def groundObservationWitness : ObservationWitness groundCoupling where
  gradient := groundGradient
  regular h w := groundCoupling_finite_c1 m_integrable m_continuous m_positive sine_left_moment_integrable m_even
    (fun i => smoothTest_integrable (curveBasis h w i))
    (fun i => (curveBasis h w i).property.1.continuous) (fun i => (curveBasis h w i).property.2)
  variation v := by
    have h := groundCoupling_density_derivative m_integrable m_continuous m_positive
      sine_left_moment_integrable m_even (smoothTest_integrable v) v.property.1.continuous v.property.2 sineGround
    convert! h using 1
    change (∫ x,v x*((-groundParameter m_integrable (fun x => (m_positive x).le)/
      (∫ y,m y*(H1.rep sineGround.u y)^2))*(H1.rep sineGround.u x)^2))=_
    have he : (fun x => v x*((-groundParameter m_integrable (fun x => (m_positive x).le)/
      (∫ y,m y*(H1.rep sineGround.u y)^2))*(H1.rep sineGround.u x)^2))=
        fun x => (-groundParameter m_integrable (fun x => (m_positive x).le)/
          (∫ y,m y*(H1.rep sineGround.u y)^2))*(v x*(H1.rep sineGround.u x)^2) := by funext x;ring
    rw [he,integral_const_mul]
    ring

 /--
Constructs `traceGradient` of type `TailGradient` by the displayed record fields. Data fields
specify the construction; proof fields discharge its required properties.

Use: `«2610.05164v2».LocalObstruction.traceObservationWitness` uses this definition in the
displayed construction of `traceObservationWitness`. Its inputs and component formulas are
fixed by that definition.

Article: 2610.05164v2, Theorem 6.1 via `«2610.05164v2».LocalObstruction.theorem_6_1`.
-/
def traceGradient : TailGradient where
  value x := 2*W₂ m x
  continuous := continuous_const.mul (W₂_continuous m_integrable)
  constant := 0
  exponential := 2*sineTraceTailCoefficient
  tail := by
    have h := sine_convolution_tail.const_mul_left 2
    convert! h using 1
    funext x
    ring

 /--
Constructs `traceObservationWitness` of type `ObservationWitness (fun f => pairing f f)` by the
displayed record fields. Data fields specify the construction; proof fields discharge its
required properties.

Use: `«2610.05164v2».LocalObstruction.ObservationSpec.witness` uses this definition in the
displayed construction of `ObservationSpec.witness`. Its inputs and component formulas are
fixed by that definition.

Article: 2610.05164v2, Theorem 6.1 via `«2610.05164v2».LocalObstruction.theorem_6_1`.
-/
def traceObservationWitness : ObservationWitness (fun f => pairing f f) where
  gradient := traceGradient
  regular h w := (pairing_finite_smooth m_integrable
    (fun i => smoothTest_integrable (curveBasis h w i))).of_le (by norm_num : (1:ℕ∞ω)≤∞) |>.contDiffAt
  variation v := by
    have h := pairing_variation m_integrable (smoothTest_integrable v)
    convert! h using 1
    change (∫ x,v x*(2*W₂ m x))=2*(∫ x,v x*W₂ m x)
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => by dsimp only;ring)

 /--
Constructs `greenDiagonalGradient` of type `TailGradient` by the displayed record fields. Data
fields specify the construction; proof fields discharge its required properties.

Use: `«2610.05164v2».LocalObstruction.hObservationWitness` uses this definition in the
displayed construction of `hObservationWitness`. Its inputs and component formulas are fixed by
that definition.

Article: 2610.05164v2, Theorem 6.1 via `«2610.05164v2».LocalObstruction.theorem_6_1`.
-/
def greenDiagonalGradient (s : ℝ) (hs : 0≤s) : TailGradient where
  value x := greenKernel s m x x
  continuous := (greenKernel_continuous m_integrable (fun x => (m_positive x).le) hs).comp
    (continuous_id.prodMk continuous_id)
  constant := 1/2
  exponential := sineJostCoefficient s/(2*transmission s m)
  tail := sine_green_diagonal_tail hs

 /--
Constructs `greenScaleTailGradient` of type `TailGradient` by the displayed record fields. Data
fields specify the construction; proof fields discharge its required properties.

Use: `«2610.05164v2».LocalObstruction.sObservationWitness` uses this definition in the
displayed construction of `sObservationWitness`. Its inputs and component formulas are fixed by
that definition.

Article: 2610.05164v2, Theorem 6.1 via `«2610.05164v2».LocalObstruction.theorem_6_1`.
-/
def greenScaleTailGradient (s : ℝ) (hs : 0≤s) : TailGradient where
  value := greenScaleGradient s m
  continuous := greenScaleGradient_continuous m_integrable (fun x => (m_positive x).le) m_continuous hs m_even
  constant := 0
  exponential := sineGreenScaleCoefficient s
  tail := by simpa only [sub_zero] using sine_green_scale_tail hs

 /--
Constructs `hObservationWitness` of type `ObservationWitness (fun f => observationH f s)` by
the displayed record fields. Data fields specify the construction; proof fields discharge its
required properties.

Use: `«2610.05164v2».LocalObstruction.ObservationSpec.witness` uses this definition in the
displayed construction of `ObservationSpec.witness`. Its inputs and component formulas are
fixed by that definition.

Article: 2610.05164v2, Theorem 6.1 via `«2610.05164v2».LocalObstruction.theorem_6_1`.
-/
def hObservationWitness (s : ℝ) (hs : 0<s) : ObservationWitness (fun f => observationH f s) where
  gradient := (greenDiagonalGradient s hs.le).smul s
  regular h w := by
    have hf : ContDiffAt ℝ 1 (fun p : (Fin 5 → ℝ) × ℝ => observationH
        (perturb m (fun i x => curveBasis h w i x) p.1) p.2) (0,s) :=
      (observationH_finite_joint_analytic m_integrable m_continuous m_positive
        (fun i => smoothTest_integrable (curveBasis h w i))
        (fun i => (curveBasis h w i).property.1.continuous)
        (fun i => (curveBasis h w i).property.2) hs).contDiffAt
    exact hf.comp (f := fun a : Fin 5 → ℝ => (a,s)) 0 (contDiffAt_id.prodMk contDiffAt_const)
  variation v := by
    have h := observationH_density_derivative m_integrable m_continuous m_positive
      (smoothTest_integrable v) v.property.1.continuous v.property.2 hs m_even
    convert! h using 1
    change (∫ x,v x*(s*greenKernel s m x x))=s*(∫ x,greenKernel s m x x*v x)
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => by dsimp only;ring)

 /--
Constructs `sObservationWitness` of type `ObservationWitness (fun f => observationS f s)` by
the displayed record fields. Data fields specify the construction; proof fields discharge its
required properties.

Use: `«2610.05164v2».LocalObstruction.ObservationSpec.witness` uses this definition in the
displayed construction of `ObservationSpec.witness`. Its inputs and component formulas are
fixed by that definition.

Article: 2610.05164v2, Theorem 6.1 via `«2610.05164v2».LocalObstruction.theorem_6_1`.
-/
def sObservationWitness (s : ℝ) (hs : 0<s) : ObservationWitness (fun f => observationS f s) where
  gradient := (greenDiagonalGradient s hs.le).add ((greenScaleTailGradient s hs.le).smul s)
  regular h w := (observationS_finite_joint_c1 m_integrable m_continuous m_positive
    (fun i => smoothTest_integrable (curveBasis h w i))
    (fun i => (curveBasis h w i).property.1.continuous)
    (fun i => (curveBasis h w i).property.2) hs).comp (f := fun a : Fin 5 → ℝ => (a,s)) 0 (contDiffAt_id.prodMk contDiffAt_const)
  variation v := by
    have h := observationS_density_derivative m_integrable m_continuous m_positive
      (smoothTest_integrable v) v.property.1.continuous v.property.2 hs m_even
    convert! h using 1
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => by dsimp only [TailGradient.add,TailGradient.smul,
      greenDiagonalGradient,greenScaleTailGradient];ring)

end
end «2610.05164v2».LocalObstruction
