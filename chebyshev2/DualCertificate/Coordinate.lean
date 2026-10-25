import chebyshev2.Calibration.Amplitude

/-!
Article: chebyshev2, Lemma 16.
The two cubic endpoint coordinates of Section 3.7 and F.1.
Use: `chebyshev2.DualCertificate.Side.Q` feeds
`chebyshev2.DualCertificate.NormalizedCalibration.traceTerm_identity` (trace Term identity).
Proof chain: `chebyshev2.DualCertificate.Data.admissible_analytic` — chebyshev2, Theorem E.1;
Stability of strict admissibility and uniform transfer of the certificate value.
-/
namespace chebyshev2.DualCertificate
noncomputable section
open Set chebyshev2.Calibration

/--
Defines the alternatives used to distinguish the cases in the subsequent construction.

Use: `chebyshev2.DualCertificate.Side.q_interior` uses this definition to establish
membership in the specified domain/enclosure: `side.q t ∈ Ioo (0:ℝ) 2`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.
-/
inductive Side
  /-- The left half of the ground-coordinate interval, parametrized by q=t³. -/
  | left
  /-- The reflected right half, parametrized by q=2-t³. -/
  | right
  deriving DecidableEq

/--
Supplies the typeclass structure specified by `Fintype Side`. This lets subsequent generic
library results apply to this concrete type.

Use: supplies this typeclass to generic library results in the module; instance resolution
inserts it where required by their signatures.

Article: chebyshev2, Lemma 16.
-/
instance : Fintype Side := ⟨{Side.left,Side.right}, by intro x; cases x <;> simp⟩

/--
Defines `Side.q` by pattern matching with result type `Side → ℝ → ℝ`. The displayed branches
determine the recursive cases and their returned values.

Use: `chebyshev2.DualCertificate.Side.q_interior` uses this definition to establish
membership in the specified domain/enclosure: `side.q t ∈ Ioo (0:ℝ) 2`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.
-/
def Side.q : Side → ℝ → ℝ
  | .left, t => t^3
  | .right, t => 2-t^3

/--
Membership in the specified domain/enclosure: `t^3 ∈ Icc (0:ℝ) 1`.

Use: `chebyshev2.DualCertificate.Side.q_interior` uses this assertion to establish
membership in the specified domain/enclosure: `side.q t ∈ Ioo (0:ℝ) 2`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem cube_mem {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : t^3 ∈ Icc (0:ℝ) 1 :=
  ⟨pow_nonneg ht.1 _,pow_le_one₀ ht.1 ht.2⟩

/--
Membership in the specified domain/enclosure: `side.q t ∈ Icc (0:ℝ) 2`.

Use: `chebyshev2.DualCertificate.NormalizedCalibration.farFilter_range` uses this assertion
to establish membership in the specified domain/enclosure: `N.farFilter hκ s t∈Icc (0:ℝ)
(s/κ)`.

Article: chebyshev2, Theorem E.1 via `chebyshev2.DualCertificate.Data.admissible_stable`.

Proof: Use the identities/estimates `chebyshev2.DualCertificate.cube_mem` with the
arguments shown in the proof.
-/
theorem Side.q_mem (side : Side) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    side.q t ∈ Icc (0:ℝ) 2 := by
  have hc := cube_mem ht
  cases side <;> dsimp [Side.q] <;> constructor <;> linarith [hc.1,hc.2]

/--
Membership in the specified domain/enclosure: `side.q t ∈ Ioo (0:ℝ) 2`.

Use: `chebyshev2.Calibration.ReferenceData.normalizedGamma_factor` uses this assertion to
establish exact identity `(R.calibration hσ hb homega).Gamma (t^3)=Q (t^3)*R.normalizedGamma hσ
t`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `chebyshev2.DualCertificate.cube_mem` with the
arguments shown in the proof.
-/
theorem Side.q_interior (side : Side) {t : ℝ} (ht : t ∈ Ioc (0:ℝ) 1) :
    side.q t ∈ Ioo (0:ℝ) 2 := by
  have hc := cube_mem ⟨ht.1.le,ht.2⟩
  have hp : 0<t^3 := pow_pos ht.1 _
  cases side <;> dsimp [Side.q] <;> constructor <;> linarith [hc.2]

/--
Exact identity `chebyshev2.Calibration.Q (side.q t)=t^3*(2-t^3)`.

Use: `chebyshev2.DualCertificate.NormalizedCalibration.certificateB_identity` uses this
identity to establish the identity stated in that declaration.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem Side.Q (side : Side) (t : ℝ) :
    chebyshev2.Calibration.Q (side.q t)=t^3*(2-t^3) := by
  cases side with
  | left => rfl
  | right => dsimp [Side.q,chebyshev2.Calibration.Q]; ring

end
end chebyshev2.DualCertificate
