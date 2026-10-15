import «2610.05164v2».DualCertificate.CenteredCoefficients
import «2610.05164v2».DualCertificate.Cancellation
import «2610.05164v2».Comparison.Integrability

/-!
Article: 2610.05164v2, Lemma 16.
The determinant and trace comparison multipliers in the closed cubic charts.
Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.traceTerm_identity` feeds
`«2610.05164v2».DualCertificate.NormalizedCalibration.certificateB_identity` (certificate B
identity).
Proof chain: `«2610.05164v2».DualCertificate.Data.admissible_analytic` — 2610.05164v2, Theorem E.1;
Stability of strict admissibility and uniform transfer of the certificate value.
-/
namespace «2610.05164v2».DualCertificate.NormalizedCalibration
noncomputable section
open Set «2610.05164v2».Calibration «2610.05164v2».Comparison
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable (N : «2610.05164v2».DualCertificate.NormalizedCalibration)

/--
Defines `determinantTerm` of type `ℝ` by `-s*(2-t^3)*(1+U*N.R side hκ s t)/ (N.speed κ t*N.root
κ t*(2+side.q t*(s/κ)*U+(2-side.q t)*N.R side hκ s t))`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.determinantTerm_identity` uses this
definition to establish `N.determinantTerm side hκ s t U=
N.calibration.comparisonA hκ s (side.q t) (side.q t*(s/κ)*U)/(t*N.root κ t)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def determinantTerm (side : Side) {κ : ℝ} (hκ : 0<κ) (s t U : ℝ) : ℝ :=
  -s*(2-t^3)*(1+U*N.R side hκ s t)/
    (N.speed κ t*N.root κ t*(2+side.q t*(s/κ)*U+(2-side.q t)*N.R side hκ s t))

/--
Defines `traceTerm` of type `ℝ` by `κ*(2-t^3)/(2*N.speed κ t*N.root κ t)* (2*(1-θ)*N.Rzero side
hκ t-side.q t*(1-θ)-(2-side.q t)*N.Rzero side hκ t)`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.traceTerm_identity` uses this
definition to establish `N.traceTerm side hκ t θ=
N.calibration.comparisonA0 hκ (side.q t) (side.q t*(1-θ))/(t*N.root κ t)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def traceTerm (side : Side) {κ : ℝ} (hκ : 0<κ) (t θ : ℝ) : ℝ :=
  κ*(2-t^3)/(2*N.speed κ t*N.root κ t)*
    (2*(1-θ)*N.Rzero side hκ t-side.q t*(1-θ)-(2-side.q t)*N.Rzero side hκ t)

/--
The stated quantitative bound `2≤2+side.q t*(s/κ)*U+(2-side.q t)*N.R side hκ s t`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.determinantTerm_identity` uses this
bound to establish `N.determinantTerm side hκ s t U=
N.calibration.comparisonA hκ s (side.q t) (side.q t*(s/κ)*U)/(t*N.root κ t)`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Proof: Use the identities/estimates `«2610.05164v2».DualCertificate.determinant_denominator`,
`«2610.05164v2».DualCertificate.Side.q_mem`,
`«2610.05164v2».DualCertificate.NormalizedCalibration.R_range` with the arguments shown in the
proof.
-/
theorem determinantTerm_denominator (side : Side) {κ s t U : ℝ}
    (hκ : 0<κ) (hs : 0<s) (ht : t∈Icc (0:ℝ) 1) (hU : U∈Icc (0:ℝ) 1) :
    2≤2+side.q t*(s/κ)*U+(2-side.q t)*N.R side hκ s t :=
  determinant_denominator (side.q_mem ht) hU (div_pos hs hκ) (N.R_range side hκ hs ht).1

variable (hΓ : ∀ q∈Icc (0:ℝ) 2,N.calibration.Gamma (2-q)=N.calibration.Gamma q)

include hΓ in
/--
Exact identity `(2-side.q t)*N.R side hκ s t=N.calibration.rightFilter hκ s (side.q t)`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.determinantTerm_identity` rewrites
with this identity to establish `N.determinantTerm side hκ s t U=
N.calibration.comparisonA hκ s (side.q t) (side.q t*(s/κ)*U)/(t*N.root κ t)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem R_factor (side : Side) {κ s t : ℝ} (hκ : 0<κ) (hs : 0<s)
    (ht : t∈Ioc (0:ℝ) 1) :
    (2-side.q t)*N.R side hκ s t=N.calibration.rightFilter hκ s (side.q t) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  rw [N.rightFilter_reflection hΓ hκ]
  cases side with
  | left =>
    dsimp [R,farFilter,Side.q]
    field_simp [show 2-t^3≠0 by linarith [(cube_mem ⟨ht.1.le,ht.2⟩).2]]
  | right =>
    dsimp [R,Side.q]
    rw [sub_sub_cancel]
    have he := N.leftU_factor hκ hs ht
    field_simp [hκ.ne',hs.ne'] at he ⊢
    nlinarith [he]

include hΓ in
/--
Exact identity `(2-side.q t)*N.Rzero side hκ t=N.calibration.rightLinear hκ (side.q t)`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.traceTerm_identity` rewrites with
this identity to establish `N.traceTerm side hκ t θ=
N.calibration.comparisonA0 hκ (side.q t) (side.q t*(1-θ))/(t*N.root κ t)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem Rzero_factor (side : Side) {κ t : ℝ} (hκ : 0<κ)
    (ht : t∈Ioc (0:ℝ) 1) :
    (2-side.q t)*N.Rzero side hκ t=N.calibration.rightLinear hκ (side.q t) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  rw [N.rightLinear_reflection hΓ hκ]
  cases side with
  | left =>
    dsimp [Rzero,farLinear,Side.q]
    field_simp [show 2-t^3≠0 by linarith [(cube_mem ⟨ht.1.le,ht.2⟩).2]]
  | right =>
    dsimp [Rzero,Side.q]
    rw [sub_sub_cancel]
    have he := N.leftTheta_factor hκ ht
    nlinarith [he]

include hΓ in
/--
The precise assertion is `N.determinantTerm side hκ s t U= N.calibration.comparisonA hκ s
(side.q t) (side.q t*(s/κ)*U)/(t*N.root κ t)`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.certificateB_identity` rewrites with
this identity to establish the identity stated in that declaration.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem determinantTerm_identity (side : Side) {κ s t U : ℝ}
    (hκ : 0<κ) (hs : 0<s) (ht : t∈Ioc (0:ℝ) 1) (hU : U∈Icc (0:ℝ) 1) :
    N.determinantTerm side hκ s t U=
      N.calibration.comparisonA hκ s (side.q t) (side.q t*(s/κ)*U)/(t*N.root κ t) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  rw [«2610.05164v2».Calibration.Data.comparisonA,ite_eq_left (side.q_interior ht)]
  unfold determinantCoefficient
  rw [← N.R_factor hΓ side hκ hs ht,N.side_speed hΓ side hκ ⟨ht.1.le,ht.2⟩,side.Q]
  unfold determinantTerm
  have hd : 2+side.q t*(s/κ)*U+(2-side.q t)*N.R side hκ s t≠0 :=
    ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ)<2) (N.determinantTerm_denominator side hκ hs ⟨ht.1.le,ht.2⟩ hU))
  field_simp [hκ.ne',ht.1.ne',(N.root_spec hκ ⟨ht.1.le,ht.2⟩).1.ne',
    (N.speed_positive hκ ⟨ht.1.le,ht.2⟩).ne',hd]
  have hQ := side.Q t
  unfold «2610.05164v2».Calibration.Q at hQ
  cases side <;> dsimp [Side.q] at * <;> ring

include hΓ in
/--
The precise assertion is `N.traceTerm side hκ t θ= N.calibration.comparisonA0 hκ (side.q t)
(side.q t*(1-θ))/(t*N.root κ t)`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.certificateB_identity` rewrites with
this identity to establish the identity stated in that declaration.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem traceTerm_identity (side : Side) {κ t θ : ℝ} (hκ : 0<κ)
    (ht : t∈Ioc (0:ℝ) 1) :
    N.traceTerm side hκ t θ=
      N.calibration.comparisonA0 hκ (side.q t) (side.q t*(1-θ))/(t*N.root κ t) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  rw [«2610.05164v2».Calibration.Data.comparisonA0,ite_eq_left (side.q_interior ht)]
  unfold traceCoefficient
  rw [← N.Rzero_factor hΓ side hκ ht,N.side_speed hΓ side hκ ⟨ht.1.le,ht.2⟩,side.Q]
  unfold traceTerm
  field_simp [ht.1.ne',(N.root_spec hκ ⟨ht.1.le,ht.2⟩).1.ne',
    (N.speed_positive hκ ⟨ht.1.le,ht.2⟩).ne']
  have hQ := side.Q t
  unfold «2610.05164v2».Calibration.Q at hQ
  cases side <;> dsimp [Side.q] at * <;> ring

end
end «2610.05164v2».DualCertificate.NormalizedCalibration
