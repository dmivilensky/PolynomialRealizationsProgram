import chebyshev2.DualCertificate.NormalizedStates
import chebyshev2.DualCertificate.ReflectedFilters

/-!
Article: chebyshev2, Lemma 16.
Smoothness of all normalized comparison state inputs on the closed cubic charts.
Result: `chebyshev2.DualCertificate.NormalizedCalibration.Rzero_smooth` supplies the stated
article conclusion.
-/
namespace chebyshev2.DualCertificate.NormalizedCalibration
noncomputable section
open Set chebyshev2.Calibration
open scoped ContDiff
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable (N : chebyshev2.DualCertificate.NormalizedCalibration) {κ : ℝ} (hκ : 0<κ)

include hκ in
/--
Smoothness to the stated order: `ContDiffOn ℝ ∞ (N.speed κ) (Icc (0:ℝ) 1)`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 16.

Proof: Use the identities/estimates
`chebyshev2.DualCertificate.NormalizedCalibration.speed_smooth` with the arguments shown in
the proof.
-/
theorem speed_smooth_fixed : ContDiffOn ℝ ∞ (N.speed κ) (Icc (0:ℝ) 1) :=
  N.speed_smooth.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ ht => ⟨hκ,ht⟩)

/--
Smoothness to the stated order: `ContDiffOn ℝ ∞ (N.leftU hκ s) (Icc (0:ℝ) 1)`.

Use: `chebyshev2.DualCertificate.NormalizedCalibration.R_smooth` uses this assertion to
establish smoothness to the stated order: `ContDiffOn ℝ ∞ (N.R side hκ s) (Icc (0:ℝ) 1)`.

Article: chebyshev2, Lemma 16 via
`chebyshev2.DualCertificate.NormalizedCalibration.R_smooth`.

Proof: Use the identities/estimates
`chebyshev2.DualCertificate.NormalizedCalibration.defectQuotient_smooth` with the arguments
shown in the proof.
-/
theorem leftU_smooth {s : ℝ} (hs : 0<s) :
    ContDiffOn ℝ ∞ (N.leftU hκ s) (Icc (0:ℝ) 1) :=
  contDiffOn_const.sub (N.defectQuotient_smooth hκ hs)

/--
Smoothness to the stated order: `ContDiffOn ℝ ∞ (N.leftTheta hκ) (Icc (0:ℝ) 1)`.

Use: `chebyshev2.DualCertificate.NormalizedCalibration.Rzero_smooth` uses this assertion to
establish smoothness to the stated order: `ContDiffOn ℝ ∞ (N.Rzero side hκ) (Icc (0:ℝ) 1)`.

Article: chebyshev2, Lemma 16 via
`chebyshev2.DualCertificate.NormalizedCalibration.Rzero_smooth`.

Proof: Use the identities/estimates
`chebyshev2.DualCertificate.NormalizedCalibration.linearDefectQuotient_smooth` with the
arguments shown in the proof.
-/
theorem leftTheta_smooth : ContDiffOn ℝ ∞ (N.leftTheta hκ) (Icc (0:ℝ) 1) :=
  N.linearDefectQuotient_smooth hκ

variable (hΓ : ∀ q∈Icc (0:ℝ) 2,N.calibration.Gamma (2-q)=N.calibration.Gamma q)

include hΓ in
/--
Smoothness to the stated order: `ContDiffOn ℝ ∞ (N.farFilter hκ s) (Icc (0:ℝ) 1)`.

Use: `chebyshev2.DualCertificate.NormalizedCalibration.R_smooth` uses this assertion to
establish smoothness to the stated order: `ContDiffOn ℝ ∞ (N.R side hκ s) (Icc (0:ℝ) 1)`.

Article: chebyshev2, Lemma 16 via
`chebyshev2.DualCertificate.NormalizedCalibration.R_smooth`.

Proof: Use the identities/estimates
`chebyshev2.DualCertificate.NormalizedCalibration.reflectedFilter_smooth`,
`chebyshev2.DualCertificate.cube_mem` with the arguments shown in the proof.
-/
theorem farFilter_smooth {s : ℝ} (hs : 0≤s) :
    ContDiffOn ℝ ∞ (N.farFilter hκ s) (Icc (0:ℝ) 1) :=
  (N.reflectedFilter_smooth hΓ hκ hs).div (by fun_prop)
    (fun t ht => by linarith [(cube_mem ht).2])
include hΓ in
/--
Smoothness to the stated order: `ContDiffOn ℝ ∞ (N.farLinear hκ) (Icc (0:ℝ) 1)`.

Use: `chebyshev2.DualCertificate.NormalizedCalibration.Rzero_smooth` uses this assertion to
establish smoothness to the stated order: `ContDiffOn ℝ ∞ (N.Rzero side hκ) (Icc (0:ℝ) 1)`.

Article: chebyshev2, Lemma 16 via
`chebyshev2.DualCertificate.NormalizedCalibration.Rzero_smooth`.

Proof: Use the identities/estimates
`chebyshev2.DualCertificate.NormalizedCalibration.reflectedLinear_smooth`,
`chebyshev2.DualCertificate.cube_mem` with the arguments shown in the proof.
-/
theorem farLinear_smooth : ContDiffOn ℝ ∞ (N.farLinear hκ) (Icc (0:ℝ) 1) :=
  (N.reflectedLinear_smooth hΓ hκ).div (by fun_prop)
    (fun t ht => by linarith [(cube_mem ht).2])
include hΓ in
/--
Smoothness to the stated order: `ContDiffOn ℝ ∞ (N.U side hκ s) (Icc (0:ℝ) 1)`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 16.

Proof: Use the identities/estimates
`chebyshev2.DualCertificate.NormalizedCalibration.leftU_smooth`,
`chebyshev2.DualCertificate.NormalizedCalibration.farFilter_smooth` with the arguments
shown in the proof.
-/
theorem U_smooth (side : Side) {s : ℝ} (hs : 0<s) :
    ContDiffOn ℝ ∞ (N.U side hκ s) (Icc (0:ℝ) 1) := by
  cases side with
  | left => exact N.leftU_smooth hκ hs
  | right => exact contDiffOn_const.mul (N.farFilter_smooth hκ hΓ hs.le)

include hΓ in
/--
Smoothness to the stated order: `ContDiffOn ℝ ∞ (N.theta side hκ) (Icc (0:ℝ) 1)`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 16.

Proof: Use the identities/estimates
`chebyshev2.DualCertificate.NormalizedCalibration.leftTheta_smooth`,
`chebyshev2.DualCertificate.NormalizedCalibration.farLinear_smooth` with the arguments
shown in the proof.
-/
theorem theta_smooth (side : Side) :
    ContDiffOn ℝ ∞ (N.theta side hκ) (Icc (0:ℝ) 1) := by
  cases side with
  | left => exact N.leftTheta_smooth hκ
  | right => exact contDiffOn_const.sub (N.farLinear_smooth hκ hΓ)

include hΓ in
/--
Smoothness to the stated order: `ContDiffOn ℝ ∞ (N.R side hκ s) (Icc (0:ℝ) 1)`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev2, Lemma 16.

Proof: Use the identities/estimates
`chebyshev2.DualCertificate.NormalizedCalibration.farFilter_smooth`,
`chebyshev2.DualCertificate.NormalizedCalibration.leftU_smooth` with the arguments shown in
the proof.
-/
theorem R_smooth (side : Side) {s : ℝ} (hs : 0<s) :
    ContDiffOn ℝ ∞ (N.R side hκ s) (Icc (0:ℝ) 1) := by
  cases side with
  | left => exact N.farFilter_smooth hκ hΓ hs.le
  | right => exact contDiffOn_const.mul (N.leftU_smooth hκ hs)

include hΓ in
/--
Smoothness to the stated order: `ContDiffOn ℝ ∞ (N.Rzero side hκ) (Icc (0:ℝ) 1)`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev2, Lemma 16.

Proof: Use the identities/estimates
`chebyshev2.DualCertificate.NormalizedCalibration.farLinear_smooth`,
`chebyshev2.DualCertificate.NormalizedCalibration.leftTheta_smooth` with the arguments
shown in the proof.
-/
theorem Rzero_smooth (side : Side) :
    ContDiffOn ℝ ∞ (N.Rzero side hκ) (Icc (0:ℝ) 1) := by
  cases side with
  | left => exact N.farLinear_smooth hκ hΓ
  | right => exact contDiffOn_const.sub (N.leftTheta_smooth hκ)

end
end chebyshev2.DualCertificate.NormalizedCalibration
