import «2610.05164v2».DualCertificate.PriceAssembly
import «2610.05164v2».DualCertificate.NormalizedCertificate
import «2610.05164v2».DualCertificate.EnergyBound
import «2610.05164v2».StateRegion.OriginalAttainment

/-!
Article: 2610.05164v2, Theorem 3.6.
Definition 8 and its implication to the actual state residual.
Use: `«2610.05164v2».DualCertificate.Data.admissible_analytic` feeds
`«2610.05164v2».DualCertificate.Data.relaxed_energy_ge_value` (Theorem 3.6(i) for the literal
rational certificate, with exactly its numerically checked strict cell inequalities as the remaining
premises).
-/
namespace «2610.05164v2».DualCertificate.Data
noncomputable section
open Set Real «2610.05164v2».Residual «2610.05164v2».Calculus «2610.05164v2».Calibration
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable (D : «2610.05164v2».DualCertificate.Data)

/--
Defines `B` of type `ℝ` by `D.normalization.certificateB D.potential side hκ D.ξ₀ D.ξ₁ D.χ D.τ
t U V θ`.

Use: `«2610.05164v2».DualCertificate.Data.Admissible` uses this definition in the displayed
construction of `Admissible`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def B (side : Side) {κ : ℝ} (hκ : 0<κ) (t U V θ : ℝ) : ℝ :=
  D.normalization.certificateB D.potential side hκ D.ξ₀ D.ξ₁ D.χ D.τ t U V θ

/--
Defines `C` of type `ℝ` by `D.potential.centeredC D.normalization side hκ t U V θ`.

Use: `«2610.05164v2».DualCertificate.Data.Admissible` uses this definition in the displayed
construction of `Admissible`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def C (side : Side) {κ : ℝ} (hκ : 0<κ) (t U V θ : ℝ) : ℝ :=
  D.potential.centeredC D.normalization side hκ t U V θ

/--
Defines `Admissible` of type `Prop`. The displayed construction fixes its component data; its
proof fields enforce the listed compatibility properties.

Use: `«2610.05164v2».DualCertificate.Data.admissible_analytic` uses this definition to
establish the precise assertion is `D.analytic.Admissible hκ`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def Admissible {κ : ℝ} (hκ : 0<κ) : Prop :=
  ∀ side i,∀ t∈Icc ((D.cells side).lo i:ℝ) ((D.cells side).hi i:ℝ),
    ∀ U∈Icc (0:ℝ) 1,∀ T∈Icc (0:ℝ) 1,
      criterion (D.B side hκ t U ((scales hκ).V U T) ((scales hκ).thetaMinus U T))
        (D.C side hκ t U ((scales hκ).V U T) ((scales hκ).thetaMinus U T))
        ((D.cells side).affine i t) (D.normalization.certificateL κ t)<0 ∧
      criterion (D.B side hκ t U ((scales hκ).V U T) ((scales hκ).thetaPlus U T))
        (D.C side hκ t U ((scales hκ).V U T) ((scales hκ).thetaPlus U T))
        ((D.cells side).affine i t) (D.normalization.certificateL κ t)<0

/--
The stated quantitative bound `criterion (D.B side hκ t U V θ) (D.C side hκ t U V θ) ((D.cells
side).value t) (D.normalization.certificateL κ t)<0`.

Use: `«2610.05164v2».DualCertificate.Data.normalized_residual_of_admissible` uses this bound to
establish establishes the uniform, quantified assertion `∀ n : ℝ,0≤n →
0≤D.calibration.stateResidual hκ D.ξ₀ D.ξ₁ D.χ D.τ (D.price hκ) (D.statePotential κ)
(PolynomialPotential.unnormalize κ (side.q t,U,V,θ)) n`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».DualCertificate.Cells.index_mem`,
`«2610.05164v2».DualCertificate.NormalizedCalibration.actual_face_reduction` with the arguments
shown in the proof.
-/
theorem normalized_criterion_of_admissible {κ : ℝ} (hκ : 0<κ) (ha : D.Admissible hκ)
    (side : Side) {t U V θ : ℝ} (ht : t∈Icc (0:ℝ) 1)
    (hstate : (U,V,θ)∈(scales hκ).normalized) :
    criterion (D.B side hκ t U V θ) (D.C side hκ t U V θ)
      ((D.cells side).value t) (D.normalization.certificateL κ t)<0 := by
  -- Use the identities/estimates `«2610.05164v2».DualCertificate.Cells.index_mem`,
  -- `«2610.05164v2».DualCertificate.NormalizedCalibration.actual_face_reduction` with the
  -- arguments shown in the proof.
  obtain ⟨hU,T,hT,hV,hθ⟩ := hstate
  dsimp only at hU hV hθ
  subst V
  let i := (D.cells side).index t ht
  have hi := ha side i t ((D.cells side).index_mem ht) U hU T hT
  have hface := D.normalization.actual_face_reduction D.potential side hκ
    D.ξ₀ D.ξ₁ D.χ D.τ t U ((scales hκ).V U T) ((D.cells side).affine i t)
    ((scales hκ).thetaMinus U T) ((scales hκ).thetaPlus U T) θ hθ
  have he : (D.cells side).value t=(D.cells side).affine i t := by
    rw [Cells.value,dite_eq_left ht]
  rw [he]
  exact hface.trans_lt (max_lt hi.1 hi.2)

/--
Defines `statePotential` of type `State → ℝ` by `if hκ : 0<κ then D.potential.centered
D.normalization hκ else fun _ => 0`.

Use: `«2610.05164v2».DualCertificate.Data.analytic` uses this definition in the displayed
construction of `analytic`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def statePotential (κ : ℝ) : State → ℝ :=
  if hκ : 0<κ then D.potential.centered D.normalization hκ else fun _ => 0

/--
Smoothness to the stated order: `ContDiff ℝ 1 (D.statePotential κ)`.

Use: `«2610.05164v2».DualCertificate.Data.analytic` uses this assertion in the displayed
construction of `analytic`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`«2610.05164v2».DualCertificate.PolynomialPotential.centered_c1`,
`«2610.05164v2».DualCertificate.Data.Gamma_symmetric` with the arguments shown in the proof.
-/
theorem potential_c1 {κ : ℝ} (hκ : 0<κ) : ContDiff ℝ 1 (D.statePotential κ) := by
  rw [statePotential,dite_eq_left hκ]
  exact D.potential.centered_c1 D.normalization (fun _ hq => D.Gamma_symmetric hq) hκ

/--
Exact identity `D.statePotential κ (0,0,0,0)=D.statePotential κ (2,0,0,2)`.

Use: `«2610.05164v2».DualCertificate.Data.analytic` uses this identity in the displayed
construction of `analytic`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`«2610.05164v2».DualCertificate.PolynomialPotential.centered_boundary` with the arguments shown
in the proof.
-/
theorem potential_boundary {κ : ℝ} (hκ : 0<κ) :
    D.statePotential κ (0,0,0,0)=D.statePotential κ (2,0,0,2) := by
  rw [statePotential,dite_eq_left hκ]
  exact D.potential.centered_boundary D.normalization hκ

/--
Constructs `analytic` of type `AnalyticData` by the displayed record fields. Data fields
specify the construction; proof fields discharge its required properties.

Use: `«2610.05164v2».DualCertificate.Data.admissible_analytic` uses this definition to
establish the precise assertion is `D.analytic.Admissible hκ`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def analytic : AnalyticData where
  calibration := D.calibration
  ξ₀ := D.ξ₀
  ξ₁ := D.ξ₁
  χ := D.χ
  τ := D.τ
  price := fun _ hκ => D.price hκ
  potential := D.statePotential
  smooth := fun _ hκ => D.potential_c1 hκ
  boundary := fun _ hκ => D.potential_boundary hκ

 /--
Exact identity `D.calibration.stateResidual hκ D.ξ₀ D.ξ₁ D.χ D.τ (D.price hκ) (D.statePotential
κ) Y 0=0`.

Use: `«2610.05164v2».DualCertificate.Data.admissible_analytic` uses this identity to establish
the precise assertion is `D.analytic.Admissible hκ`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`«2610.05164v2».DualCertificate.PolynomialPotential.centered_d_endpoints`,
`«2610.05164v2».DualCertificate.Data.Gamma_symmetric`,
`«2610.05164v2».Calibration.Data.amplitude_zero` with the arguments shown in the proof.
-/
theorem boundary_residual {κ : ℝ} (hκ : 0<κ) {Y : State}
    (hY : Y∈(scales hκ).states) (hq : Y.1=0 ∨ Y.1=2) :
    D.calibration.stateResidual hκ D.ξ₀ D.ξ₁ D.χ D.τ (D.price hκ) (D.statePotential κ) Y 0=0 := by
  -- Use the identities/estimates
  -- `«2610.05164v2».DualCertificate.PolynomialPotential.centered_d_endpoints`,
  -- `«2610.05164v2».DualCertificate.Data.Gamma_symmetric`,
  -- `«2610.05164v2».Calibration.Data.amplitude_zero` with the arguments shown in the proof.
  have hz : Y.1=0 ∧ Y.2.1=0 ∧ Y.2.2.1=0 ∧ Y.2.2.2=0 ∨ Y.1=2 := by
    rcases hq with hq | hq
    · left
      rcases hY with ⟨⟨q,U,V,θ⟩,_,rfl⟩
      change q=0 at hq
      simp [«2610.05164v2».StateRegion.Scales.stateLift,hq]
    · exact Or.inr hq
  have hd : dPotential (D.statePotential κ) Y=0 := by
    rw [statePotential,dite_eq_left hκ]
    exact D.potential.centered_d_endpoints D.normalization (fun _ hq => D.Gamma_symmetric hq) hκ hz
  have hν : D.calibration.amplitude κ Y.1=0 := by
    rcases hq with hq | hq <;> rw [hq]
    · exact D.calibration.amplitude_zero κ
    · exact D.calibration.amplitude_two κ
  have hQ : Q Y.1=0 := by rcases hq with hq | hq <;> simp [Q,hq]
  simp [«2610.05164v2».Calibration.Data.stateResidual,«2610.05164v2».Residual.residual,rho,hν,hQ,hd]

 /--
Establishes the uniform, quantified assertion `∀ n : ℝ,0≤n → 0≤D.calibration.stateResidual hκ
D.ξ₀ D.ξ₁ D.χ D.τ (D.price hκ) (D.statePotential κ) (PolynomialPotential.unnormalize κ (side.q
t,U,V,θ)) n`.

Use: `«2610.05164v2».DualCertificate.Data.admissible_analytic` uses this bound to establish the
precise assertion is `D.analytic.Admissible hκ`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».StateRegion.Scales.normalized_bounds`,
`«2610.05164v2».DualCertificate.NormalizedCalibration.actual_normalized_criterion`,
`«2610.05164v2».DualCertificate.Data.Gamma_symmetric` with the arguments shown in the proof.
-/
theorem normalized_residual_of_admissible {κ t U V θ : ℝ} (hκ : 0<κ)
    (ha : D.Admissible hκ) (side : Side) (ht : t∈Ioc (0:ℝ) 1)
    (hstate : (U,V,θ)∈(scales hκ).normalized)
    (hprice : D.cellPrice (side.q t)=(D.cells side).value t) :
    ∀ n : ℝ,0≤n → 0≤D.calibration.stateResidual hκ D.ξ₀ D.ξ₁ D.χ D.τ (D.price hκ)
      (D.statePotential κ) (PolynomialPotential.unnormalize κ (side.q t,U,V,θ)) n := by
  -- Use the identities/estimates `«2610.05164v2».StateRegion.Scales.normalized_bounds`,
  -- `«2610.05164v2».DualCertificate.NormalizedCalibration.actual_normalized_criterion`,
  -- `«2610.05164v2».DualCertificate.Data.Gamma_symmetric` with the arguments shown in the
  -- proof.
  have hb := (scales hκ).normalized_bounds hstate
  have h := (D.normalization.actual_normalized_criterion D.potential
    (fun _ hq => D.Gamma_symmetric hq) side hκ ht hb.1 hb.2.1
      D.ξ₀ D.ξ₁ D.χ D.τ θ ((D.cells side).value t)).mpr
    (D.normalized_criterion_of_admissible hκ ha side ⟨ht.1.le,ht.2⟩ hstate).le
  rw [D.normalization_calibration] at h
  intro n hn
  convert! h n hn using 1
  unfold «2610.05164v2».Calibration.Data.stateResidual PolynomialPotential.unnormalize
  rw [D.price_interior hκ (side.q_interior ht),hprice,statePotential,dite_eq_left hκ]

 /--
The precise assertion is `D.analytic.Admissible hκ`.

Use: `«2610.05164v2».DualCertificate.Data.relaxed_energy_ge_value` uses this assertion to
establish the stated quantitative bound `D.analytic.targetValue≤∫ x,(sqrt (m.value x))^3`.

Article: 2610.05164v2, Theorem 3.6.

Proof: Separate `q≤1` from its negation; prove the goal under each of these mutually exclusive
hypotheses.
-/
theorem admissible_analytic {κ : ℝ} (hκ : 0<κ) (ha : D.Admissible hκ) :
    D.analytic.Admissible hκ := by
  -- Separate `q≤1` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  constructor
  · intro Y hY h₀ h₂
    apply (pointwise_criterion hκ.ne' _ _ _ _ _ _ _).mp
    rcases hY with ⟨⟨q,U,V,θ⟩,⟨hq,hN⟩,rfl⟩
    change 0<q at h₀
    change q<2 at h₂
    by_cases hl : q≤1
    · let t := cubeRoot q
      have ht : t∈Ioc (0:ℝ) 1 := ⟨cubeRoot_pos h₀,(cubeRoot_mem ⟨hq.1,hl⟩).2⟩
      have he : Side.left.q t=q := cubeRoot_cube hq.1
      have hp : D.cellPrice (Side.left.q t)=(D.cells Side.left).value t := by
        rw [he]
        simp only [cellPrice,cubicSides,ite_eq_left hl]
        rfl
      have h := D.normalized_residual_of_admissible hκ ha Side.left ht hN hp
      simpa only [he,PolynomialPotential.unnormalize,«2610.05164v2».StateRegion.Scales.stateLift,scales,analytic,«2610.05164v2».Calibration.Data.stateResidual] using h
    · let t := cubeRoot (2-q)
      have ht : t∈Ioc (0:ℝ) 1 :=
        ⟨cubeRoot_pos (by linarith),(cubeRoot_mem ⟨by linarith [hq.2],by linarith⟩).2⟩
      have he : Side.right.q t=q := by
        dsimp only [Side.q,t]
        rw [cubeRoot_cube (by linarith [hq.2])]
        ring
      have hp : D.cellPrice (Side.right.q t)=(D.cells Side.right).value t := by
        rw [he]
        simp only [cellPrice,cubicSides,ite_eq_right hl]
        rfl
      have h := D.normalized_residual_of_admissible hκ ha Side.right ht hN hp
      simpa only [he,PolynomialPotential.unnormalize,«2610.05164v2».StateRegion.Scales.stateLift,scales,analytic,«2610.05164v2».Calibration.Data.stateResidual] using h
  · intro Y hY hq
    exact le_of_eq (D.boundary_residual hκ hY hq).symm

/--
Theorem 3.6(i) for the literal rational certificate, with exactly its numerically checked
strict cell inequalities as the remaining premises.

The stated quantitative bound `D.analytic.targetValue≤∫ x,(sqrt (m.value x))^3`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2610.05164v2, Theorem 3.6.

Proof: Use the identities/estimates
`«2610.05164v2».DualCertificate.AnalyticData.relaxed_energy_ge_target`,
`«2610.05164v2».DualCertificate.Data.admissible_analytic` with the arguments shown in the
proof.
-/
theorem relaxed_energy_ge_value (m : «2610.05164v2».Filters.CompactDensity)
    (hm : m∈«2610.05164v2».Filters.CompactDensity.relaxed D.calibration.sigma)
    (ha : D.Admissible (κ := Real.pi^2/4) (div_pos (sq_pos_of_pos Real.pi_pos) (by norm_num))) :
    D.analytic.targetValue≤∫ x,(sqrt (m.value x))^3 :=
  D.analytic.relaxed_energy_ge_target m hm (D.admissible_analytic
    (div_pos (sq_pos_of_pos Real.pi_pos) (by norm_num)) ha)

end
end «2610.05164v2».DualCertificate.Data
