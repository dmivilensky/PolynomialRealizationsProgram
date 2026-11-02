import krylov.ContinuumBV.PotentialAtoms

/-!
Article: main_krylov, apC:lem:fund, two physical directional identities.
Use: identify the actual Fréchet derivative of the potential on both physical
state directions. These coefficients connect the nonlinear BV chain theorem
to the drift measure dx and the genuine string mass measure dM.
Source: uniqueness of ordinary derivatives along affine state curves.
-/

namespace krylov.ContinuumBV
noncomputable section
open krylov.ContinuumControl

/-- Physical drift direction of the normalized string equation. -/
def driftDirection (z : PotentialState) : PotentialState := (z.2.1, 0, 0)

/-- Physical mass direction, valid for continuous mass and finite impulses. -/
def massDirection (z : PotentialState) : PotentialState := (0, z.1, z.1 ^ 2)

/-- Fréchet derivative on any linear combination of the two actual state
directions. The formula is obtained by differentiating the true potential. -/
theorem fderiv_statePotential_direction {γ dx dm : ℝ} {σ : ℝ → ℝ} {z : PotentialState}
    (hγ : γ ≠ 0) (hφ : 0 < z.1) (hp : 0 < z.2.1) (hK : 0 < z.2.2)
    (hσ : ContDiffAt ℝ 1 σ (z.1 * z.2.1 / z.2.2))
    (hgraph : FeedbackGraphAt γ σ (z.1 * z.2.1 / z.2.2)) :
    fderiv ℝ (statePotential γ σ) z
      (dx • driftDirection z + dm • massDirection z) =
        -(z.2.2 ^ (-γ)) / 2 *
          (z.2.1 / (z.1 * Real.sqrt (σ (z.1 * z.2.1 / z.2.2))) * dx +
            z.1 * Real.sqrt (σ (z.1 * z.2.1 / z.2.2)) / z.2.1 * dm) := by
  let φ : ℝ → ℝ := fun u => z.1 + u * (z.2.1 * dx)
  let p : ℝ → ℝ := fun u => z.2.1 + u * (z.1 * dm)
  let K : ℝ → ℝ := fun u => z.2.2 + u * (z.1 ^ 2 * dm)
  have hdφ : HasDerivAt φ (z.2.1 * dx) 0 := by
    simpa only [id_eq, one_mul] using
      (((hasDerivAt_id (0 : ℝ)).mul_const (z.2.1 * dx)).const_add z.1)
  have hdp : HasDerivAt p (z.1 * dm) 0 := by
    simpa only [id_eq, one_mul] using
      (((hasDerivAt_id (0 : ℝ)).mul_const (z.1 * dm)).const_add z.2.1)
  have hdK : HasDerivAt K (z.1 ^ 2 * dm) 0 := by
    simpa only [id_eq, one_mul] using
      (((hasDerivAt_id (0 : ℝ)).mul_const (z.1 ^ 2 * dm)).const_add z.2.2)
  have hφ₀ : φ 0 = z.1 := by simp [φ]
  have hp₀ : p 0 = z.2.1 := by simp [p]
  have hK₀ : K 0 = z.2.2 := by simp [K]
  have hd := hasDerivAt_stateValue (γ := γ) (x := 0) (dx := dx) (dm := dm)
    (σ := σ) (φ := φ) (p := p) (K := K) hγ
    (by simpa only [hφ₀] using hφ.ne') (by simpa only [hp₀] using hp.ne')
    (by simpa only [hK₀] using hK)
    (by simpa only [hφ₀, hp₀, hK₀] using hgraph.positive)
    (by simpa only [hφ₀, hp₀, hK₀] using hgraph.differentiable.hasDerivAt)
    (by simpa only [hφ₀, hp₀, hK₀] using hgraph.equation)
    (by simpa only [hp₀] using hdφ)
    (by simpa only [hφ₀] using hdp)
    (by simpa only [hφ₀] using hdK)
  have hcurve := hdφ.prodMk (hdp.prodMk hdK)
  have hcurve₀ : (φ 0, p 0, K 0) = z := by simp only [hφ₀, hp₀, hK₀, Prod.eta]
  have hF := (contDiffAt_statePotential hγ hφ.ne' hp.ne' hK.ne' hσ hgraph.positive).differentiableAt
    (by norm_num)
  have hFcurve : HasFDerivAt (statePotential γ σ) (fderiv ℝ (statePotential γ σ) z)
      (φ 0, p 0, K 0) := by rw [hcurve₀]; exact hF.hasFDerivAt
  have hchain := hFcurve.comp_hasDerivAt (0 : ℝ) hcurve
  have heq := hchain.unique hd
  simpa only [hφ₀, hp₀, hK₀, driftDirection, massDirection, Prod.smul_mk,
    Prod.mk_add_mk, smul_eq_mul, mul_zero, zero_mul, add_zero, zero_add, mul_comm]
    using heq

/-- Actual coefficient of physical drift dx in the BV chain identity. -/
theorem fderiv_statePotential_drift {γ : ℝ} {σ : ℝ → ℝ} {z : PotentialState}
    (hγ : γ ≠ 0) (hφ : 0 < z.1) (hp : 0 < z.2.1) (hK : 0 < z.2.2)
    (hσ : ContDiffAt ℝ 1 σ (z.1 * z.2.1 / z.2.2))
    (hgraph : FeedbackGraphAt γ σ (z.1 * z.2.1 / z.2.2)) :
    fderiv ℝ (statePotential γ σ) z (driftDirection z) =
      -(z.2.2 ^ (-γ)) / 2 * z.2.1 / (z.1 * Real.sqrt (σ (z.1 * z.2.1 / z.2.2))) := by
  have h := fderiv_statePotential_direction (dx := 1) (dm := 0) hγ hφ hp hK hσ hgraph
  simpa only [one_smul, zero_smul, add_zero, mul_one, mul_zero, mul_div_assoc] using h

/-- Actual coefficient of continuous mass dM in the BV chain identity. -/
theorem fderiv_statePotential_mass {γ : ℝ} {σ : ℝ → ℝ} {z : PotentialState}
    (hγ : γ ≠ 0) (hφ : 0 < z.1) (hp : 0 < z.2.1) (hK : 0 < z.2.2)
    (hσ : ContDiffAt ℝ 1 σ (z.1 * z.2.1 / z.2.2))
    (hgraph : FeedbackGraphAt γ σ (z.1 * z.2.1 / z.2.2)) :
    fderiv ℝ (statePotential γ σ) z (massDirection z) =
      -(z.2.2 ^ (-γ)) / 2 * (z.1 * Real.sqrt (σ (z.1 * z.2.1 / z.2.2)) / z.2.1) := by
  simpa only [zero_smul, one_smul, zero_add, mul_zero, zero_add, mul_one] using
    fderiv_statePotential_direction (dx := 0) (dm := 1) hγ hφ hp hK hσ hgraph

end
end krylov.ContinuumBV
