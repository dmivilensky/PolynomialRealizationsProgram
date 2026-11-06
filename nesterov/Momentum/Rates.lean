import nesterov.Momentum.Stationary
import nesterov.Rates.Rest
import nesterov.Quadratic.Rate

/-!
Article: Definition `def:rate` and Lemma `lem:envelope`.
Use: identify the general finite-memory uniform rate with the actual two-step
family and its scalar quadratic characteristic modes.
-/
namespace nesterov.Momentum
noncomputable section
open scoped BigOperators Topology

/-- The actual uniform nonlinear distance factor of the momentum tuning. -/
def momentumRate (β τ h : ℝ) (hh : h≠0) (μ L : ℝ) : ℝ :=
  Rates.rate (method β τ h hh) μ L

/-- The finite-dimensional distance factor with the prescribed rest initialization. -/
def momentumRestRate (β τ h : ℝ) (hh : h≠0) (μ L : ℝ) : ℝ :=
  Rates.restRate (method β τ h hh) μ L

/-- The from-rest source factor is bounded by the all-state uniform factor. -/
theorem restRate_le_momentumRate {μ L β τ h : ℝ} (hh : h≠0)
    (hμ : 0<μ) (hμL : μ<L) :
    momentumRestRate β τ h hh μ L≤momentumRate β τ h hh μ L :=
  Rates.restRate_le_rate (method β τ h hh) hμ hμL

/-- The source endpoint characteristic and the latent stationary polynomial
agree up to the fixed nonzero factor −1/h. -/
theorem method_characteristic (β τ h : ℝ) (hh : h≠0) (lam : ℝ) (z : ℂ) :
    (method β τ h hh).characteristic lam z = -(1/(h:ℂ))*Quadratic.characteristic β τ h lam z := by
  change ((∑ j : Fin 3, (![-β/h,(1+β)/h,-1/h] j : ℂ)*z^j.val) -
    (lam:ℂ)*(∑ j : Fin 2, (![-τ,1+τ] j : ℂ)*z^j.val)) = _
  simp [Fin.sum_univ_three,Fin.sum_univ_two,Quadratic.characteristic,Quadratic.queryPolynomial]
  field_simp [hh]
  ring

theorem method_characteristic_zero_iff (β τ h : ℝ) (hh : h≠0) (lam : ℝ) (z : ℂ) :
    (method β τ h hh).characteristic lam z=0 ↔ Quadratic.characteristic β τ h lam z=0 := by
  rw [method_characteristic]
  exact mul_eq_zero.trans (or_iff_right (neg_ne_zero.mpr (one_div_ne_zero (Complex.ofReal_ne_zero.mpr hh))))

/-- Every endpoint or interior curvature root bounds the true nonlinear factor. -/
theorem root_norm_le_momentumRate {μ L β τ h lam : ℝ} (hh : h≠0)
    (hμ : 0<μ) (hμL : μ<L) (hlam : lam∈Set.Icc μ L) {z : ℂ}
    (hz : Quadratic.characteristic β τ h lam z=0) :
    ‖z‖≤momentumRate β τ h hh μ L :=
  Rates.characteristicRoot_norm_le_rate (method β τ h hh) hμ hμL hlam
    ((method_characteristic_zero_iff β τ h hh lam z).mpr hz)

/-- The literal maximum over scalar quadratic roots is a nonlinear lower bound. -/
theorem quadraticRate_le_momentumRate {μ L β τ h : ℝ} (hh : h≠0)
    (hμ : 0<μ) (hμL : μ<L) :
    Quadratic.quadraticRate μ L β τ h≤momentumRate β τ h hh μ L := by
  apply csSup_le (Quadratic.rootNorms_nonempty hμL.le β τ h)
  rintro r ⟨lam,hlam,z,hz,rfl⟩
  exact root_norm_le_momentumRate hh hμ hμL hlam hz

end
end nesterov.Momentum
