import nesterov.Momentum.Rates
import nesterov.Rates.QuadraticMaximum

/-!
Article: §2 and §4, the quadratic rate in the general and two-step dictionaries.
Use: both literal root-max definitions agree; the characteristic sign and step
factor introduce no extra modes or changes of normalization.
-/
namespace nesterov.Momentum
noncomputable section

theorem quadraticRootNorms_method (β τ h μ L : ℝ) (hh : h≠0) :
    Rates.quadraticRootNorms (method β τ h hh) μ L=Quadratic.rootNorms μ L β τ h := by
  ext x
  constructor
  · rintro ⟨lam,hlam,z,hz,hx⟩
    exact ⟨lam,hlam,z,(method_characteristic_zero_iff β τ h hh lam z).mp hz,hx⟩
  · rintro ⟨lam,hlam,z,hz,hx⟩
    exact ⟨lam,hlam,z,(method_characteristic_zero_iff β τ h hh lam z).mpr hz,hx⟩

theorem quadraticRate_method (β τ h μ L : ℝ) (hh : h≠0) :
    Rates.quadraticRate (method β τ h hh) μ L=Quadratic.quadraticRate μ L β τ h := by
  unfold Rates.quadraticRate Quadratic.quadraticRate
  rw [quadraticRootNorms_method]

end
end nesterov.Momentum
