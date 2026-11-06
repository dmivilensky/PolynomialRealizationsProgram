import nesterov.IQC.KYP.Potential
import polyak.Functions.Normalization

/-! The exact function-value term of the source lag-one Lyapunov form. -/
namespace nesterov.IQC.KYP
noncomputable section
open scoped BigOperators
variable {a : Spectral.SymbolPair} {t : ℝ}

theorem sourcePotential_single_lag (cert : Duality.StrictCertificate a t)
    (hlags : cert.lags={1}) (h : ℕ→ℝ) (k : ℕ) :
    sourcePotential cert h k=2*Real.exp (-t)*(cert.α 1-cert.β 1)*h k := by
  rw [sourcePotential_eq_finite_sum]
  simp only [hlags,Finset.sum_singleton,Nat.cast_one,one_mul,
    Finset.sum_range_one,Nat.cast_zero,zero_add,Nat.add_zero,mul_one]
  have he : Real.exp t*Real.exp (-2*t)=Real.exp (-t) := by
    rw [←Real.exp_add]
    congr 1
    ring
  linear_combination 2*(cert.α 1-cert.β 1)*h k*he

/-- The lag-one certificate normalized as in Proposition lyap has Ψ=2ψ. -/
theorem sourcePotential_lagOne (cert : Duality.StrictCertificate a t)
    (hlags : cert.lags={1}) (hα : cert.α 1=Real.exp t) (hβ : cert.β 1=0)
    (h : ℕ→ℝ) (k : ℕ) : sourcePotential cert h k=2*h k := by
  rw [sourcePotential_single_lag cert hlags,hα,hβ,sub_zero]
  have he : Real.exp (-t)*Real.exp t=1:=by rw [←Real.exp_add]; simp
  linear_combination 2*h k*he

/-- The displayed original-objective correction in Proposition lyap. -/
theorem normalized_value_correction {E : Type*} [NormedAddCommGroup E]
    (μ L : ℝ) (f : E→ℝ) (x : E) :
    -2*polyak.normalizeFunction μ L f x=
      4/(L-μ)*(f x-(L+μ)/4*‖x‖^2) := by
  unfold polyak.normalizeFunction
  ring

end
end nesterov.IQC.KYP
