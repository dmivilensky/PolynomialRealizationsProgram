import nesterov.Oracle.Model
import nesterov.Rates.RootBounds
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! Literal worst-case oracle errors, with the supremum taken before the
horizon root limsup. Extended nonnegative reals retain unbounded policies. -/
namespace nesterov.Oracle
noncomputable section
open Set Filter
open scoped Topology

def error (A : Algorithm) (q : ℝ) (N : ℕ) : ENNReal :=
  ⨆ (d : ℕ) (f : Space d→ℝ) (xstar : Space d) (_h : Instance q d f xstar),
    ENNReal.ofReal ‖(A N d).result (firstOrderOracle f) N-xstar‖

def literalRate (A : Algorithm) (q : ℝ) : ENNReal :=
  limsup (fun N : ℕ=>error A q N^((N:ℝ)⁻¹)) atTop

theorem instance_error_le (A : Algorithm) {q : ℝ} {N d : ℕ}
    {f : Space d→ℝ} {xstar : Space d} (hf : Instance q d f xstar) :
    ENNReal.ofReal ‖(A N d).result (firstOrderOracle f) N-xstar‖≤error A q N :=
  le_iSup_of_le d (le_iSup_of_le f (le_iSup_of_le xstar (le_iSup_of_le hf le_rfl)))

theorem error_le_of_uniform (A : Algorithm) {q r C : ℝ}
    (h : ∀ N d : ℕ,∀ (f : Space d→ℝ) (xstar : Space d),Instance q d f xstar →
      ‖(A N d).result (firstOrderOracle f) N-xstar‖≤C*r^N) (N : ℕ) :
    error A q N≤ENNReal.ofReal (C*r^N) := by
  apply iSup_le
  intro d
  apply iSup_le
  intro f
  apply iSup_le
  intro xstar
  apply iSup_le
  intro hf
  exact ENNReal.ofReal_le_ofReal (h N d f xstar hf)

theorem geometric_root_tendsto {C ρ : ℝ} (hC : 0<C) (hρ : 0<ρ) :
    Tendsto (fun N : ℕ=>(ENNReal.ofReal (C*ρ^N))^((N:ℝ)⁻¹)) atTop (𝓝 (ENNReal.ofReal ρ)) := by
  have ht : Tendsto (fun N : ℕ=>C^((N:ℝ)⁻¹)*ρ) atTop (𝓝 ρ) := by
    simpa only [one_mul] using (Rates.tendsto_const_root hC).mul_const ρ
  apply (ENNReal.tendsto_ofReal ht).congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  rw [ENNReal.ofReal_rpow_of_nonneg (mul_pos hC (pow_pos hρ N)).le (by positivity)]
  rw [Real.mul_rpow hC.le (pow_pos hρ N).le,Real.pow_rpow_inv_natCast hρ.le (by omega)]

theorem literalRate_ge_of_error_lower (A : Algorithm) {q C ρ : ℝ}
    (hC : 0<C) (hρ : 0<ρ) (hbound : ∀ N : ℕ,ENNReal.ofReal (C*ρ^N)≤error A q N) :
    ENNReal.ofReal ρ≤literalRate A q := by
  have ht := geometric_root_tendsto hC hρ
  have hp : ∀ᶠ N : ℕ in atTop,
      (ENNReal.ofReal (C*ρ^N))^((N:ℝ)⁻¹)≤error A q N^((N:ℝ)⁻¹) :=
    Eventually.of_forall (fun N=>ENNReal.rpow_le_rpow (hbound N) (by positivity))
  have hh := limsup_le_limsup hp (by isBoundedDefault) (by isBoundedDefault)
  rw [ht.limsup_eq] at hh
  exact hh

theorem literalRate_ge_of_hard_instances (A : Algorithm) {q C ρ : ℝ}
    (hC : 0<C) (hρ : 0<ρ)
    (h : ∀ N : ℕ,∃ (d : ℕ) (f : Space d→ℝ) (xstar : Space d),
      Instance q d f xstar ∧ C*ρ^N≤‖(A N d).result (firstOrderOracle f) N-xstar‖) :
    ENNReal.ofReal ρ≤literalRate A q := by
  apply literalRate_ge_of_error_lower A hC hρ
  intro N
  obtain ⟨d,f,xstar,hf,hl⟩ := h N
  exact (ENNReal.ofReal_le_ofReal hl).trans (instance_error_le A hf)

theorem literalRate_le_of_uniform (A : Algorithm) {q C r : ℝ}
    (hC : 0<C) (hr : 0<r)
    (h : ∀ N d : ℕ,∀ (f : Space d→ℝ) (xstar : Space d),Instance q d f xstar →
      ‖(A N d).result (firstOrderOracle f) N-xstar‖≤C*r^N) :
    literalRate A q≤ENNReal.ofReal r := by
  have ht := geometric_root_tendsto hC hr
  have hp : ∀ᶠ N : ℕ in atTop,error A q N^((N:ℝ)⁻¹)≤
      (ENNReal.ofReal (C*r^N))^((N:ℝ)⁻¹) :=
    Eventually.of_forall (fun N=>ENNReal.rpow_le_rpow (error_le_of_uniform A h N) (by positivity))
  have hh := limsup_le_limsup hp (by isBoundedDefault) (by isBoundedDefault)
  rw [ht.limsup_eq] at hh
  exact hh

end
end nesterov.Oracle
