import nesterov.Oracle.ResistingOracleHard
import nesterov.Oracle.Envelope
import nesterov.Oracle.MomentumPolicy

/-! The dimension-uniform deterministic first-order lower bound, proved
from actual smooth strongly convex hard functions. TMM attains this oracle
root factor; the literal condition-number acceleration coefficient is ≤1. -/
namespace nesterov.Oracle
noncomputable section
open Filter
open scoped Topology

theorem first_order_lower_square (A : Algorithm) {s : ℝ} (hs : 0<s) (hs1 : s<1) :
    ENNReal.ofReal (1-s)≤literalRate A (s^2) := by
  have hρ : 0<1-s := sub_pos.mpr hs1
  have hC : 0<Real.sqrt (1-(1-s)^2) := by
    apply Real.sqrt_pos.mpr
    nlinarith
  apply literalRate_ge_of_hard_instances A hC hρ
  intro N
  obtain ⟨f,z,hf,hz,hn,hl⟩ := Geometric.finite_hard_instance N hs hs1 (A N (2*N+2))
  refine ⟨2*N+2,f,z,⟨hf,hz,hn⟩,?_⟩
  exact hl

theorem first_order_literal_rate_lower (A : Algorithm) {q : ℝ} (hq : 0<q) (hq1 : q<1) :
    ENNReal.ofReal (1-Real.sqrt q)≤literalRate A q := by
  have hs : 0<Real.sqrt q := Real.sqrt_pos.mpr hq
  have hs1 : Real.sqrt q<1 := by
    have h := Real.sqrt_lt_sqrt hq.le hq1
    simpa only [Real.sqrt_one] using h
  have h := first_order_lower_square A hs hs1
  simpa only [Real.sq_sqrt hq.le] using h

theorem first_order_kappa_lower (A : Algorithm) {κ : ℝ} (hκ : 1<κ) :
    ENNReal.ofReal (1-1/Real.sqrt κ)≤literalRate A (1/κ) := by
  have hκp : 0<κ := by linarith
  have h := first_order_literal_rate_lower A (one_div_pos.mpr hκp) ((div_lt_one hκp).mpr hκ)
  simpa only [Real.sqrt_div (by norm_num : (0:ℝ)≤1),Real.sqrt_one] using h

theorem tmm_oracle_rate (κ : ℝ) (hκ : 1<κ) :
    literalRate (momentumAlgorithm (Robust.tmmDesign κ hκ).beta (Robust.tmmDesign κ hκ).tau
      (Robust.tmmDesign κ hκ).step) (1/κ)=ENNReal.ofReal (1-1/Real.sqrt κ) := by
  apply le_antisymm
  · have h := momentum_literalRate_le (Robust.tmmDesign κ hκ).tuning
      (Robust.tmmDesign κ hκ).mu_pos (Robust.tmmDesign κ hκ).mu_lt_one
    change literalRate (momentumAlgorithm (Robust.tmmDesign κ hκ).beta (Robust.tmmDesign κ hκ).tau
      (Robust.tmmDesign κ hκ).step) (1/κ)≤ENNReal.ofReal
      (Momentum.momentumRate (Robust.tmmDesign κ hκ).beta (Robust.tmmDesign κ hκ).tau
        (Robust.tmmDesign κ hκ).step (Robust.tmmDesign κ hκ).step_pos.ne' (1/κ) 1) at h
    rwa [(Robust.tmm_exact_rates κ hκ).1] at h
  · exact first_order_kappa_lower _ hκ

theorem tmm_oracle_optimal (κ : ℝ) (hκ : 1<κ) (A : Algorithm) :
    literalRate (momentumAlgorithm (Robust.tmmDesign κ hκ).beta (Robust.tmmDesign κ hκ).tau
      (Robust.tmmDesign κ hκ).step) (1/κ)≤literalRate A (1/κ) := by
  rw [tmm_oracle_rate κ hκ]
  exact first_order_kappa_lower A hκ

/-- +∞ root factors have acceleration coefficient −∞. This avoids
discarding arbitrary policies through totalized real suprema. -/
def kappaCoefficient (A : Algorithm) (κ : ℝ) : EReal :=
  if literalRate A (1/κ)=⊤ then ⊥ else
    ((Real.sqrt κ*(1-(literalRate A (1/κ)).toReal):ℝ):EReal)

theorem first_order_kappa_coefficient_le (A : Algorithm) {κ : ℝ} (hκ : 1<κ) :
    kappaCoefficient A κ≤(1:EReal) := by
  unfold kappaCoefficient
  split_ifs with ht
  · exact bot_le
  · apply EReal.coe_le_coe_iff.mpr
    have h := ENNReal.toReal_mono ht (first_order_kappa_lower A hκ)
    have hρ : 0≤1-1/Real.sqrt κ := (Robust.tmmDesign κ hκ).rho_pos.le
    rw [ENNReal.toReal_ofReal hρ] at h
    have hs : 0<Real.sqrt κ := Real.sqrt_pos.mpr (by linarith)
    have hh := mul_le_mul_of_nonneg_left (show 1-(literalRate A (1/κ)).toReal≤1/Real.sqrt κ by linarith) hs.le
    simpa only [mul_one_div_cancel hs.ne'] using hh

theorem all_family_kappa_limsup_le_one {B : Type*} {l : Filter B}
    (A : B→Algorithm) {κ : B→ℝ} (hκ : ∀ᶠ b in l,1<κ b) :
    limsup (fun b=>kappaCoefficient (A b) (κ b)) l≤(1:EReal) := by
  apply Filter.limsup_le_of_le (by isBoundedDefault)
  filter_upwards [hκ] with b hb
  exact first_order_kappa_coefficient_le (A b) hb

theorem tmm_kappa_coefficient (κ : ℝ) (hκ : 1<κ) :
    kappaCoefficient (momentumAlgorithm (Robust.tmmDesign κ hκ).beta (Robust.tmmDesign κ hκ).tau
      (Robust.tmmDesign κ hκ).step) κ=(1:EReal) := by
  unfold kappaCoefficient
  rw [tmm_oracle_rate κ hκ]
  simp only [ENNReal.ofReal_ne_top,ite_false]
  have hρ : 0≤1-1/Real.sqrt κ := (Robust.tmmDesign κ hκ).rho_pos.le
  rw [ENNReal.toReal_ofReal hρ,sub_sub_cancel,
    mul_one_div_cancel (Real.sqrt_pos.mpr (by linarith : (0:ℝ)<κ)).ne']
  norm_cast

end
end nesterov.Oracle
