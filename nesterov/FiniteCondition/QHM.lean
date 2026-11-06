import nesterov.FiniteCondition.Counterexample
import nesterov.Momentum.QHMRates
import nesterov.Momentum.QueryRates

/-! Article: Corollary `cor:QHM`, with the actual accumulator initialized at zero. -/
namespace nesterov.FiniteCondition
noncomputable section
open nesterov.Momentum

def AllStableQHMConverge (β ν : ℝ) : Prop :=
  ∀ α μ L : ℝ,0<α → 0<μ → μ<L →
    Quadratic.Stable μ L β (qhmExtrapolation β ν) (α*(1-β)) →
      qhmRate α β ν μ L<1

theorem qhm_tonguefree_iff {β ν : ℝ} (hβ : 0≤β) (hβ1 : β<1)
    (_hν0 : 0≤ν) (hν1 : ν≤1) :
    AllStableQHMConverge β ν ↔ tauThree β≤qhmExtrapolation β ν := by
  have hτ : 0≤qhmExtrapolation β ν :=
    div_nonneg (mul_nonneg (sub_nonneg.mpr hν1) hβ) (sub_pos.mpr hβ1).le
  constructor
  · intro hall
    by_contra hh
    have hlt := lt_of_not_ge hh
    obtain ⟨q,μ,L,hqb,hqt,hqh,hμ,hL,hs,_,hr⟩ := three_tongue_witness hβ hβ1 hτ hlt
    let α : ℝ := (1-β)⁻¹
    have hα : 0<α := inv_pos.mpr (sub_pos.mpr hβ1)
    have he : α*(1-β)=1 := inv_mul_cancel₀ (sub_pos.mpr hβ1).ne'
    have hs1 : Quadratic.Stable μ L β (qhmExtrapolation β ν) 1 := by
      simpa only [Tuning.Stable,hqb,hqt,hqh] using hs
    have hhq := hall α μ L hα hμ hL (by rw [he];exact hs1)
    have hstep : α*(1-β)≠0 := by rw [he];norm_num
    rw [qhmRate_eq_queryRestRate α β ν μ L hβ1.ne hstep] at hhq
    have hrq : 1<momentumRestRate β (qhmExtrapolation β ν) (α*(1-β)) hstep μ L := by
      simpa only [hqb,hqt,hqh,he] using hr
    have hp : queryPole (qhmExtrapolation β ν)<
        momentumRestRate β (qhmExtrapolation β ν) (α*(1-β)) hstep μ L :=
      (queryPole_mem hτ).2.trans hrq
    have heq := queryRestRate_eq_restRate_of_pole_lt_rest hstep hτ hp
    rw [heq] at hhq
    linarith
  · intro ht α μ L hα hμ hL hs
    have hh := (qhm_parameters_admissible hα hβ hβ1 hν1).1
    let q : Tuning := ⟨β,qhmExtrapolation β ν,α*(1-β),hβ,hβ1,hτ,hh⟩
    have hr := tonguefree_rate q hμ hL hs ht
    have hb := (queryRestRate_le_restRate (β:=β) (μ:=μ) (L:=L) hh.ne' hτ).trans
      (restRate_le_momentumRate (β:=β) hh.ne' hμ hL)
    rw [qhmRate_eq_queryRestRate α β ν μ L hβ1.ne hh.ne']
    exact hb.trans_lt hr

end
end nesterov.FiniteCondition
