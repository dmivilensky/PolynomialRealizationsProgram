import nesterov.TwoStep.KnownQHM
import nesterov.TwoStep.AsymptoticsPhysical
import nesterov.TwoStep.KnownTuningRates
import nesterov.Realization.RestQuadratic

/-! The QHM conclusions for the literal supremum-before-limit initialized rate. -/
namespace nesterov.TwoStep.KnownTunings
noncomputable section
open Filter Set Asymptotics
open scoped Topology

theorem qhm_quadratic_root_limsup_le_rate {α β ν μ L lam : ℝ}
    (hα : 0<α) (hβ : β<1) (hμ : 0<μ) (hμL : μ<L) (hlam : lam∈Icc μ L) :
    limsup (fun n : ℕ=>|Momentum.qhmIterate (fun x : ℝ=>lam*x) α β ν 1 n|^((n:ℝ)⁻¹)) atTop≤
      Momentum.qhmRate α β ν μ L := by
  have hh : α*(1-β)≠0 := (mul_pos hα (sub_pos.mpr hβ)).ne'
  let i : Momentum.QHMInstance μ L := {
    Carrier := ℝ
    f := fun x : ℝ=>lam/2*‖x‖^2
    admissible := Momentum.real_quadratic_centered hμ hμL hlam
    initial := 1 }
  have hg : gradient (fun x : ℝ=>lam/2*‖x‖^2)=(fun x : ℝ=>lam*x) :=
    funext (Momentum.real_quadratic_gradient lam)
  have hpoint (n : ℕ) : |Momentum.qhmIterate (fun x : ℝ=>lam*x) α β ν 1 n|≤
      Momentum.qhmEnvelope α β ν μ L n := by
    have hmem : |Momentum.qhmIterate (fun x : ℝ=>lam*x) α β ν 1 n|∈Momentum.qhmRatios α β ν μ L n := by
      refine ⟨i,by norm_num,?_⟩
      change _=‖Momentum.qhmIterate (gradient (fun x : ℝ=>lam/2*‖x‖^2)) α β ν 1 n‖/‖(1:ℝ)‖
      rw [hg]
      simp only [Real.norm_eq_abs,abs_one,div_one]
    exact le_csSup (Momentum.qhmRatios_bddAbove α β ν μ L hβ.ne hh n) (Or.inr hmem)
  have hb : IsBoundedUnder (·≤·) atTop (fun n : ℕ=>Momentum.qhmEnvelope α β ν μ L n^((n:ℝ)⁻¹)) := by
    simpa only [Momentum.qhmEnvelope_eq_queryRestEnvelope α β ν μ L hβ.ne hh] using
      Momentum.query_roots_bounded β (Momentum.qhmExtrapolation β ν) (α*(1-β)) hh μ L
  exact limsup_le_limsup (Eventually.of_forall fun n=>
    Real.rpow_le_rpow (abs_nonneg _) (hpoint n) (by positivity))
    (isCoboundedUnder_le_of_le atTop (fun n=>Real.rpow_nonneg (abs_nonneg _) _)) hb

def qhmTranslatedTuning (α β ν : ℝ) : Momentum.Tuning :=
  physicalTuning β (Momentum.qhmExtrapolation β ν) (α*(1-β))

theorem qhmTranslatedTuning_parameters {α β ν : ℝ}
    (hp : 0<α ∧ 0≤β ∧ β<1 ∧ ν≤1) :
    (qhmTranslatedTuning α β ν).beta=β ∧
      (qhmTranslatedTuning α β ν).tau=Momentum.qhmExtrapolation β ν ∧
      (qhmTranslatedTuning α β ν).stepSize=α*(1-β) := by
  obtain ⟨hh,hτ⟩ := Momentum.qhm_parameters_admissible hp.1 hp.2.1 hp.2.2.1 hp.2.2.2
  exact physicalTuning_parameters ⟨hp.2.1,hp.2.2.1,hτ,hh⟩

variable {A : Type*} {l : Filter A} {ε α β ν : A→ℝ} {c : ℝ}

/-- The source QHM weight restriction for the actual initialized class rate. -/
theorem qhm_actual_weight_isBigO (hc : 0<c) (he : Tendsto ε l (𝓝[>] (0:ℝ)))
    (hp : ∀ᶠ a in l,0<α a ∧ 0≤β a ∧ β a<1 ∧ ν a≤1)
    (hrate : ∀ᶠ a in l,Momentum.qhmRate (α a) (β a) (ν a) (ε a^2) 1≤1-c*ε a) :
    (fun a=>1-ν a) =O[l] ε := by
  apply qhm_weight_isBigO hc he hp
  filter_upwards [hp,hrate,he.eventually self_mem_nhdsWithin,
    (he.mono_right nhdsWithin_le_nhds).eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))]
    with a hpa hra hea he1 lam hlam
  have hep : 0<ε a := hea
  exact (qhm_quadratic_root_limsup_le_rate hpa.1 hpa.2.2.1 (sq_pos_of_pos hep)
    (by nlinarith : ε a^2<1) hlam).trans hra

/-- Every accelerated actual QHM family obeys the literal half-step liminf rule. -/
theorem qhm_actual_half_le_liminf [l.IsCountablyGenerated] [NeBot l]
    (hc : 0<c) (he : Tendsto ε l (𝓝[>] (0:ℝ)))
    (hp : ∀ᶠ a in l,0<α a ∧ 0≤β a ∧ β a<1 ∧ ν a≤1)
    (hrate : ∀ᶠ a in l,Momentum.qhmRate (α a) (β a) (ν a) (ε a^2) 1≤1-c*ε a) :
    1/2≤liminf (fun a=>Momentum.qhmExtrapolation (β a) (ν a)) l := by
  have hquad : ∀ᶠ a in l,∀ lam∈Icc (ε a^2) 1,
      limsup (fun n : ℕ=>|Momentum.qhmIterate (fun x : ℝ=>lam*x) (α a) (β a) (ν a) 1 n|^((n:ℝ)⁻¹)) atTop≤1-c*ε a := by
    filter_upwards [hp,hrate,he.eventually self_mem_nhdsWithin,
      (he.mono_right nhdsWithin_le_nhds).eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))]
      with a hpa hra hea he1 lam hlam
    have hep : 0<ε a := hea
    exact (qhm_quadratic_root_limsup_le_rate hpa.1 hpa.2.2.1 (sq_pos_of_pos hep)
      (by nlinarith : ε a^2<1) hlam).trans hra
  let q : A→Momentum.Tuning := fun a=>qhmTranslatedTuning (α a) (β a) (ν a)
  have hparameters : ∀ᶠ a in l,(q a).beta=β a ∧
      (q a).tau=Momentum.qhmExtrapolation (β a) (ν a) ∧ (q a).stepSize=α a*(1-β a) :=
    hp.mono fun _ ha=>qhmTranslatedTuning_parameters ha
  have hqrate : ∀ᶠ a in l,Quadratic.quadraticRate (ε a^2) 1 (q a).beta (q a).tau (q a).stepSize≤1-c*ε a := by
    filter_upwards [hp,hparameters,hquad,qhm_eventually_nondegenerate hc he hp hquad,
      he.eventually self_mem_nhdsWithin,
      (he.mono_right nhdsWithin_le_nhds).eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))]
      with a hpa hqa hba hne hea he1
    have hep : 0<ε a := hea
    rw [hqa.1,hqa.2.1,hqa.2.2]
    exact qhm_quadratic_rate_bound (sq_pos_of_pos hep) (by nlinarith : ε a^2<1)
      hpa.1 hpa.2.1 hpa.2.2.1 hpa.2.2.2 hne hba
  have hstable : ∀ᶠ a in l,(q a).Stable (ε a^2) 1 := by
    filter_upwards [hqrate,he.eventually self_mem_nhdsWithin,
      (he.mono_right nhdsWithin_le_nhds).eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))]
      with a ha hea he1
    have hep : 0<ε a := hea
    apply (Quadratic.stable_iff_quadraticRate_lt_one (by nlinarith : ε a^2≤1)).mpr
    exact ha.trans_lt (by nlinarith [mul_pos hc hep])
  have hrest : ∀ᶠ a in l,Momentum.momentumRestRate (q a).beta (q a).tau (q a).stepSize
      (q a).step_pos.ne' (ε a^2) 1≤1 := by
    filter_upwards [hp,hparameters,hrate,he.eventually self_mem_nhdsWithin] with a hpa hqa hra hea
    have hep : 0<ε a := hea
    have hh : α a*(1-β a)≠0 := (mul_pos hpa.1 (sub_pos.mpr hpa.2.2.1)).ne'
    have hdict := Momentum.qhmRate_eq_queryRestRate (α a) (β a) (ν a) (ε a^2) 1 hpa.2.2.1.ne hh
    have hquery : Momentum.queryRestRate (q a).beta (q a).tau (q a).stepSize
        (q a).step_pos.ne' (ε a^2) 1≤1 := by
      have hraw : Momentum.queryRestRate (β a) (Momentum.qhmExtrapolation (β a) (ν a))
          (α a*(1-β a)) hh (ε a^2) 1≤1 := by rw [←hdict];nlinarith [mul_pos hc hep]
      simpa only [hqa.1,hqa.2.1,hqa.2.2] using hraw
    have hmax := Momentum.restRate_le_max_queryRestRate (β:=(q a).beta)
      (q a).step_pos.ne' (q a).tau_nonneg
      (μ:=ε a^2) (L:=1)
    exact hmax.trans (max_le hquery (Momentum.queryPole_mem (q a).tau_nonneg).2.le)
  have ht := half_le_liminf_tau_filter hc he hstable hqrate hrest
  have heq : (fun a=>(q a).tau)=ᶠ[l] (fun a=>Momentum.qhmExtrapolation (β a) (ν a)) :=
    hparameters.mono fun _ ha=>ha.2.1
  rwa [liminf_congr heq] at ht

end
end nesterov.TwoStep.KnownTunings
