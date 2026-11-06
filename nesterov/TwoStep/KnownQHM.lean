import nesterov.TwoStep.AsymptoticsBasics
import nesterov.TwoStep.WallReal
import nesterov.Momentum.QHMRates
import nesterov.Momentum.RestQuadratic
import nesterov.Momentum.QueryRates

/-! Corollary B(iii): necessary accelerated QHM weights, including the exact
common-factor case, where the initialized method is gradient descent. -/
namespace nesterov.TwoStep.KnownTunings
noncomputable section
open Filter Set
open Asymptotics
open scoped Topology

theorem qhm_degenerate_product {β ν : ℝ} (hβ : β<1)
    (hdeg : β=Momentum.qhmExtrapolation β ν/(1+Momentum.qhmExtrapolation β ν))
    (hτ : 0≤Momentum.qhmExtrapolation β ν) : ν*β=0 := by
  have hden : 1+Momentum.qhmExtrapolation β ν≠0 := ne_of_gt (by linarith)
  have hh := (eq_div_iff hden).mp hdeg
  have ht : (1-β)*Momentum.qhmExtrapolation β ν=(1-ν)*β := by
    unfold Momentum.qhmExtrapolation
    field_simp [ne_of_gt (sub_pos.mpr hβ)]
  nlinarith

theorem qhm_degenerate_succ (g : ℝ→ℝ) (α β ν x₀ : ℝ) (hdeg : ν*β=0) (n : ℕ) :
    Momentum.qhmIterate g α β ν x₀ (n+1)=Momentum.qhmIterate g α β ν x₀ n-
      α*g (Momentum.qhmIterate g α β ν x₀ n) := by
  rcases mul_eq_zero.mp hdeg with rfl|rfl
  all_goals
    simp only [Momentum.qhmIterate,Momentum.qhmState,Momentum.qhmStep,smul_eq_mul]
    ring

theorem qhm_degenerate_quadratic (α β ν lam : ℝ) (hdeg : ν*β=0) (n : ℕ) :
    Momentum.qhmIterate (fun x : ℝ=>lam*x) α β ν 1 n=(1-α*lam)^n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [qhm_degenerate_succ _ α β ν 1 hdeg n,ih]
    ring

theorem qhm_degenerate_root_limsup (α β ν lam : ℝ) (hdeg : ν*β=0) :
    limsup (fun n : ℕ=>|Momentum.qhmIterate (fun x : ℝ=>lam*x) α β ν 1 n|^((n:ℝ)⁻¹)) atTop=
      |1-α*lam| := by
  have ht : Tendsto (fun n : ℕ=>|Momentum.qhmIterate (fun x : ℝ=>lam*x) α β ν 1 n|^((n:ℝ)⁻¹))
      atTop (𝓝 |1-α*lam|) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [qhm_degenerate_quadratic α β ν lam hdeg n,abs_pow,
      Real.pow_rpow_inv_natCast (abs_nonneg _) (by omega)]
  exact ht.limsup_eq

/-- The initialized QHM quadratic factors are the complete two-step root
maximum whenever the source common factor is absent. -/
theorem qhm_quadratic_rate_bound {μ L α β ν r : ℝ} (hμ : 0<μ) (hμL : μ<L)
    (hα : 0<α) (hβ₀ : 0≤β) (hβ₁ : β<1) (hν : ν≤1)
    (hne : β≠Momentum.qhmExtrapolation β ν/(1+Momentum.qhmExtrapolation β ν))
    (hbound : ∀ lam∈Icc μ L,
      limsup (fun n : ℕ=>|Momentum.qhmIterate (fun x : ℝ=>lam*x) α β ν 1 n|^((n:ℝ)⁻¹)) atTop≤r) :
    Quadratic.quadraticRate μ L β (Momentum.qhmExtrapolation β ν) (α*(1-β))≤r := by
  obtain ⟨hh,hτ⟩ := Momentum.qhm_parameters_admissible hα hβ₀ hβ₁ hν
  obtain ⟨lam,hlam,z,hz,hmax⟩ := (Quadratic.quadraticRate_isGreatest_general
    (β:=β) (τ:=Momentum.qhmExtrapolation β ν) (h:=α*(1-β)) hμL.le).1
  have hb := hbound lam hlam
  simp_rw [Momentum.qhmIterate_eq_queries (fun x : ℝ=>lam*x) α β ν hβ₁.ne 1] at hb
  rw [Momentum.quadratic_query_root_limsup hh (hμ.trans_le hlam.1) (by norm_num) hτ hne] at hb
  rw [hmax]
  exact ((Quadratic.scalarRadius_isGreatest β (Momentum.qhmExtrapolation β ν) (α*(1-β)) lam).2
    ⟨z,hz,rfl⟩).trans hb

variable {A : Type*} {l : Filter A} {ε α β ν : A→ℝ} {c : ℝ}

/-- Acceleration excludes the exact gradient-descent degeneracy eventually. -/
theorem qhm_eventually_nondegenerate (hc : 0<c) (he : Tendsto ε l (𝓝[>] (0:ℝ)))
    (hphysical : ∀ᶠ a in l,0<α a ∧ 0≤β a ∧ β a<1 ∧ ν a≤1)
    (hbound : ∀ᶠ a in l,∀ lam∈Icc (ε a^2) 1,
      limsup (fun n : ℕ=>|Momentum.qhmIterate (fun x : ℝ=>lam*x) (α a) (β a) (ν a) 1 n|^((n:ℝ)⁻¹)) atTop≤1-c*ε a) :
    ∀ᶠ a in l,β a≠Momentum.qhmExtrapolation (β a) (ν a)/(1+Momentum.qhmExtrapolation (β a) (ν a)) := by
  filter_upwards [hphysical,hbound,he.eventually self_mem_nhdsWithin,
    (he.mono_right nhdsWithin_le_nhds).eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1)),
    (he.mono_right nhdsWithin_le_nhds).eventually (eventually_lt_nhds (div_pos hc (by norm_num : (0:ℝ)<4)))]
    with a hp hb hea he1 hec hdeg
  have hepos : 0<ε a := hea
  have hμL : ε a^2<1 := by nlinarith
  have hτ := (Momentum.qhm_parameters_admissible hp.1 hp.2.1 hp.2.2.1 hp.2.2.2).2
  have hprod := qhm_degenerate_product hp.2.2.1 hdeg hτ
  have hsmall := hb (ε a^2) ⟨le_rfl,hμL.le⟩
  have hlarge := hb 1 ⟨hμL.le,le_rfl⟩
  rw [qhm_degenerate_root_limsup _ _ _ _ hprod] at hsmall hlarge
  have hm : 1-α a*ε a^2≤1-c*ε a := (le_abs_self _).trans hsmall
  have hL : α a-1≤1-c*ε a := by
    have hh := (neg_le_abs (1-α a*1)).trans hlarge
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hL (sq_nonneg (ε a))
  have hn := mul_nonneg (mul_pos hc hepos).le (sq_nonneg (ε a))
  nlinarith

/-- Corollary B(iii-a): the translated parameters obey the source quantitative
accelerated bounds, with no exclusion inserted into the original hypotheses. -/
theorem qhm_accelerated_parameter_bounds (hc : 0<c) (he : Tendsto ε l (𝓝[>] (0:ℝ)))
    (hphysical : ∀ᶠ a in l,0<α a ∧ 0≤β a ∧ β a<1 ∧ ν a≤1)
    (hbound : ∀ᶠ a in l,∀ lam∈Icc (ε a^2) 1,
      limsup (fun n : ℕ=>|Momentum.qhmIterate (fun x : ℝ=>lam*x) (α a) (β a) (ν a) 1 n|^((n:ℝ)⁻¹)) atTop≤1-c*ε a) :
    ∀ᶠ a in l,Momentum.qhmExtrapolation (β a) (ν a)<2/c^2 ∧
      1-β a<max 4 (8/c)*ε a := by
  filter_upwards [qhm_eventually_nondegenerate hc he hphysical hbound,hphysical,hbound,
    he.eventually self_mem_nhdsWithin,
    (he.mono_right nhdsWithin_le_nhds).eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))]
    with a hne hp hb he0 he1
  have hea : 0<ε a := he0
  obtain ⟨hh,hτ⟩ := Momentum.qhm_parameters_admissible hp.1 hp.2.1 hp.2.2.1 hp.2.2.2
  let q : Momentum.Tuning := {
    beta := β a
    tau := Momentum.qhmExtrapolation (β a) (ν a)
    stepSize := α a*(1-β a)
    beta_nonneg := hp.2.1
    beta_lt_one := hp.2.2.1
    tau_nonneg := hτ
    step_pos := hh }
  have hrate := qhm_quadratic_rate_bound (sq_pos_of_pos hea) (by nlinarith : ε a^2<1)
    hp.1 hp.2.1 hp.2.2.1 hp.2.2.2 hne hb
  have hstable : q.Stable (ε a^2) 1 := (Quadratic.stable_iff_quadraticRate_lt_one (by nlinarith : ε a^2≤1)).mpr
    (hrate.trans_lt (by nlinarith [mul_pos hc hea]))
  exact (accelerated_tuning_bounds q hea he1 hc hstable hrate).2.2

theorem qhm_accelerated_beta_tendsto (hc : 0<c) (he : Tendsto ε l (𝓝[>] (0:ℝ)))
    (hphysical : ∀ᶠ a in l,0<α a ∧ 0≤β a ∧ β a<1 ∧ ν a≤1)
    (hbound : ∀ᶠ a in l,∀ lam∈Icc (ε a^2) 1,
      limsup (fun n : ℕ=>|Momentum.qhmIterate (fun x : ℝ=>lam*x) (α a) (β a) (ν a) 1 n|^((n:ℝ)⁻¹)) atTop≤1-c*ε a) :
    Tendsto β l (𝓝 1) := by
  have hb := qhm_accelerated_parameter_bounds hc he hphysical hbound
  have hδ : Tendsto (fun a=>1-β a) l (𝓝 0) := by
    apply squeeze_zero' (hphysical.mono fun _ ha=>sub_nonneg.mpr ha.2.2.1.le)
      (hb.mono fun _ ha=>ha.2.le)
    simpa only [mul_zero] using (he.mono_right nhdsWithin_le_nhds).const_mul (max 4 (8/c))
  have ht := (tendsto_const_nhds (x:=(1:ℝ))).sub hδ
  simp only [sub_zero] at ht
  convert ht using 1
  funext a
  ring

/-- The QHM weight must approach one at the accelerated scale. -/
theorem qhm_weight_isBigO (hc : 0<c) (he : Tendsto ε l (𝓝[>] (0:ℝ)))
    (hphysical : ∀ᶠ a in l,0<α a ∧ 0≤β a ∧ β a<1 ∧ ν a≤1)
    (hbound : ∀ᶠ a in l,∀ lam∈Icc (ε a^2) 1,
      limsup (fun n : ℕ=>|Momentum.qhmIterate (fun x : ℝ=>lam*x) (α a) (β a) (ν a) 1 n|^((n:ℝ)⁻¹)) atTop≤1-c*ε a) :
    (fun a=>1-ν a) =O[l] ε := by
  let M : ℝ := max 4 (8/c)
  have hp := qhm_accelerated_parameter_bounds hc he hphysical hbound
  have hβ := qhm_accelerated_beta_tendsto hc he hphysical hbound
  apply IsBigO.of_bound (4*M/c^2)
  filter_upwards [hp,hphysical,he.eventually self_mem_nhdsWithin,
    hβ.eventually (eventually_gt_nhds (by norm_num : (1/2:ℝ)<1))] with a hpa hphys he0 hhalf
  have hep : 0<ε a := he0
  have hn : 0≤1-ν a := sub_nonneg.mpr hphys.2.2.2
  have hb : 0≤1-β a := sub_nonneg.mpr hphys.2.2.1.le
  have hτ := (Momentum.qhm_parameters_admissible hphys.1 hphys.2.1 hphys.2.2.1 hphys.2.2.2).2
  have hid : Momentum.qhmExtrapolation (β a) (ν a)*(1-β a)=(1-ν a)*β a := by
    unfold Momentum.qhmExtrapolation
    exact div_mul_cancel₀ _ (sub_pos.mpr hphys.2.2.1).ne'
  have hhalf' := mul_le_mul_of_nonneg_left hhalf.le hn
  rw [←hid] at hhalf'
  have hprod : Momentum.qhmExtrapolation (β a) (ν a)*(1-β a)≤(2/c^2)*(M*ε a) :=
    mul_le_mul hpa.1.le hpa.2.le hb (by positivity)
  have hweight : 1-ν a≤(4*M/c^2)*ε a := by
    calc
      1-ν a≤2*(Momentum.qhmExtrapolation (β a) (ν a)*(1-β a)) := by nlinarith
      _≤2*((2/c^2)*(M*ε a)) := mul_le_mul_of_nonneg_left hprod (by norm_num)
      _=_ := by ring
  simpa only [Real.norm_eq_abs,abs_of_nonneg hn,abs_of_pos hep] using hweight

theorem qhm_weight_tendsto_one (hc : 0<c) (he : Tendsto ε l (𝓝[>] (0:ℝ)))
    (hphysical : ∀ᶠ a in l,0<α a ∧ 0≤β a ∧ β a<1 ∧ ν a≤1)
    (hbound : ∀ᶠ a in l,∀ lam∈Icc (ε a^2) 1,
      limsup (fun n : ℕ=>|Momentum.qhmIterate (fun x : ℝ=>lam*x) (α a) (β a) (ν a) 1 n|^((n:ℝ)⁻¹)) atTop≤1-c*ε a) :
    Tendsto ν l (𝓝 1) := by
  have hd := (qhm_weight_isBigO hc he hphysical hbound).trans_tendsto
    (he.mono_right nhdsWithin_le_nhds)
  have ht := (tendsto_const_nhds (x:=(1:ℝ))).sub hd
  simp only [sub_zero] at ht
  convert ht using 1
  funext a
  ring

/-- A fixed QHM weight below one cannot accelerate on quadratics. -/
theorem qhm_fixed_weight_no_acceleration [NeBot l] {ν₀ : ℝ} (hν₀ : ν₀<1)
    (hν : ∀ᶠ a in l,ν a=ν₀) (hc : 0<c) (he : Tendsto ε l (𝓝[>] (0:ℝ)))
    (hphysical : ∀ᶠ a in l,0<α a ∧ 0≤β a ∧ β a<1 ∧ ν a≤1)
    (hbound : ∀ᶠ a in l,∀ lam∈Icc (ε a^2) 1,
      limsup (fun n : ℕ=>|Momentum.qhmIterate (fun x : ℝ=>lam*x) (α a) (β a) (ν a) 1 n|^((n:ℝ)⁻¹)) atTop≤1-c*ε a) :
    False := by
  have ht := (qhm_weight_tendsto_one hc he hphysical hbound).congr' hν
  have hh : ν₀=1 := tendsto_nhds_unique tendsto_const_nhds ht
  linarith

end
end nesterov.TwoStep.KnownTunings
