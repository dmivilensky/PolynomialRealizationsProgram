import nesterov.Realization.StartupCoordinates
import nesterov.Momentum.Rates
import nesterov.Momentum.PolyakBridge
import nesterov.Closure.Equality
import nesterov.Attainment.Optimal

/-! From one fixed physical startup witness to the literal from-rest rate. -/
noncomputable section
open Filter Set
open scoped Topology BigOperators NNReal

namespace nesterov.Momentum
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- A genuine objective and a nonzero start enter the source supremum at every
horizon, with its actual prescribed zero-momentum execution. -/
theorem iterate_ratio_mem_restRatios {μ L β τ h : ℝ} (hh : h≠0)
    {f : E→ℝ} (hf : polyak.CenteredSmoothStronglyConvex μ L f)
    {x₀ : E} (hx₀ : x₀≠0) (n : ℕ) :
    ‖iterate (gradient f) β τ h x₀ n‖/‖x₀‖∈Rates.restRatios (method β τ h hh) μ L n := by
  let r : Rates.HilbertRun (method β τ h hh) μ L :=
    ⟨E,f,hf,history (gradient f) β τ h x₀ x₀,history_isTrajectory _ β τ h hh _ _⟩
  have hr : r.FromRest := by
    intro j
    fin_cases j <;> rfl
  refine ⟨r,inferInstance,hr,hx₀,?_⟩
  change _=‖history (gradient f) β τ h x₀ x₀ (n+2-1)‖/‖x₀‖
  rw [show n+2-1=n+1 by omega]
  rfl

theorem iterate_ratio_le_restEnvelope {μ L β τ h : ℝ} (hh : h≠0)
    {f : E→ℝ} (hf : polyak.CenteredSmoothStronglyConvex μ L f)
    {x₀ : E} (hx₀ : x₀≠0) (n : ℕ) :
    ‖iterate (gradient f) β τ h x₀ n‖/‖x₀‖≤Rates.restEnvelope (method β τ h hh) μ L n :=
  le_csSup (Rates.restRatios_bddAbove _ _ _ _)
    (mem_insert_of_mem _ (iterate_ratio_mem_restRatios hh hf hx₀ n))

theorem iterate_roots_bounded {μ L β τ h : ℝ} (hh : h≠0)
    {f : E→ℝ} (hf : polyak.CenteredSmoothStronglyConvex μ L f)
    {x₀ : E} (hx₀ : x₀≠0) :
    IsBoundedUnder (·≤·) atTop
      (fun n : ℕ=>‖iterate (gradient f) β τ h x₀ n‖^((n:ℝ)⁻¹)) := by
  let M := method β τ h hh
  have hnorm : 0<‖x₀‖ := norm_pos_iff.mpr hx₀
  have hmem : 0<Real.sqrt M.memory := Real.sqrt_pos.mpr (Nat.cast_pos.mpr M.memory_pos)
  apply Rates.roots_bounded_of_mul_pow (fun n=>norm_nonneg _)
    (mul_pos hnorm hmem) (M.stepBound_pos L)
  intro n
  have hratio := iterate_ratio_le_restEnvelope (β:=β) (τ:=τ) hh hf hx₀ n
  have hstep := (Rates.restEnvelope_le_envelope M μ L n).trans
    (mul_le_mul_of_nonneg_left (Rates.envelope_le M μ L n) hmem.le)
  have hh' := (div_le_iff₀ hnorm).mp (hratio.trans hstep)
  nlinarith

/-- The literal root limsup of one fixed physical execution is bounded by the
source from-rest supremum, whose boundedness has already been established. -/
theorem iterate_root_limsup_le_restRate {μ L β τ h : ℝ} (hh : h≠0)
    {f : E→ℝ} (hf : polyak.CenteredSmoothStronglyConvex μ L f)
    {x₀ : E} (hx₀ : x₀≠0) :
    limsup (fun n : ℕ=>‖iterate (gradient f) β τ h x₀ n‖^((n:ℝ)⁻¹)) atTop≤
      momentumRestRate β τ h hh μ L := by
  have hpoint (n : ℕ) : ‖iterate (gradient f) β τ h x₀ n‖≤
      ‖x₀‖*Rates.restEnvelope (method β τ h hh) μ L n := by
    have hh' := (div_le_iff₀ (norm_pos_iff.mpr hx₀)).mp (iterate_ratio_le_restEnvelope (β:=β) (τ:=τ) hh hf hx₀ n)
    nlinarith
  apply le_of_forall_gt_imp_ge_of_dense
  intro R hR
  have hRp : 0<R := (Rates.restRate_nonneg (method β τ h hh) μ L).trans_lt hR
  obtain ⟨B,hB,hbound⟩ := Rates.exists_mul_pow_of_limsup_root_lt
    (Rates.restEnvelope_nonneg (method β τ h hh) μ L)
    (Rates.rest_roots_bounded (method β τ h hh) μ L) hRp hR
  apply Rates.limsup_root_le_of_mul_pow (fun n=>norm_nonneg _)
    (mul_pos (norm_pos_iff.mpr hx₀) hB) hRp
  intro n
  calc
    _ ≤ ‖x₀‖*Rates.restEnvelope (method β τ h hh) μ L n := hpoint n
    _ ≤ ‖x₀‖*(B*R^n) := mul_le_mul_of_nonneg_left (hbound n) (norm_nonneg _)
    _ = _ := by ring
end nesterov.Momentum

namespace nesterov.Rates
/-- A positive fixed exponential lower bound survives the literal root limsup. -/
theorem exp_le_root_limsup_of_lower_bound {f : ℕ→ℝ} {C t : ℝ}
    (hC : 0<C) (hbound : ∀ n : ℕ,C*Real.exp ((n:ℝ)*t)≤f n)
    (hb : IsBoundedUnder (·≤·) atTop (fun n : ℕ=>f n^((n:ℝ)⁻¹))) :
    Real.exp t≤limsup (fun n : ℕ=>f n^((n:ℝ)⁻¹)) atTop := by
  have hlim : Tendsto (fun n : ℕ=>C^((n:ℝ)⁻¹)*Real.exp t) atTop (𝓝 (Real.exp t)) := by
    simpa using (tendsto_const_root hC).mul_const (Real.exp t)
  have he : ∀ᶠ n : ℕ in atTop,C^((n:ℝ)⁻¹)*Real.exp t≤f n^((n:ℝ)⁻¹) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hexp : (Real.exp ((n:ℝ)*t))^((n:ℝ)⁻¹)=Real.exp t := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
      congr 1
      field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)]
    calc
      _ = (C*Real.exp ((n:ℝ)*t))^((n:ℝ)⁻¹) := by
        rw [Real.mul_rpow hC.le (Real.exp_pos _).le,hexp]
      _ ≤ _ := Real.rpow_le_rpow (mul_nonneg hC.le (Real.exp_pos _).le) (hbound n) (by positivity)
  have hh := limsup_le_limsup he
    (isCoboundedUnder_le_of_le atTop (fun n=>mul_nonneg
      (Real.rpow_nonneg hC.le _) (Real.exp_pos _).le)) hb
  rwa [hlim.limsup_eq] at hh
end nesterov.Rates

namespace nesterov.Realization
open Spectral
variable {J : Type*} [Fintype J]

/-- Every finite feasible wave with the startup reserve gives a lower bound
on the actual finite-dimensional from-rest rate. -/
theorem exp_le_momentumRestRate_of_feasible (q : Momentum.Tuning) {μ L t C : ℝ}
    (hμ : 0<μ) (hμL : μ<L) (hs : q.Stable μ L)
    (w : J→ℝ≥0) (c : J→Frequency) (hw : ∑ j,w j=1)
    (hfeas : Feasible ((Momentum.method q.beta q.tau q.stepSize q.step_pos.ne').symbolPair μ L t)
      t (finiteSpectrum w c hw) C)
    (hstrict : 0<t → |C|<meanG (finiteSpectrum w c hw)
      ((Momentum.method q.beta q.tau q.stepSize q.step_pos.ne').symbolPair μ L t)) :
    Real.exp t≤Momentum.momentumRestRate q.beta q.tau q.stepSize q.step_pos.ne' μ L := by
  obtain ⟨lam,_,Y,f,_,hf,_,hx,_,c₀,hc₀,hbound⟩ :=
    exists_real_startup q hμ hμL hs w c hw hfeas hstrict
  apply Rates.exp_le_root_limsup_of_lower_bound hc₀ _
    (Rates.rest_roots_bounded _ _ _)
  intro n
  have hb := (le_div_iff₀ (norm_pos_iff.mpr hx)).mpr (hbound n)
  exact hb.trans (Momentum.iterate_ratio_le_restEnvelope q.step_pos.ne' hf hx n)
end nesterov.Realization
