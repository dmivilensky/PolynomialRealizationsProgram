import nesterov.Robust.TMM
import nesterov.Momentum.QueryRates

/-! TMM's reported extrapolated point is measured on the same actual
trajectories. Its literal uniform from-rest root factor equals the design rate. -/
namespace nesterov.Robust
noncomputable section
open Set Filter
open scoped Topology

def reportedRatios (D : Design) (δ : ℝ) (n : ℕ) : Set ℝ :=
  {x | ∃ r : Rates.HilbertRun (Momentum.method D.beta D.tau D.step D.step_pos.ne') (1/D.kappa) 1,
    ∃ _ : FiniteDimensional ℝ r.Carrier,
    r.FromRest ∧ r.w 0≠0 ∧ x=‖(1+δ) • r.w (n+1)-δ • r.w n‖/‖r.w 0‖}

def reportedEnvelope (D : Design) (δ : ℝ) (n : ℕ) : ℝ :=
  sSup (insert 0 (reportedRatios D δ n))

def reportedRate (D : Design) (δ : ℝ) : ℝ :=
  limsup (fun n : ℕ=>reportedEnvelope D δ n^((n:ℝ)⁻¹)) atTop

theorem reported_norm_bound (D : Design) {δ : ℝ} (hδ : 0≤δ)
    (r : Rates.HilbertRun (Momentum.method D.beta D.tau D.step D.step_pos.ne') (1/D.kappa) 1)
    (n : ℕ) :
    ‖(1+δ) • r.w (n+1)-δ • r.w n‖≤
      (1+2*δ)*(Momentum.method D.beta D.tau D.step D.step_pos.ne').stateNorm r.w n := by
  let M := Momentum.method D.beta D.tau D.step D.step_pos.ne'
  have h₀ : ‖r.w n‖≤M.stateNorm r.w n := by simpa using M.norm_le_stateNorm r.w n (0:Fin 2)
  have h₁ : ‖r.w (n+1)‖≤M.stateNorm r.w n := M.norm_le_stateNorm r.w n (1:Fin 2)
  calc
    _≤‖(1+δ) • r.w (n+1)‖+‖δ • r.w n‖ := norm_sub_le _ _
    _=(1+δ)*‖r.w (n+1)‖+δ*‖r.w n‖ := by
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
        abs_of_nonneg (by linarith),abs_of_nonneg hδ]
    _≤(1+δ)*M.stateNorm r.w n+δ*M.stateNorm r.w n :=
      add_le_add (mul_le_mul_of_nonneg_left h₁ (by linarith))
        (mul_le_mul_of_nonneg_left h₀ hδ)
    _=_ := by ring

theorem reported_ratios_bound (D : Design) {δ : ℝ} (hδ : 0≤δ) (n : ℕ)
    {x : ℝ} (hx : x∈insert 0 (reportedRatios D δ n)) :
    x≤(1+2*δ)*Real.sqrt 2*Rates.envelope
      (Momentum.method D.beta D.tau D.step D.step_pos.ne') (1/D.kappa) 1 n := by
  let M := Momentum.method D.beta D.tau D.step D.step_pos.ne'
  rcases hx with rfl|⟨r,_,hr,hz,rfl⟩
  · exact mul_nonneg (mul_nonneg (by linarith) (Real.sqrt_nonneg _)) (Rates.envelope_nonneg _ _ _ _)
  · apply (div_le_iff₀ (norm_pos_iff.mpr hz)).mpr
    have hb := Rates.stateNorm_le_envelope r n
    rw [hr.stateNorm_zero] at hb
    change M.stateNorm r.w n≤Rates.envelope M (1/D.kappa) 1 n*(Real.sqrt 2*‖r.w 0‖) at hb
    exact (reported_norm_bound D hδ r n).trans
      ((mul_le_mul_of_nonneg_left hb (show 0≤1+2*δ by linarith)).trans_eq (by ring))

theorem reported_bddAbove (D : Design) {δ : ℝ} (hδ : 0≤δ) (n : ℕ) :
    BddAbove (insert 0 (reportedRatios D δ n)) :=
  ⟨_,fun _ hx=>reported_ratios_bound D hδ n hx⟩

theorem reported_nonneg (D : Design) {δ : ℝ} (hδ : 0≤δ) (n : ℕ) :
    0≤reportedEnvelope D δ n :=
  le_csSup (reported_bddAbove D hδ n) (mem_insert _ _)

theorem reported_envelope_le (D : Design) {δ : ℝ} (hδ : 0≤δ) (n : ℕ) :
    reportedEnvelope D δ n≤(1+2*δ)*Real.sqrt 2*Rates.envelope
      (Momentum.method D.beta D.tau D.step D.step_pos.ne') (1/D.kappa) 1 n :=
  csSup_le (insert_nonempty _ _) (fun _ hx=>reported_ratios_bound D hδ n hx)

theorem reported_roots_bounded (D : Design) {δ : ℝ} (hδ : 0≤δ) :
    IsBoundedUnder (·≤·) atTop (fun n : ℕ=>reportedEnvelope D δ n^((n:ℝ)⁻¹)) := by
  let M := Momentum.method D.beta D.tau D.step D.step_pos.ne'
  have hC : 0<(1+2*δ)*Real.sqrt 2 := mul_pos (by linarith) (by positivity)
  apply Rates.roots_bounded_of_mul_pow (reported_nonneg D hδ) hC (M.stepBound_pos 1)
  intro n
  exact (reported_envelope_le D hδ n).trans
    (mul_le_mul_of_nonneg_left (Rates.envelope_le M (1/D.kappa) 1 n) hC.le)

theorem reported_rate_le (D : Design) {δ : ℝ} (hδ : 0≤δ) : reportedRate D δ≤D.rho := by
  have h := Rates.limsup_root_le_of_mul_bound (reported_nonneg D hδ)
    (Rates.envelope_nonneg (Momentum.method D.beta D.tau D.step D.step_pos.ne') (1/D.kappa) 1)
    (mul_pos (show 0<1+2*δ by linarith) (by positivity : 0<Real.sqrt 2))
    (reported_envelope_le D hδ)
    (Rates.tendsto_envelope_root (Momentum.method D.beta D.tau D.step D.step_pos.ne') D.mu_pos D.mu_lt_one)
  change reportedRate D δ≤Momentum.momentumRate D.beta D.tau D.step D.step_pos.ne' (1/D.kappa) 1 at h
  rwa [D.exact_rates.1] at h

namespace Design
variable (D : Design)

def reportedDelta : ℝ := D.rho^2/(1-D.rho^2)

theorem reportedDelta_nonneg : 0≤D.reportedDelta := by
  unfold reportedDelta
  have hh : D.rho^2<1 := by nlinarith [D.rho_pos,D.rho_lt_one]
  positivity

theorem reportedDelta_pole : D.reportedDelta/(1+D.reportedDelta)=D.rho^2 := by
  unfold reportedDelta
  have hh : 1-D.rho^2≠0 := by nlinarith [D.rho_pos,D.rho_lt_one]
  field_simp [hh]
  ring

theorem reported_quadratic (n : ℕ) :
    (1+D.reportedDelta)*Momentum.history (fun x : ℝ=>(1/D.kappa)*x)
      D.beta D.tau D.step 1 1 (n+1)-
      D.reportedDelta*Momentum.history (fun x : ℝ=>(1/D.kappa)*x)
        D.beta D.tau D.step 1 1 n=D.rho^n := by
  let w := Momentum.history (fun x : ℝ=>(1/D.kappa)*x) D.beta D.tau D.step 1 1
  have hw (n : ℕ) : w (n+2)=(D.rho+D.rho^2)*w (n+1)-D.rho^3*w n := by
    have h := Momentum.history_recurrence (fun x : ℝ=>(1/D.kappa)*x) D.beta D.tau D.step 1 1 n
    simp only [smul_eq_mul] at h
    change w (n+2)=w (n+1)+D.beta*(w (n+1)-w n)-
      D.step*((1/D.kappa)*(w (n+1)+D.tau*(w (n+1)-w n))) at h
    rw [←D.S_mu,←D.Q_mu]
    unfold Quadratic.S Quadratic.Q
    nlinarith
  have hden : 1-D.rho^2≠0 := by nlinarith [D.rho_pos,D.rho_lt_one]
  change (1+D.reportedDelta)*w (n+1)-D.reportedDelta*w n=D.rho^n
  induction n with
  | zero => simp [w,reportedDelta]
  | succ n ih =>
    rw [show n+1+1=n+2 by omega,hw n,pow_succ]
    unfold reportedDelta at ih ⊢
    field_simp [hden] at ih ⊢
    linear_combination D.rho*ih

theorem reported_envelope_lower (n : ℕ) :
    D.rho^n≤reportedEnvelope D D.reportedDelta n := by
  let f : ℝ→ℝ := fun x=>(1/D.kappa)/2*‖x‖^2
  have hf : polyak.CenteredSmoothStronglyConvex (1/D.kappa) 1 f :=
    Momentum.real_quadratic_centered D.mu_pos D.mu_lt_one (left_mem_Icc.mpr D.mu_lt_one.le)
  let r : Rates.HilbertRun (Momentum.method D.beta D.tau D.step D.step_pos.ne') (1/D.kappa) 1 :=
    ⟨ℝ,f,hf,Momentum.history (gradient f) D.beta D.tau D.step 1 1,
      Momentum.history_isTrajectory _ D.beta D.tau D.step D.step_pos.ne' _ _⟩
  have hr : r.FromRest := by intro j;fin_cases j <;> rfl
  apply le_csSup (reported_bddAbove D D.reportedDelta_nonneg n)
  refine mem_insert_of_mem _ ⟨r,inferInstance,hr,by simp [r],?_⟩
  have hg : gradient f=(fun x : ℝ=>(1/D.kappa)*x) :=
    funext (Momentum.real_quadratic_gradient (1/D.kappa))
  change D.rho^n=‖(1+D.reportedDelta)*Momentum.history (gradient f)
    D.beta D.tau D.step 1 1 (n+1)-D.reportedDelta*Momentum.history (gradient f)
      D.beta D.tau D.step 1 1 n‖/‖(1:ℝ)‖
  rw [hg,D.reported_quadratic,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg D.rho_pos.le _),
    norm_one,div_one]

theorem reported_exact_rate : reportedRate D D.reportedDelta=D.rho := by
  apply le_antisymm (reported_rate_le D D.reportedDelta_nonneg)
  have h := Rates.exp_le_root_limsup_of_lower_bound (C:=1) (t:=Real.log D.rho)
    zero_lt_one (fun n=>?_)
    (reported_roots_bounded D D.reportedDelta_nonneg)
  · simpa only [reportedRate,Real.exp_log D.rho_pos] using h
  · rw [one_mul,Real.exp_nat_mul,Real.exp_log D.rho_pos]
    exact D.reported_envelope_lower n

end Design
end
end nesterov.Robust
