import nesterov.Robust.Asymptotics

/-! Fixed robust design constant c: the physical slow data lie on the
source balance curve (3c,2c²,1/(2c²)). -/
namespace nesterov.Robust.Design
noncomputable section
open Filter
open scoped Topology

theorem epsilon_square {D : Robust.Design} {ε : ℝ} (he : D.kappa*ε^2=1) :
    0<1-ε^2 := by
  nlinarith [D.kappa_gt_one,sq_nonneg ε]

theorem balance_beta {D : Robust.Design} {ε : ℝ} (he : D.kappa*ε^2=1) :
    D.beta*(1-ε^2)=D.rho^3 := by
  have hb : D.beta*(D.kappa-1)=D.kappa*D.rho^3 :=
    (div_mul_cancel₀ _ (show D.kappa-1≠0 by linarith [D.kappa_gt_one]))
  have hp : (D.kappa-1)*ε^2=1-ε^2 := by nlinarith [he]
  calc
    _=D.beta*((D.kappa-1)*ε^2) := by rw [hp]
    _=(D.beta*(D.kappa-1))*ε^2 := by ring
    _=(D.kappa*ε^2)*D.rho^3 := by rw [hb];ring
    _=D.rho^3 := by rw [he,one_mul]

theorem balance_step {D : Robust.Design} {ε c : ℝ}
    (he : D.kappa*ε^2=1) (hr : D.rho=1-c*ε) : D.step=c^2*(1+D.rho) := by
  unfold step
  rw [show 1-D.rho=c*ε by linarith [hr]]
  calc
    _=c^2*(D.kappa*ε^2)*(1+D.rho) := by ring
    _=_ := by rw [he,mul_one]

theorem balance_theta {D : Robust.Design} {ε c : ℝ}
    (he : D.kappa*ε^2=1) (hep : 0<ε) (hr : D.rho=1-c*ε) :
    (1-D.beta)/ε=(3*c-(3*c^2+1)*ε+c^3*ε^2)/(1-ε^2) := by
  apply (div_eq_div_iff hep.ne' (epsilon_square he).ne').mpr
  calc
    _=(1-ε^2)-D.rho^3 := by nlinarith [balance_beta he]
    _=_ := by rw [hr];ring

theorem balance_tau {D : Robust.Design} {ε c : ℝ}
    (he : D.kappa*ε^2=1) (hc : 0<c) (hr : D.rho=1-c*ε) :
    D.tau=D.rho^3/(c^2*(1+D.rho)*(1-ε^2)) := by
  have hd : c^2*(1+D.rho)*(1-ε^2)≠0 :=
    (mul_pos (mul_pos (sq_pos_of_pos hc) (by linarith [D.rho_pos])) (epsilon_square he)).ne'
  apply (eq_div_iff hd).mpr
  calc
    _=(D.step*D.tau)*(1-ε^2) := by rw [balance_step he hr];ring
    _=_ := by rw [D.step_tau];exact balance_beta he

variable {A : Type*} {l : Filter A} (D : A→Robust.Design) {ε : A→ℝ} {c : ℝ}
    (he : ∀ a,(D a).kappa*ε a^2=1) (hep : ∀ a,0<ε a)
    (hr : ∀ a,(D a).rho=1-c*ε a) (hε : Tendsto ε l (𝓝 0)) (hc : 0<c)

include hr hε in
theorem balance_rho_tendsto : Tendsto (fun a=>(D a).rho) l (𝓝 1) := by
  have hh := (tendsto_const_nhds (x:=(1:ℝ))).sub (hε.const_mul c)
  simpa only [mul_zero,sub_zero,hr] using hh

include he hep hr hε in
theorem balance_theta_tendsto :
    Tendsto (fun a=>(1-(D a).beta)/ε a) l (𝓝 (3*c)) := by
  have hcont : ContinuousAt (fun x : ℝ=>(3*c-(3*c^2+1)*x+c^3*x^2)/(1-x^2)) 0 := by
    fun_prop (disch := norm_num)
  convert hcont.tendsto.comp hε using 1
  · funext a
    exact balance_theta (he a) (hep a) (hr a)
  · norm_num

include he hr hε in
theorem balance_step_tendsto : Tendsto (fun a=>(D a).step) l (𝓝 (2*c^2)) := by
  have hρ := balance_rho_tendsto D hr hε
  have hh := ((tendsto_const_nhds (x:=(1:ℝ))).add hρ).const_mul (c^2)
  convert hh using 1
  · funext a
    exact balance_step (he a) (hr a)
  · congr 1
    ring

include he hr hε hc in
theorem balance_tau_tendsto : Tendsto (fun a=>(D a).tau) l (𝓝 (1/(2*c^2))) := by
  have hρ := balance_rho_tendsto D hr hε
  have hnum := hρ.pow 3
  have hden := (((tendsto_const_nhds (x:=(1:ℝ))).add hρ).const_mul (c^2)).mul
    ((tendsto_const_nhds (x:=(1:ℝ))).sub (hε.pow 2))
  have hd : c^2*(1+(1:ℝ))*(1-0^2)≠0 := by positivity
  have hh := hnum.div hden hd
  convert hh using 1
  · funext a
    exact balance_tau (he a) hc (hr a)
  · norm_num
    ring

theorem balance_constants {c : ℝ} (hc : 0<c) :
    Flow.cF (3*c) (2*c^2)=c ∧ Flow.cQ (3*c) (2*c^2)=c ∧
      3*c=3*Real.sqrt ((2*c^2)/2) := by
  have hq : Flow.cQ 3 2=1 := by norm_num [Flow.cQ]
  have hf : Flow.cF 3 2=1 := by norm_num [Flow.cF,hq]
  have hs : (2*c^2)/2=c^2 := by ring
  constructor
  · have h := Flow.cF_scale hc 3 2
    rw [hf,mul_one] at h
    simpa only [mul_comm] using h
  constructor
  · have h := Flow.cQ_scale hc 3 2
    rw [hq,mul_one] at h
    simpa only [mul_comm] using h
  · rw [hs,Real.sqrt_sq hc.le]

end
end nesterov.Robust.Design
