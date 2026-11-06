import nesterov.TwoStep.QuadraticAsymptotics
import nesterov.Momentum.RestQuadratic
import Mathlib.Analysis.Calculus.DSlope

/-! The fixed scalar from-rest witness in the quadratic branch of Theorem B(a). -/
namespace nesterov.TwoStep
noncomputable section
open Filter Set
open scoped Topology

/-- A positive Vieta pair gives a lower bound at every horizon from rest. -/
theorem rest_iterate_lower_of_positive_roots {β τ h lam a b : ℝ}
    (ha : 0≤a) (hb : 0≤b) (ha1 : a≤1)
    (hsum : a+b=Quadratic.S β τ h lam) (hprod : a*b=Quadratic.Q β τ h lam) :
    ∀ n : ℕ,a^n≤Momentum.iterate (fun x : ℝ=>lam*x) β τ h 1 n := by
  let x : ℕ→ℝ := Momentum.iterate (fun x : ℝ=>lam*x) β τ h 1
  have hrec := Momentum.quadratic_iterate_recurrence β τ h lam 1
  have hinc : ∀ n : ℕ,a*x n≤x (n+1) := by
    intro n
    induction n with
    | zero =>
      have h₁ : x 1=Quadratic.S β τ h lam-Quadratic.Q β τ h lam := by
        dsimp [x]
        rw [Momentum.iterate_one]
        simp only [smul_eq_mul,mul_one]
        unfold Quadratic.S Quadratic.Q
        ring
      rw [h₁,←hsum,←hprod]
      have hx₀ : x 0=1 := rfl
      rw [hx₀]
      nlinarith [mul_nonneg hb (sub_nonneg.mpr ha1)]
    | succ n ih =>
      have hh := hrec n
      change x (n+2)=Quadratic.S β τ h lam*x (n+1)-Quadratic.Q β τ h lam*x n at hh
      rw [←hsum,←hprod] at hh
      have hp := mul_le_mul_of_nonneg_left ih hb
      simpa only [Nat.succ_eq_add_one,Nat.add_assoc] using (by nlinarith : a*x (n+1)≤x (n+2))
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hh := (mul_le_mul_of_nonneg_left ih ha).trans (hinc n)
    simpa only [pow_succ,mul_comm] using hh

private theorem exp_decay_secant_tendsto {A : Type*} {l : Filter A} {e : A→ℝ}
    (he : Tendsto e l (𝓝[>] (0:ℝ))) (k : ℝ) :
    Tendsto (fun a=>(1-Real.exp (-k*e a))/e a) l (𝓝 k) := by
  have hz : Tendsto (fun a=>-k*e a) l (𝓝 0) := by
    simpa only [mul_zero] using (he.mono_right nhdsWithin_le_nhds).const_mul (-k)
  have hc : ContinuousAt (dslope Real.exp 0) 0 :=
    continuousAt_dslope_same.mpr Real.differentiable_exp.differentiableAt
  have hv : dslope Real.exp 0 0=1 := by
    simpa only [dslope_same,Real.exp_zero] using (Real.hasDerivAt_exp 0).deriv
  have ht := (hc.tendsto.comp hz).const_mul k
  rw [hv,mul_one] at ht
  apply ht.congr'
  filter_upwards [he.eventually self_mem_nhdsWithin] with a ha
  have hh := sub_smul_dslope Real.exp 0 (-k*e a)
  simp only [sub_zero,smul_eq_mul,Real.exp_zero] at hh
  dsimp only [Function.comp_def]
  apply (eq_div_iff (ne_of_gt ha)).mpr
  linear_combination -hh

namespace Scaling
variable {A : Type*} {l : Filter A} {θ y τ : ℝ} (F : Scaling A l θ y τ)

/-- One literal scalar quadratic and the fixed from-rest initialization work
at every horizon, with the full exponential lower bound of Theorem B(a). -/
theorem quadratic_branch_rest_lower (hbranch : Flow.cQ θ y≤θ/3) {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ a in l,∀ n : ℕ,Real.exp (-(Flow.cQ θ y+δ)*F.epsilon a*n)≤
      |Momentum.iterate (fun x : ℝ=>F.epsilon a^2*x) (F.tuning a).beta
        (F.tuning a).tau (F.tuning a).stepSize 1 n| := by
  have hdisc : 0<θ^2-4*y := by
    by_contra hn
    have hh := Flow.cQ_eq_half (by linarith : θ^2≤4*y)
    rw [hh] at hbranch
    linarith [F.theta_pos]
  let t : A→ℝ := fun a=>F.thetaAt a+(F.tuning a).stepSize*(1+(F.tuning a).tau)*F.epsilon a
  have ht : Tendsto t l (𝓝 θ) := by
    have hh := F.theta_tendsto.add ((F.step_tendsto.mul
      ((tendsto_const_nhds (x:=(1:ℝ))).add F.tau_tendsto)).mul F.epsilon_zero)
    simp only [mul_zero,add_zero] at hh
    convert hh using 1
    funext a
    rfl
  let d : A→ℝ := fun a=>Real.sqrt ((t a)^2-4*(F.tuning a).stepSize)
  have hD := (ht.pow 2).sub (F.step_tendsto.const_mul 4)
  have hd : Tendsto d l (𝓝 (Real.sqrt (θ^2-4*y))) := hD.sqrt
  let u : A→ℝ := fun a=>(t a-d a)/2
  let v : A→ℝ := fun a=>(t a+d a)/2
  have hCQ : (θ-Real.sqrt (θ^2-4*y))/2=Flow.cQ θ y := by
    unfold Flow.cQ
    rw [ite_eq_right (by linarith : ¬θ^2<4*y)]
  have hu : Tendsto u l (𝓝 (Flow.cQ θ y)) := by simpa only [hCQ] using (ht.sub hd).div_const 2
  have hv := (ht.add hd).div_const 2
  let r : A→ℝ := fun a=>1-F.epsilon a*u a
  let s : A→ℝ := fun a=>1-F.epsilon a*v a
  have hr : Tendsto r l (𝓝 1) := by simpa only [zero_mul,sub_zero] using
    (tendsto_const_nhds (x:=(1:ℝ))).sub (F.epsilon_zero.mul hu)
  have hs : Tendsto s l (𝓝 1) := by simpa only [zero_mul,sub_zero] using
    (tendsto_const_nhds (x:=(1:ℝ))).sub (F.epsilon_zero.mul hv)
  have hexp := exp_decay_secant_tendsto F.epsilon_tendsto (Flow.cQ θ y+δ)
  have hdiff := hexp.sub hu
  have hdiffpos : 0<(Flow.cQ θ y+δ)-Flow.cQ θ y := by linarith
  filter_upwards [F.epsilon_pos,F.beta_eq,hD.eventually (eventually_gt_nhds hdisc),
    hu.eventually (eventually_gt_nhds (Flow.cQ_pos F.theta_pos F.step_pos)),
    hr.eventually (eventually_gt_nhds (by norm_num : (0:ℝ)<1)),
    hs.eventually (eventually_gt_nhds (by norm_num : (0:ℝ)<1)),
    hdiff.eventually (eventually_gt_nhds hdiffpos)] with a he hβ hDa hua hra hsa hxa n
  have huv : u a*v a=(F.tuning a).stepSize := by
    have hsq := Real.sq_sqrt hDa.le
    dsimp [u,v,d]
    nlinarith
  have husum : u a+v a=t a := by dsimp [u,v];ring
  have hsum : r a+s a=Quadratic.S (F.tuning a).beta (F.tuning a).tau
      (F.tuning a).stepSize (F.epsilon a^2) := by
    rw [hβ]
    dsimp [r,s,Quadratic.S]
    rw [show 1-F.epsilon a*u a+(1-F.epsilon a*v a)=2-F.epsilon a*(u a+v a) by ring,husum]
    dsimp [t]
    ring
  have hprod : r a*s a=Quadratic.Q (F.tuning a).beta (F.tuning a).tau
      (F.tuning a).stepSize (F.epsilon a^2) := by
    rw [hβ]
    dsimp [r,s,Quadratic.Q]
    rw [show (1-F.epsilon a*u a)*(1-F.epsilon a*v a)=
      1-F.epsilon a*(u a+v a)+F.epsilon a^2*(u a*v a) by ring,husum,huv]
    dsimp [t]
    ring
  have hra1 : r a≤1 := by dsimp [r];nlinarith [mul_pos he hua]
  have hpoint := rest_iterate_lower_of_positive_roots hra.le hsa.le hra1 hsum hprod n
  have hbase : Real.exp (-(Flow.cQ θ y+δ)*F.epsilon a)≤r a := by
    have hh : u a<(1-Real.exp (-(Flow.cQ θ y+δ)*F.epsilon a))/F.epsilon a := by linarith
    have hmul := (lt_div_iff₀ he).mp hh
    dsimp [r]
    linarith
  have hpow := pow_le_pow_left₀ (Real.exp_pos _).le hbase n
  have hh := hpow.trans (hpoint.trans (le_abs_self _))
  convert hh using 1
  rw [←Real.exp_nat_mul]
  congr 1
  ring

end Scaling
end
end nesterov.TwoStep
