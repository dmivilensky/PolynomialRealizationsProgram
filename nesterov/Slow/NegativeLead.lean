import nesterov.Slow.FixedRoot
import nesterov.Slow.EvalControl
import nesterov.Faithful.Algebra
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
Article: Faithful discretization(c), negative effective lead.
A polynomial divided-difference identity replaces the analytic implicit-function
argument. It proves a growing fixed-curvature limit mode, then transfers that
mode to the actual continuous family.
-/
namespace nesterov.Slow.SecondOrderFamily
noncomputable section
open Polynomial Filter Set
open scoped Topology
variable {θ y : ℝ} (F : nesterov.Slow.SecondOrderFamily θ y)

def negativeLine (_F : nesterov.Slow.SecondOrderFamily θ y) (d : ℝ) : Polynomial ℂ := C 1+C (d:ℂ)*X

def negativeScaled (d : ℝ) : Polynomial ℂ :=
  ((F.u 0).map Complex.ofRealHom).comp (F.negativeLine d)-
    X^2*(F.q0.map Complex.ofRealHom).comp (F.negativeLine d)

def negativeLimit (_F : nesterov.Slow.SecondOrderFamily θ y) : Polynomial ℂ := C 1-X^2*C ((-1/y:ℝ):ℂ)

def oscillatoryRoot (_F : nesterov.Slow.SecondOrderFamily θ y) : ℂ := (Real.sqrt y:ℂ)*Complex.I

def negativeCorrection (d : ℝ) (z : ℂ) : ℂ :=
  -(y:ℂ)*z*((F.u 0 /ₘ (X-C 1)).eval₂ Complex.ofRealHom (1+(d:ℂ)*z)-
    z^2*(F.q0 /ₘ (X-C 1)).eval₂ Complex.ofRealHom (1+(d:ℂ)*z))/(z+F.oscillatoryRoot)

def negativeRadius (d : ℝ) (z : ℂ) : ℝ := 2*(F.negativeCorrection d z).re+Complex.normSq z

lemma tail_eval_one (p : Polynomial ℝ) : (p /ₘ (X-C 1)).eval 1=p.derivative.eval 1 := by
  have hh := congrArg (Polynomial.eval (1:ℝ))
    (divByMonic_add_X_sub_C_mul_derivative_divByMonic_eq_derivative p 1)
  simpa only [eval_add,eval_mul,eval_sub,eval_X,eval_C,sub_self,zero_mul,add_zero] using hh

theorem negativeScaled_eval (d : ℝ) (z : ℂ) :
    (F.negativeScaled d).eval z=(F.u 0).eval₂ Complex.ofRealHom (1+(d:ℂ)*z)-
      z^2*F.q0.eval₂ Complex.ofRealHom (1+(d:ℂ)*z) := by
  simp only [negativeScaled,negativeLine,eval_sub,eval_mul,eval_pow,eval_comp,eval_add,eval_C,eval_X,eval_map]

theorem negativeScaled_degree (d : ℝ) : (F.negativeScaled d).natDegree≤F.memory+2 := by
  have hl : (F.negativeLine d).natDegree≤1 := by
    unfold negativeLine
    exact (natDegree_add_le _ _).trans (max_le (by simp) (natDegree_mul_le.trans (by simp)))
  have hu : (((F.u 0).map Complex.ofRealHom).comp (F.negativeLine d)).natDegree≤F.memory :=
    natDegree_comp_le.trans ((Nat.mul_le_mul (natDegree_map_le.trans (F.u_natDegree_lt 0).le) hl).trans (by simp))
  have hq : ((F.q0.map Complex.ofRealHom).comp (F.negativeLine d)).natDegree≤F.memory := by
    have hqdeg : F.q0.natDegree≤F.memory := by rw [←F.quotient_zero];exact F.quotient_natDegree_le 0
    exact natDegree_comp_le.trans ((Nat.mul_le_mul (natDegree_map_le.trans hqdeg) hl).trans (by simp))
  have hp : (X^2*(F.q0.map Complex.ofRealHom).comp (F.negativeLine d)).natDegree≤2+F.memory :=
    natDegree_mul_le.trans (Nat.add_le_add (by simp) hq)
  exact (natDegree_sub_le _ _).trans (max_le (by omega) (by omega))

theorem negativeScaled_tendsto (z : ℂ) :
    Tendsto (fun d=>(F.negativeScaled d).eval z) (𝓝[>] (0:ℝ)) (𝓝 (F.negativeLimit.eval z)) := by
  have h : Continuous (fun d : ℝ=>(F.u 0).eval₂ Complex.ofRealHom (1+(d:ℂ)*z)-
    z^2*F.q0.eval₂ Complex.ofRealHom (1+(d:ℂ)*z)) := by fun_prop
  have hh := (h.tendsto 0).mono_left (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ)≤𝓝 (0:ℝ))
  simp only [Complex.ofReal_zero,zero_mul,add_zero] at hh
  have hu1 : (F.u 0).eval₂ Complex.ofRealHom 1=1 := by
    simpa only [map_one,F.u_one] using eval₂_at_apply (p:=F.u 0) Complex.ofRealHom (1:ℝ)
  have hq1 : F.q0.eval₂ Complex.ofRealHom 1=((-1/y:ℝ):ℂ) := by
    convert eval₂_at_apply (p:=F.q0) Complex.ofRealHom (1:ℝ) using 1
    rw [F.q0_one]
    rfl
  rw [hu1,hq1] at hh
  simpa only [negativeScaled_eval,negativeLimit,eval_sub,eval_C,eval_mul,eval_pow,eval_X] using hh

theorem oscillatoryRoot_sq : F.oscillatoryRoot^2= -(y:ℂ) := by
  unfold oscillatoryRoot
  rw [mul_pow,Complex.I_sq,←Complex.ofReal_pow,Real.sq_sqrt F.step_pos.le]
  ring

theorem oscillatoryRoot_re : F.oscillatoryRoot.re=0 := by simp [oscillatoryRoot]

theorem oscillatoryRoot_normSq : Complex.normSq F.oscillatoryRoot=y := by
  simp only [oscillatoryRoot,Complex.normSq_mul,Complex.normSq_ofReal,Complex.normSq_I,mul_one]
  simpa only [pow_two] using Real.sq_sqrt F.step_pos.le

theorem oscillatoryRoot_ne_zero : F.oscillatoryRoot≠0 := by
  intro hz
  have hh := F.oscillatoryRoot_normSq
  rw [hz,Complex.normSq_zero] at hh
  exact F.step_pos.ne' hh.symm

theorem oscillatoryRoot_isRoot : F.negativeLimit.eval F.oscillatoryRoot=0 := by
  simp only [negativeLimit,eval_sub,eval_mul,eval_pow,eval_X,eval_C,F.oscillatoryRoot_sq]
  push_cast
  field_simp [F.step_pos.ne']
  ring

theorem negativeLimit_ne_zero : F.negativeLimit≠0 := by
  intro hz
  have hh := congrArg (Polynomial.eval (0:ℂ)) hz
  simp [negativeLimit] at hh


theorem negativeCorrection_zero :
    F.negativeCorrection 0 F.oscillatoryRoot=
      ((-(y/2)*((F.u 0).derivative.eval 1+y*F.q0.derivative.eval 1):ℝ):ℂ) := by
  have he (p : Polynomial ℝ) : p.eval₂ Complex.ofRealHom 1=((p.eval (1:ℝ):ℝ):ℂ) :=
    eval₂_at_apply (p:=p) Complex.ofRealHom (1:ℝ)
  simp only [negativeCorrection,Complex.ofReal_zero,zero_mul,add_zero,he,tail_eval_one,F.oscillatoryRoot_sq]
  rw [show F.oscillatoryRoot+F.oscillatoryRoot=2*F.oscillatoryRoot by ring]
  push_cast
  field_simp [F.oscillatoryRoot_ne_zero]
  ring

theorem negativeRadius_zero :
    F.negativeRadius 0 F.oscillatoryRoot=
      -y*nesterov.Faithful.effectiveLead (F.u 0) F.q0 y := by
  simp only [negativeRadius,F.negativeCorrection_zero,Complex.ofReal_re,F.oscillatoryRoot_normSq]
  unfold nesterov.Faithful.effectiveLead
  ring

theorem negativeCorrection_continuousAt :
    ContinuousAt (fun p : ℝ × ℂ=>F.negativeCorrection p.1 p.2) (0,F.oscillatoryRoot) := by
  have hden : F.oscillatoryRoot+F.oscillatoryRoot≠0 := by
    rw [←two_mul]
    exact mul_ne_zero (by norm_num) F.oscillatoryRoot_ne_zero
  unfold negativeCorrection
  have hn : ContinuousAt (fun p : ℝ × ℂ=>
    -(y:ℂ)*p.2*((F.u 0 /ₘ (X-C 1)).eval₂ Complex.ofRealHom (1+(p.1:ℂ)*p.2)-
      p.2^2*(F.q0 /ₘ (X-C 1)).eval₂ Complex.ofRealHom (1+(p.1:ℂ)*p.2))) (0,F.oscillatoryRoot) := by fun_prop
  have hd : ContinuousAt (fun p : ℝ × ℂ=>p.2+F.oscillatoryRoot) (0,F.oscillatoryRoot) := by fun_prop
  convert hn.div hd hden using 1

theorem negativeRadius_continuousAt :
    ContinuousAt (fun p : ℝ × ℂ=>F.negativeRadius p.1 p.2) (0,F.oscillatoryRoot) := by
  unfold negativeRadius
  exact (Complex.continuous_re.continuousAt.comp F.negativeCorrection_continuousAt).const_mul 2 |>.add (by fun_prop)

/-- The first-order displacement of any nearby slow root is an exact quotient. -/
theorem negative_root_displacement {d : ℝ} {z : ℂ}
    (hroot : (F.negativeScaled d).eval z=0) (hden : z+F.oscillatoryRoot≠0) :
    z-F.oscillatoryRoot=(d:ℂ)*F.negativeCorrection d z := by
  let Z := 1+(d:ℂ)*z
  have hu := nesterov.Slow.eval_sub_eval_one (F.u 0) Z
  have hq := nesterov.Slow.eval_sub_eval_one F.q0 Z
  rw [F.u_one,Complex.ofReal_one] at hu
  rw [F.q0_one] at hq
  have hU : (F.u 0).eval₂ Complex.ofRealHom Z=
      1+(d:ℂ)*z*(F.u 0 /ₘ (X-C 1)).eval₂ Complex.ofRealHom Z := by
    dsimp [Z] at hu ⊢
    linear_combination hu
  have hQ : F.q0.eval₂ Complex.ofRealHom Z=
      ((-1/y:ℝ):ℂ)+(d:ℂ)*z*(F.q0 /ₘ (X-C 1)).eval₂ Complex.ofRealHom Z := by
    dsimp [Z] at hq ⊢
    linear_combination hq
  rw [F.negativeScaled_eval] at hroot
  change (F.u 0).eval₂ Complex.ofRealHom Z-z^2*F.q0.eval₂ Complex.ofRealHom Z=0 at hroot
  rw [hU,hQ] at hroot
  push_cast at hroot
  have hy : (y:ℂ)≠0 := Complex.ofReal_ne_zero.mpr F.step_pos.ne'
  field_simp [hy] at hroot
  unfold negativeCorrection
  change z-F.oscillatoryRoot=(d:ℂ)*
    (-(y:ℂ)*z*((F.u 0 /ₘ (X-C 1)).eval₂ Complex.ofRealHom Z-
      z^2*(F.q0 /ₘ (X-C 1)).eval₂ Complex.ofRealHom Z)/(z+F.oscillatoryRoot))
  field_simp [hden]
  linear_combination hroot-F.oscillatoryRoot_sq

theorem negative_root_radius_identity {d : ℝ} {z : ℂ}
    (hroot : (F.negativeScaled d).eval z=0) (hden : z+F.oscillatoryRoot≠0) :
    Complex.normSq (1+(d:ℂ)*z)-1=d^2*F.negativeRadius d z := by
  have hh := congrArg Complex.re (F.negative_root_displacement hroot hden)
  simp only [Complex.sub_re,F.oscillatoryRoot_re,sub_zero,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero] at hh
  simp only [Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.one_re,Complex.one_im,
    Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,zero_add,
    negativeRadius]
  rw [hh]
  ring


theorem negative_lead_growing_roots
    (hlead : nesterov.Faithful.effectiveLead (F.u 0) F.q0 y<0) :
    ∀ᶠ d in 𝓝[>] (0:ℝ),0<d ∧ d<1 ∧ ∃ Z : ℂ,
      (F.method 0).characteristic (d^2) Z=0 ∧ 1<‖Z‖ := by
  have hr0 : 0<F.negativeRadius 0 F.oscillatoryRoot := by
    rw [F.negativeRadius_zero]
    exact mul_pos_of_neg_of_neg (by linarith [F.step_pos]) hlead
  have hpos := F.negativeRadius_continuousAt.tendsto.eventually (eventually_gt_nhds hr0)
  have hd0 : F.oscillatoryRoot+F.oscillatoryRoot≠0 := by
    rw [←two_mul]
    exact mul_ne_zero (by norm_num) F.oscillatoryRoot_ne_zero
  have hdc : ContinuousAt (fun p : ℝ × ℂ=>p.2+F.oscillatoryRoot) (0,F.oscillatoryRoot) := by fun_prop
  have hden := hdc.tendsto.eventually_ne hd0
  have hgood : ∀ᶠ p : ℝ × ℂ in 𝓝 (0,F.oscillatoryRoot),
      0<F.negativeRadius p.1 p.2 ∧ p.2+F.oscillatoryRoot≠0 := hpos.and hden
  obtain ⟨η,hη,hball⟩ := Metric.eventually_nhds_iff.mp hgood
  have hroots := nesterov.Slow.eventually_exists_root_near F.negativeScaled_degree
    F.negativeScaled_tendsto F.negativeLimit_ne_zero F.oscillatoryRoot_isRoot hη
  have hsmall : ∀ᶠ d in 𝓝[>] (0:ℝ),d<min η 1 :=
    (eventually_lt_nhds (lt_min hη zero_lt_one)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hroots,hsmall,self_mem_nhdsWithin] with d hroot hd hp
  change 0<d at hp
  have hdη := (lt_min_iff.mp hd).1
  have hd1 := (lt_min_iff.mp hd).2
  obtain ⟨z,hz,hnear⟩ := hroot
  have hdist : dist (d,z) (0,F.oscillatoryRoot)<η := by
    rw [Prod.dist_eq]
    apply max_lt
    · simpa only [Real.dist_eq,sub_zero,abs_of_pos hp] using hdη
    · simpa only [dist_eq_norm] using hnear
  obtain ⟨hrad,hden⟩ := hball hdist
  have hid := F.negative_root_radius_identity hz hden
  have hn : 1<‖1+(d:ℂ)*z‖ := by
    rw [Complex.normSq_eq_norm_sq] at hid
    have hprod := mul_pos (sq_pos_of_pos hp) hrad
    nlinarith [norm_nonneg (1+(d:ℂ)*z)]
  refine ⟨hp,hd1,1+(d:ℂ)*z,?_,hn⟩
  rw [F.negativeScaled_eval] at hz
  rw [(F.method 0).characteristic_eq_polynomial_eval]
  simp only [eval_sub,eval_mul,eval_C,eval_map]
  change (F.v 0).eval₂ Complex.ofRealHom (1+(d:ℂ)*z)-
    (d^2:ℝ)*(F.u 0).eval₂ Complex.ofRealHom (1+(d:ℂ)*z)=0
  have hfac : F.v 0=(X-C 1)^2*F.q0 := F.initial_factor
  rw [hfac]
  simp only [eval₂_mul,eval₂_pow,eval₂_sub,eval₂_X,eval₂_C]
  have hc (r : ℝ) : Complex.ofRealHom r=(r:ℂ) := rfl
  simp only [hc,Complex.ofReal_one]
  push_cast
  linear_combination -(d:ℂ)^2*hz

theorem exists_unstable_limit_mode
    (hlead : nesterov.Faithful.effectiveLead (F.u 0) F.q0 y<0) :
    ∃ lam∈Ioo (0:ℝ) 1,∃ z : ℂ,(F.method 0).characteristic lam z=0 ∧ 1<‖z‖ := by
  obtain ⟨d,hd,hsmall,z,hz,hn⟩ := (F.negative_lead_growing_roots hlead).exists
  exact ⟨d^2,⟨sq_pos_of_pos hd,by nlinarith⟩,z,hz,hn⟩


/-- Negative effective lead gives a uniform quadratic divergence margin for
all sufficiently small members of the original continuous family. -/
theorem negative_lead_quadratic_lower
    (hlead : nesterov.Faithful.effectiveLead (F.u 0) F.q0 y<0) :
    ∃ lam∈Ioo (0:ℝ) 1,∃ r : ℝ,1<r ∧ ∀ᶠ ε in 𝓝[>] (0:ℝ),
      ∃ z : ℂ,(F.method ε).characteristic lam z=0 ∧ r<‖z‖ ∧
        r<nesterov.Rates.quadraticRate (F.method ε) (ε^2) 1 := by
  obtain ⟨lam,hlam,z,hz,hn⟩ := F.exists_unstable_limit_mode hlead
  obtain ⟨r,hr,he⟩ := F.fixed_unstable_root_lower hlam hz hn
  exact ⟨lam,hlam,r,hr,he⟩

end
end nesterov.Slow.SecondOrderFamily
