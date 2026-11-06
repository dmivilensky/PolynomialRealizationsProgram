import nesterov.Slow.ScaledLimit
import nesterov.Slow.RootPerturbation
import nesterov.Flow.QuadraticRates
import nesterov.Rates.QuadraticMaximum

/-! Actual slow characteristic roots and the quadratic ceiling, including critical damping. -/
namespace nesterov.Slow.SecondOrderFamily
noncomputable section
open Polynomial Filter Set
open scoped Topology
variable {θ y : ℝ} (F : nesterov.Slow.SecondOrderFamily θ y)

def affineSlow (_F : nesterov.Slow.SecondOrderFamily θ y) (ε : ℝ) : Polynomial ℂ := C 1-C (ε:ℂ)*X

def scaledCharacteristic (ε : ℝ) : Polynomial ℂ :=
  ((F.u ε).map Complex.ofRealHom).comp (F.affineSlow ε)+
    X*(C (F.thetaAt ε:ℂ)-X)*((F.quotient ε).map Complex.ofRealHom).comp (F.affineSlow ε)

def limitCharacteristic (_F : nesterov.Slow.SecondOrderFamily θ y) : Polynomial ℂ := C 1+X*(C (θ:ℂ)-X)*C ((-1/y:ℝ):ℂ)

theorem scaledCharacteristic_eval (ε : ℝ) (w : ℂ) :
    (F.scaledCharacteristic ε).eval w=
      (F.u ε).eval₂ Complex.ofRealHom (1-(ε:ℂ)*w)+
        w*((F.thetaAt ε:ℂ)-w)*(F.quotient ε).eval₂ Complex.ofRealHom (1-(ε:ℂ)*w) := by
  simp only [scaledCharacteristic,affineSlow,eval_add,eval_mul,eval_sub,eval_C,eval_X,
    eval_comp,eval_map]

theorem scaledCharacteristic_degree (ε : ℝ) : (F.scaledCharacteristic ε).natDegree≤F.memory+2 := by
  have hlin : (F.affineSlow ε).natDegree≤1 := by
    unfold affineSlow
    exact (natDegree_sub_le _ _).trans (max_le (by simp)
      (natDegree_mul_le.trans (by simp)))
  have hu : (((F.u ε).map Complex.ofRealHom).comp (F.affineSlow ε)).natDegree≤F.memory := by
    calc
      _ ≤ ((F.u ε).map Complex.ofRealHom).natDegree*(F.affineSlow ε).natDegree := natDegree_comp_le
      _ ≤ F.memory*1 := Nat.mul_le_mul (natDegree_map_le.trans (F.u_natDegree_lt ε).le) hlin
      _ = _ := Nat.mul_one _
  have hq : (((F.quotient ε).map Complex.ofRealHom).comp (F.affineSlow ε)).natDegree≤F.memory := by
    calc
      _ ≤ ((F.quotient ε).map Complex.ofRealHom).natDegree*(F.affineSlow ε).natDegree := natDegree_comp_le
      _ ≤ F.memory*1 := Nat.mul_le_mul (natDegree_map_le.trans (F.quotient_natDegree_le ε)) hlin
      _ = _ := Nat.mul_one _
  have hθ : (C (F.thetaAt ε:ℂ)-X).natDegree≤1 :=
    (natDegree_sub_le _ _).trans (max_le (by simp) (by simp))
  have hr : (X*(C (F.thetaAt ε:ℂ)-X)*((F.quotient ε).map Complex.ofRealHom).comp (F.affineSlow ε)).natDegree≤2+F.memory :=
    natDegree_mul_le.trans (Nat.add_le_add
      (natDegree_mul_le.trans (Nat.add_le_add (by simp) hθ)) hq)
  exact (natDegree_add_le _ _).trans (max_le (by omega) (by omega))

theorem scaledCharacteristic_tendsto (w : ℂ) :
    Tendsto (fun ε=>(F.scaledCharacteristic ε).eval w) (𝓝[>] (0:ℝ)) (𝓝 (F.limitCharacteristic.eval w)) := by
  have he : Tendsto (fun ε : ℝ=>(ε:ℂ)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    convert (Complex.continuous_ofReal.tendsto 0).comp
      (continuous_id.continuousWithinAt.tendsto : Tendsto (fun ε : ℝ=>ε) (𝓝[>] (0:ℝ)) (𝓝 0)) using 1
    funext a
    rfl
  have hz : Tendsto (fun ε : ℝ=>1-(ε:ℂ)*w) (𝓝[>] (0:ℝ)) (𝓝 1) := by simpa using tendsto_const_nhds.sub (he.mul_const w)
  have hu := F.u_eval_tendsto hz
  have hq := F.quotient_eval_tendsto hz
  have hθ := Complex.continuous_ofReal.tendsto θ |>.comp F.thetaAt_tendsto
  have hh := hu.add (((hθ.sub_const w).const_mul w).mul hq)
  simp only [scaledCharacteristic_eval]
  convert hh using 1
  · funext ε
    rfl
  · simp only [limitCharacteristic,eval_add,eval_mul,eval_sub,eval_C,eval_X]
    have hu1 : (F.u 0).eval₂ Complex.ofRealHom 1=1 := by
      simpa only [map_one,F.u_one] using eval₂_at_apply (p:=F.u 0) Complex.ofRealHom (1:ℝ)
    have hq1 : F.q0.eval₂ Complex.ofRealHom 1=((-1/y:ℝ):ℂ) := by
      convert eval₂_at_apply (p:=F.q0) Complex.ofRealHom (1:ℝ) using 1
      rw [F.q0_one]
      rfl
    rw [hu1,hq1]

theorem limitCharacteristic_ne_zero : F.limitCharacteristic≠0 := by
  intro h
  have hh := congrArg (Polynomial.eval (0:ℂ)) h
  simp [limitCharacteristic] at hh

/-- The exact affine slow polynomial generates actual characteristic roots. -/
theorem affine_characteristic_eq : ∀ᶠ ε in 𝓝[>] (0:ℝ),∀ w : ℂ,
    (F.method ε).characteristic (ε^2) (1-(ε:ℂ)*w)=
      -(ε:ℂ)^2*(F.scaledCharacteristic ε).eval w := by
  filter_upwards [F.factorization,self_mem_nhdsWithin] with ε hfac hε w
  have he : (ε:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hε)
  have hθ : (ε:ℂ)*(F.thetaAt ε:ℂ)=1-(F.beta ε:ℂ) := by
    dsimp [thetaAt]
    push_cast
    field_simp
  rw [(F.method ε).characteristic_eq_polynomial_eval]
  simp only [eval_sub,eval_mul,eval_C,eval_map]
  change ((F.v ε).eval₂ Complex.ofRealHom (1-(ε:ℂ)*w))-
    (ε^2:ℝ)*(F.u ε).eval₂ Complex.ofRealHom (1-(ε:ℂ)*w)=_
  rw [hfac,F.scaledCharacteristic_eval]
  simp only [eval₂_mul,eval₂_sub,eval₂_X,eval₂_C]
  have hcast (r : ℝ) : Complex.ofRealHom r=(r:ℂ) := rfl
  simp only [hcast]
  push_cast
  rw [show 1-(ε:ℂ)*w-(F.beta ε:ℂ)= (ε:ℂ)*(F.thetaAt ε:ℂ)-(ε:ℂ)*w by rw [hθ];ring]
  ring


/-- Every flow root is approached by actual quadratic roots in slow coordinates. -/
theorem actual_root_near {w₀ : ℂ} (hw₀ : F.limitCharacteristic.eval w₀=0)
    {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ),∃ w : ℂ,
      (F.method ε).characteristic (ε^2) (1-(ε:ℂ)*w)=0 ∧ ‖w-w₀‖<δ := by
  have hr := nesterov.Slow.eventually_exists_root_near F.scaledCharacteristic_degree
    F.scaledCharacteristic_tendsto F.limitCharacteristic_ne_zero hw₀ hδ
  filter_upwards [hr,F.affine_characteristic_eq] with ε hε hchar
  obtain ⟨w,hw,hd⟩ := hε
  exact ⟨w,by rw [hchar w,hw,mul_zero],hd⟩

/-- One slow flow root has real part exactly c_Q, in every damping regime. -/
theorem exists_slow_root : ∃ w : ℂ,F.limitCharacteristic.eval w=0 ∧ w.re=nesterov.Flow.cQ θ y := by
  obtain ⟨γ,_,hchar⟩ := nesterov.Flow.exists_quadratic_frequency F.theta_pos F.step_pos
  let s := nesterov.Flow.spiralExponent (nesterov.Flow.cQ θ y) γ
  refine ⟨-s,?_,?_⟩
  · change s^2+(θ:ℂ)*s+(y:ℂ)=0 at hchar
    simp only [limitCharacteristic,eval_add,eval_mul,eval_sub,eval_C,eval_X]
    push_cast
    field_simp [F.step_pos.ne']
    linear_combination hchar
  · simp [s,nesterov.Flow.spiralExponent]

/-- Quantified form of the quadratic ceiling; it also covers unstable fast modes. -/
theorem quadratic_coefficient_eventually_le {a : ℝ} (ha : nesterov.Flow.cQ θ y<a) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ),
      (1-nesterov.Rates.quadraticRate (F.method ε) (ε^2) 1)/ε≤a := by
  obtain ⟨w₀,hw₀,hre⟩ := F.exists_slow_root
  have hδ : 0<a-w₀.re := by rw [hre];linarith
  filter_upwards [F.actual_root_near hw₀ hδ,self_mem_nhdsWithin,
    (show ∀ᶠ ε in 𝓝[>] (0:ℝ),ε<1 from (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds)]
    with ε hε hpos hsmall
  change 0<ε at hpos
  obtain ⟨w,hroot,hd⟩ := hε
  have hμ : 0<ε^2 := sq_pos_of_pos hpos
  have hμL : ε^2<1 := by nlinarith
  have hr : ‖1-(ε:ℂ)*w‖≤nesterov.Rates.quadraticRate (F.method ε) (ε^2) 1 :=
    (nesterov.Rates.quadraticRate_isGreatest (F.method ε) hμ hμL).2
      ⟨ε^2,⟨le_rfl,hμL.le⟩,1-(ε:ℂ)*w,hroot,rfl⟩
  have hwre : w.re≤a := by
    have hh := Complex.re_le_norm (w-w₀)
    rw [Complex.sub_re] at hh
    linarith
  have hnorm : 1-ε*w.re≤‖1-(ε:ℂ)*w‖ := by
    simpa only [Complex.sub_re,Complex.one_re,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero] using Complex.re_le_norm (1-(ε:ℂ)*w)
  apply (div_le_iff₀ hpos).mpr
  nlinarith [mul_le_mul_of_nonneg_left hwre hpos.le]

end
end nesterov.Slow.SecondOrderFamily
