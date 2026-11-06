import nesterov.Faithful.Low
import nesterov.Faithful.FamilySmooth
import nesterov.Slow.Factorization
import nesterov.Flow.Constants

/-! Article Lemma D.2: the genuine joint two-scale expansion on r=1-cε.
The expansion itself only uses continuity; C³ gives the stated regularity. -/
namespace nesterov.Faithful
noncomputable section
open Polynomial Filter Set Asymptotics
open scoped Topology
variable {θ y : ℝ} (F : Slow.SecondOrderFamily θ y)

def linearCircle (c ε ω : ℝ) : ℂ := ((1-c*ε:ℝ):ℂ)*circle ω

def linearSymbol (c ε ω : ℝ) : ℝ :=
  (((1-linearCircle c ε ω)*(F.method ε).characteristic (ε^2) (linearCircle c ε ω))*
    star ((F.method ε).characteristic 1 (linearCircle c ε ω))).re

private theorem product_error_littleO {A : Type*} {l : Filter A}
    {a b q a₀ b₀ q₀ t : A→ℂ}
    (ha : (fun x=>a x-a₀ x)=o[l] t) (hb : (fun x=>b x-b₀ x)=o[l] t)
    (hq : (fun x=>q x-q₀ x)=o[l] (fun _=>(1:ℂ)))
    (ha₀ : a₀=O[l] t) (hb₀ : b₀=O[l] t) (hb' : b=O[l] t)
    (hq' : q=O[l] (fun _=>(1:ℂ))) :
    (fun x=>a x*b x*q x-a₀ x*b₀ x*q₀ x)=o[l] (fun x=>t x^2) := by
  have h₁ := (ha.mul_isBigO hb').mul_isBigO hq'
  have h₂ := (ha₀.mul_isLittleO hb).mul_isBigO hq'
  have h₃ := (ha₀.mul hb₀).mul_isLittleO hq
  have h₁' : (fun x=>(a x-a₀ x)*b x*q x)=o[l] (fun x=>t x^2) :=
    h₁.congr_right (fun x=>by ring)
  have h₂' : (fun x=>a₀ x*(b x-b₀ x)*q x)=o[l] (fun x=>t x^2) :=
    h₂.congr_right (fun x=>by ring)
  have h₃' : (fun x=>a₀ x*b₀ x*(q x-q₀ x))=o[l] (fun x=>t x^2) :=
    h₃.congr_right (fun x=>by ring)
  exact ((h₁'.add h₂').add h₃').congr_left (fun x=>by ring)

/-- The full joint expansion, along every filter approaching ε=0+ and ω=0.
In particular there is no restriction on the ratio ω/ε. -/
theorem two_scale_expansion {A : Type*} {l : Filter A} {ε ω : A→ℝ}
    (he : Tendsto ε l (𝓝[>] (0:ℝ))) (hω : Tendsto ω l (𝓝 0)) (c : ℝ) :
    (fun x=>linearSymbol F c (ε x) (ω x)-
      ε x/y*(c*Flow.delta θ y c*(ε x)^2+(θ-3*c)*(ω x)^2))=o[l]
      (fun x=>(ε x+|ω x|)^3) := by
  let e : A→ℂ := fun x=>(ε x:ℂ)
  let o : A→ℂ := fun x=>(ω x:ℂ)
  let t : A→ℂ := fun x=>((ε x+|ω x|:ℝ):ℂ)
  let z : A→ℂ := fun x=>linearCircle c (ε x) (ω x)
  let a : A→ℂ := fun x=>z x-1
  let a₀ : A→ℂ := fun x=> -(c:ℂ)*e x+Complex.I*o x
  let b : A→ℂ := fun x=>z x-(F.beta (ε x):ℂ)
  let b₀ : A→ℂ := fun x=>((θ-c:ℝ):ℂ)*e x+Complex.I*o x
  let q : A→ℂ := fun x=>(F.quotient (ε x)).eval₂ Complex.ofRealHom (z x)
  let u : A→ℂ := fun x=>(F.u (ε x)).eval₂ Complex.ofRealHom (z x)
  let v : A→ℂ := fun x=>(F.v (ε x)).eval₂ Complex.ofRealHom (z x)
  let q₀ : ℂ := ((-1/y:ℝ):ℂ)
  have he0 := he.mono_right nhdsWithin_le_nhds
  have heC : Tendsto e l (𝓝 0) := he0.ofReal
  have hoC : Tendsto o l (𝓝 0) := hω.ofReal
  have ht : Tendsto t l (𝓝 0) := by
    simpa only [abs_zero,zero_add,Complex.ofReal_zero,t] using (he0.add hω.abs).ofReal
  have heO : e=O[l] t := by
    apply IsBigO.of_bound 1
    filter_upwards [he.eventually self_mem_nhdsWithin] with x hx
    change 0<ε x at hx
    simp only [e,t,Complex.norm_real,Real.norm_eq_abs,one_mul,abs_of_pos hx,
      abs_of_pos (add_pos_of_pos_of_nonneg hx (abs_nonneg _))]
    linarith [abs_nonneg (ω x)]
  have hoO : o=O[l] t := by
    apply IsBigO.of_bound 1
    filter_upwards [he.eventually self_mem_nhdsWithin] with x hx
    change 0<ε x at hx
    simp only [o,t,Complex.norm_real,Real.norm_eq_abs,one_mul,
      abs_of_pos (add_pos_of_pos_of_nonneg hx (abs_nonneg _))]
    linarith
  obtain ⟨E,hEa,hE0,_,hE⟩ := exists_circle_increment
  have hEc : Tendsto (fun x=>E (ω x)) l (𝓝 Complex.I) := by
    simpa only [hE0,Function.comp_def] using hEa.continuousAt.tendsto.comp hω
  have hcircle : Tendsto (fun x=>circle (ω x)) l (𝓝 1) := by
    simpa only [circle_zero,Function.comp_def] using (analyticAt_circle 0).continuousAt.tendsto.comp hω
  have hz : Tendsto z l (𝓝 1) := by
    have h1 : Tendsto (fun _ : A=>(1:ℂ)) l (𝓝 1) := tendsto_const_nhds
    have hh := (h1.sub (heC.const_mul (c:ℂ))).mul hcircle
    simpa only [mul_zero,sub_zero,one_mul,z,linearCircle,Complex.ofReal_sub,Complex.ofReal_one,
      Complex.ofReal_mul,e] using hh
  have hcirO : (fun x=>circle (ω x)-1)=O[l] t := by
    have hh := hoO.mul (hEc.isBigO_one ℂ)
    exact (hh.congr_right (fun x=>mul_one _)).congr_left (fun x=>by exact (hE (ω x)).symm)
  have hEerr : (fun x=>E (ω x)-Complex.I)=o[l] (fun _=>(1:ℂ)) :=
    (isLittleO_one_iff ℂ).mpr (by simpa only [sub_self] using hEc.sub_const Complex.I)
  have htt : (fun x=>t x*t x)=o[l] t := by
    simpa only [Function.comp_def,pow_two,pow_one] using
      ((isLittleO_pow_pow (by norm_num : 1<2)).comp_tendsto ht)
  have hrem1 := ((heO.const_mul_left (-(c:ℂ))).mul hcirO).trans_isLittleO htt
  have hrem2 := hoO.mul_isLittleO hEerr
  have ha : (fun x=>a x-a₀ x)=o[l] t := by
    have h₁ : (fun x=> -(c:ℂ)*e x*(circle (ω x)-1))=o[l] t :=
      hrem1
    have h₂ : (fun x=>o x*(E (ω x)-Complex.I))=o[l] t :=
      hrem2.congr_right (fun x=>mul_one _)
    apply (h₁.add h₂).congr_left
    intro x
    dsimp [a,a₀,z,linearCircle,e,o]
    push_cast
    have hh := hE (ω x)
    linear_combination -hh
  have ha₀ : a₀=O[l] t := (heO.const_mul_left (-(c:ℂ))).add (hoO.const_mul_left Complex.I)
  have hb₀ : b₀=O[l] t := (heO.const_mul_left ((θ-c:ℝ):ℂ)).add (hoO.const_mul_left Complex.I)
  have hθ := (F.thetaAt_tendsto.comp he).ofReal
  have hβ : (fun x=>1-(F.beta (ε x):ℂ)-(θ:ℂ)*e x)=o[l] t := by
    have hh := heO.mul_isLittleO ((isLittleO_one_iff ℂ).mpr
      (by simpa only [sub_self] using hθ.sub_const (θ:ℂ)))
    apply (hh.congr_right (fun x=>mul_one _)).congr' ?_ (Eventually.of_forall (fun _=>rfl))
    filter_upwards [he.eventually self_mem_nhdsWithin] with x hx
    have hn := ne_of_gt hx
    dsimp [e,Slow.SecondOrderFamily.thetaAt]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hn]
  have hb : (fun x=>b x-b₀ x)=o[l] t := by
    apply (ha.add hβ).congr_left
    intro x
    dsimp [a,a₀,b,b₀]
    push_cast
    ring
  have hb' : b=O[l] t := (hb.isBigO.add hb₀).congr_left (fun x=>by ring)
  have hq := Slow.tendsto_eval₂_of_coeff (N:=F.memory+1)
    (fun j=>(F.quotient_coeff_tendsto j).comp he)
    (fun x=>lt_of_le_of_lt (F.quotient_natDegree_le (ε x)) (Nat.lt_succ_self _))
    (by rw [←F.quotient_zero];exact lt_of_le_of_lt (F.quotient_natDegree_le 0) (Nat.lt_succ_self _)) hz
  have hqval : F.q0.eval₂ Complex.ofRealHom 1=q₀ := by
    have hc (a : ℝ) : Complex.ofRealHom a=(a:ℂ) := rfl
    simpa only [map_one,F.q0_one,q₀,hc,Complex.ofReal_one] using eval₂_at_apply (p:=F.q0) Complex.ofRealHom (1:ℝ)
  rw [hqval] at hq
  have hu := Slow.tendsto_eval₂_of_coeff (fun j=>(F.u_coeff_tendsto j).comp he)
    (fun x=>F.u_natDegree_lt (ε x)) (F.u_natDegree_lt 0) hz
  have huval : (F.u 0).eval₂ Complex.ofRealHom 1=1 := by
    simpa only [map_one,F.u_one] using eval₂_at_apply (p:=F.u 0) Complex.ofRealHom (1:ℝ)
  rw [huval] at hu
  have hv := Slow.tendsto_eval₂_of_coeff (N:=F.memory+1) (fun j=>(F.v_coeff_tendsto j).comp he)
    (fun x=>by rw [F.v_natDegree];omega) (by rw [F.v_natDegree];omega) hz
  have hvval : (F.v 0).eval₂ Complex.ofRealHom 1=0 := by
    simpa only [map_one,F.v_one,map_zero] using eval₂_at_apply (p:=F.v 0) Complex.ofRealHom (1:ℝ)
  rw [hvval] at hv
  have hqerr : (fun x=>q x-q₀)=o[l] (fun _=>(1:ℂ)) :=
    (isLittleO_one_iff ℂ).mpr (by simpa only [sub_self] using hq.sub_const q₀)
  have hve := product_error_littleO ha hb hqerr ha₀ hb₀ hb' (hq.isBigO_one ℂ)
  have hvErr : (fun x=>v x-a₀ x*b₀ x*q₀)=o[l] (fun x=>t x^2) := by
    apply hve.congr' ?_ (Eventually.of_forall (fun _=>rfl))
    filter_upwards [he.eventually F.factorization] with x hx
    dsimp [v,q,a,b]
    rw [hx]
    simp only [eval₂_mul,eval₂_sub,eval₂_X,eval₂_C]
    rfl
  let P : A→ℂ := fun x=>e x^2*u x-v x
  let P₀ : A→ℂ := fun x=>e x^2-a₀ x*b₀ x*q₀
  have he2 := heO.pow 2
  have hlead : (fun x=>a₀ x*b₀ x*q₀)=O[l] (fun x=>t x^2) :=
    ((ha₀.mul hb₀).mul ((tendsto_const_nhds : Tendsto (fun _ : A=>q₀) l (𝓝 q₀)).isBigO_one ℂ)).congr_right (fun x=>by ring)
  have hP₀ : P₀=O[l] (fun x=>t x^2) := he2.sub hlead
  have hPerr : (fun x=>P x-P₀ x)=o[l] (fun x=>t x^2) := by
    have huerr : (fun x=>u x-1)=o[l] (fun _=>(1:ℂ)) :=
      (isLittleO_one_iff ℂ).mpr (by simpa only [sub_self] using hu.sub_const 1)
    have hh := he2.mul_isLittleO huerr
    have hh' : (fun x=>e x^2*(u x-1))=o[l] (fun x=>t x^2) :=
      hh.congr_right (fun x=>mul_one _)
    exact (hh'.sub hvErr).congr_left (fun x=>by dsimp [P,P₀];ring)
  have hP : P=O[l] (fun x=>t x^2) := (hPerr.isBigO.add hP₀).congr_left (fun x=>by ring)
  have hlast : Tendsto (fun x=>star (u x-v x)) l (𝓝 1) := by
    simpa only [sub_zero,star_one] using (hu.sub hv).star
  have hlastErr : (fun x=>star (u x-v x)-1)=o[l] (fun _=>(1:ℂ)) :=
    (isLittleO_one_iff ℂ).mpr (by simpa only [sub_self] using hlast.sub_const 1)
  have h₁ := ((ha.neg_left).mul_isBigO hP).mul_isBigO (hlast.isBigO_one ℂ)
  have h₂ := ((ha₀.neg_left).mul_isLittleO hPerr).mul_isBigO (hlast.isBigO_one ℂ)
  have h₃ := ((ha₀.neg_left).mul hP₀).mul_isLittleO hlastErr
  have h₁' : (fun x=> -(a x-a₀ x)*P x*star (u x-v x))=o[l] (fun x=>t x^3) :=
    h₁.congr_right (fun x=>by ring)
  have h₂' : (fun x=> -a₀ x*(P x-P₀ x)*star (u x-v x))=o[l] (fun x=>t x^3) :=
    h₂.congr_right (fun x=>by ring)
  have h₃' : (fun x=> -a₀ x*P₀ x*(star (u x-v x)-1))=o[l] (fun x=>t x^3) :=
    h₃.congr_right (fun x=>by ring)
  have hall : (fun x=> -a x*P x*star (u x-v x)-(-a₀ x*P₀ x))=o[l] (fun x=>t x^3) :=
    ((h₁'.add h₂').add h₃').congr_left (fun x=>by ring)
  have hre := (isBigO_of_le (f:=fun x=>(-a x*P x*star (u x-v x)-(-a₀ x*P₀ x)).re) l
    (fun x=>by simpa only [Real.norm_eq_abs] using (Complex.abs_re_le_norm
      (-a x*P x*star (u x-v x)-(-a₀ x*P₀ x))))).trans_isLittleO hall
  have hren := hre.norm_right
  apply hren.congr'
  · filter_upwards [he.eventually self_mem_nhdsWithin] with x hx
    have hy := F.step_pos.ne'
    change ((-a x*P x*star (u x-v x)-(-a₀ x*P₀ x)).re)=_
    have hact : (-a x*P x*star (u x-v x)).re=linearSymbol F c (ε x) (ω x) := by
      dsimp [linearSymbol,P,a,z,u,v,e]
      simp only [StationaryMethod.characteristic_eq_polynomial_eval,eval_sub,eval_mul,eval_C,eval_map,
        Complex.ofReal_one,one_mul,Complex.ofReal_pow]
      congr 1
      rw [show 1-linearCircle c (ε x) (ω x)= -(linearCircle c (ε x) (ω x)-1) by ring]
      rw [show (F.v (ε x)).eval₂ Complex.ofRealHom (linearCircle c (ε x) (ω x))-
          (ε x:ℂ)^2*(F.u (ε x)).eval₂ Complex.ofRealHom (linearCircle c (ε x) (ω x))=
          -((ε x:ℂ)^2*(F.u (ε x)).eval₂ Complex.ofRealHom (linearCircle c (ε x) (ω x))-
            (F.v (ε x)).eval₂ Complex.ofRealHom (linearCircle c (ε x) (ω x))) by ring,
        show (F.v (ε x)).eval₂ Complex.ofRealHom (linearCircle c (ε x) (ω x))-
          (F.u (ε x)).eval₂ Complex.ofRealHom (linearCircle c (ε x) (ω x))=
          -((F.u (ε x)).eval₂ Complex.ofRealHom (linearCircle c (ε x) (ω x))-
            (F.v (ε x)).eval₂ Complex.ofRealHom (linearCircle c (ε x) (ω x))) by ring,
        map_neg]
      ring
    rw [Complex.sub_re,hact]
    congr 1
    dsimp [a₀,b₀,P₀,q₀,e,o,Flow.delta]
    simp only [pow_two,Complex.mul_re,Complex.mul_im,Complex.sub_re,Complex.sub_im,Complex.add_re,Complex.add_im,
      Complex.neg_re,Complex.neg_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im]
    field_simp [hy]
    ring
  · filter_upwards [he.eventually self_mem_nhdsWithin] with x hx
    change ‖((ε x+|ω x|:ℝ):ℂ)^3‖=(ε x+|ω x|)^3
    rw [norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (add_pos_of_pos_of_nonneg hx (abs_nonneg _))]

end
end nesterov.Faithful
