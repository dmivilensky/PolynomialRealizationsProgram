import nesterov.Slow.EvalControl

/-!
Article: Lemma D.1, the uniform cubic normal-form remainder.
The theorem is stated for any filter with bounded slow modes. In particular,
its product-filter specialization is uniform on every compact frequency set.
-/
namespace nesterov.Slow
noncomputable section
open Polynomial Filter Set Asymptotics
open scoped Topology

lemma triple_product_error {A : Type*} {l : Filter A} {a b q a₀ b₀ q₀ e : A→ℂ}
    (ha : (fun x=>a x-a₀ x) =O[l] (fun x=>e x^2))
    (hb : (fun x=>b x-b₀ x) =O[l] (fun x=>e x^2))
    (hq : (fun x=>q x-q₀ x) =O[l] e)
    (ha₀ : a₀ =O[l] e) (hb₀ : b₀ =O[l] e) (hb' : b =O[l] e)
    (hq' : q =O[l] (fun _=>(1:ℂ))) :
    (fun x=>a x*b x*q x-a₀ x*b₀ x*q₀ x) =O[l] (fun x=>e x^3) := by
  have h₁ := (ha.mul hb').mul hq'
  have h₂ := (ha₀.mul hb).mul hq'
  have h₃ := (ha₀.mul hb₀).mul hq
  have h₁' : (fun x=>(a x-a₀ x)*b x*q x) =O[l] (fun x=>e x^3) :=
    h₁.congr_right (fun x=>by ring)
  have h₂' : (fun x=>a₀ x*(b x-b₀ x)*q x) =O[l] (fun x=>e x^3) :=
    h₂.congr_right (fun x=>by ring)
  have h₃' : (fun x=>a₀ x*b₀ x*(q x-q₀ x)) =O[l] (fun x=>e x^3) :=
    h₃.congr_right (fun x=>by ring)
  exact ((h₁'.add h₂').add h₃').congr_left (fun x=>by ring)

namespace SecondOrderFamily
variable {θ y : ℝ} (F : SecondOrderFamily θ y)

/-- Actual curvature equals the flow quadratic plus a uniform O(ε³) error;
θ_ε and y_ε are the actual factors of the family, not their limiting values. -/
theorem normal_form_bounded {A : Type*} {l : Filter A} {ε : A→ℝ} {w : A→ℂ}
    (hε : Tendsto ε l (𝓝[>] (0:ℝ))) (hw : w =O[l] (fun _=>(1:ℂ))) :
    (fun x=>F.curvature (ε x) (F.wave (ε x) (w x))-
      ((ε x:ℂ)^2/(F.stepAt (ε x):ℂ))*w x*((F.thetaAt (ε x):ℂ)-w x)) =O[l]
      (fun x=>(ε x:ℂ)^3) := by
  let e : A→ℂ := fun x=>(ε x:ℂ)
  let z : A→ℂ := fun x=>F.wave (ε x) (w x)
  let a₀ : A→ℂ := fun x=> -e x*w x
  let b₀ : A→ℂ := fun x=>e x*((F.thetaAt (ε x):ℂ)-w x)
  let a : A→ℂ := fun x=>z x-1
  let b : A→ℂ := fun x=>a x+e x*(F.thetaAt (ε x):ℂ)
  let q : A→ℂ := fun x=>(F.quotient (ε x)).eval₂ Complex.ofRealHom (z x)
  let q₀ : A→ℂ := fun x=>(((F.quotient (ε x)).eval (1:ℝ):ℝ):ℂ)
  let u : A→ℂ := fun x=>(F.u (ε x)).eval₂ Complex.ofRealHom (z x)
  let lead : A→ℂ := fun x=>a₀ x*b₀ x*q₀ x
  have he : Tendsto e l (𝓝 0) := by
    convert (Complex.continuous_ofReal.tendsto _).comp (hε.mono_right nhdsWithin_le_nhds) using 1
    funext x
    rfl
  have hθ : Tendsto (fun x=>(F.thetaAt (ε x):ℂ)) l (𝓝 (θ:ℂ)) := by
    convert (Complex.continuous_ofReal.tendsto _).comp (F.thetaAt_tendsto.comp hε) using 1
    funext x
    rfl
  have harg : a₀ =O[l] e := by
    simpa only [a₀,mul_one] using (isBigO_refl e l).neg_left.mul hw
  have harg0 : Tendsto a₀ l (𝓝 0) := harg.trans_tendsto he
  have hz : Tendsto z l (𝓝 1) := by
    simpa only [z,wave,Complex.exp_zero] using harg0.cexp
  have hE : Tendsto (fun x=>expIncrement (a₀ x)) l (𝓝 1) := by
    simpa only [Function.comp_def,expIncrement_zero] using expIncrement_continuousAt.tendsto.comp harg0
  have ha : a =O[l] e := by
    have hh := harg.mul (hE.isBigO_one ℂ)
    apply (hh.congr_right (fun x=>mul_one _)).congr_left
    intro x
    exact (expIncrement_mul (a₀ x)).trans (by rfl)
  have hb₀ : b₀ =O[l] e := by
    simpa only [b₀,mul_one] using (isBigO_refl e l).mul ((hθ.isBigO_one ℂ).sub hw)
  have hb : b =O[l] e := by
    have hh : (fun x=>e x*(F.thetaAt (ε x):ℂ)) =O[l] e := by
      simpa only [mul_one] using (isBigO_refl e l).mul (hθ.isBigO_one ℂ)
    exact ha.add hh
  have hrem : (fun x=>a x-a₀ x) =O[l] (fun x=>e x^2) := by
    exact (exp_linear_remainder_isBigO he hw).congr_left (fun x=>by dsimp [z,wave,a,a₀];ring)
  have hremB : (fun x=>b x-b₀ x) =O[l] (fun x=>e x^2) :=
    hrem.congr_left (fun x=>by dsimp [b,b₀,a₀];ring)
  have hq := tendsto_eval₂_of_coeff (N:=F.memory+1)
    (fun j=>(F.quotient_coeff_tendsto j).comp hε)
    (fun x=>lt_of_le_of_lt (F.quotient_natDegree_le (ε x)) (Nat.lt_succ_self _))
    (by rw [←F.quotient_zero];exact lt_of_le_of_lt (F.quotient_natDegree_le 0) (Nat.lt_succ_self _)) hz
  have hu := tendsto_eval₂_of_coeff (fun j=>(F.u_coeff_tendsto j).comp hε)
    (fun x=>F.u_natDegree_lt (ε x)) (F.u_natDegree_lt 0) hz
  have hu1 : (F.u 0).eval₂ Complex.ofRealHom 1=1 := by
    simpa only [map_one,F.u_one] using eval₂_at_apply (p:=F.u 0) Complex.ofRealHom (1:ℝ)
  rw [hu1] at hu
  have hqdiff : (fun x=>q x-q₀ x) =O[l] e := by
    exact (eval_sub_eval_one_isBigO (fun j=>(F.quotient_coeff_tendsto j).comp hε)
      (fun x=>F.quotient_natDegree_le (ε x)) (by rw [←F.quotient_zero];exact F.quotient_natDegree_le 0) hz).trans ha
  have hudiff : (fun x=>u x-1) =O[l] e := by
    have hh := (eval_sub_eval_one_isBigO (fun j=>(F.u_coeff_tendsto j).comp hε)
      (fun x=>(F.u_natDegree_lt (ε x)).le) (F.u_natDegree_lt 0).le hz).trans ha
    simpa only [F.u_one,Complex.ofReal_one] using hh
  have hq₀ := F.quotient_eval_tendsto (z:=fun _=>(1:ℂ)) tendsto_const_nhds
  have hq₀' : Tendsto q₀ l (𝓝 (F.q0.eval₂ Complex.ofRealHom 1)) := by
    have hh := hq₀.comp hε
    convert hh using 1
    funext x
    exact (eval₂_at_apply (p:=F.quotient (ε x)) Complex.ofRealHom (1:ℝ)).symm
  have hlead : lead =O[l] (fun x=>e x^2) := by
    simpa only [lead,mul_one,pow_two] using (harg.mul hb₀).mul (hq₀'.isBigO_one ℂ)
  have hp := triple_product_error hrem hremB hqdiff harg hb₀ hb (hq.isBigO_one ℂ)
  have hinv : (fun x=>(u x)⁻¹) =O[l] (fun _=>(1:ℂ)) :=
    (hu.inv₀ (by norm_num : (1:ℂ)≠0)).isBigO_one ℂ
  have hsmall : (fun x=>(1-u x)*(u x)⁻¹) =O[l] e := by
    simpa only [mul_one] using hudiff.neg_left.mul hinv |>.congr_left (fun x=>by ring)
  have h₁ := hp.mul hinv
  have h₂ := hlead.mul hsmall
  have h₁' : (fun x=>(a x*b x*q x-lead x)*(u x)⁻¹) =O[l] (fun x=>e x^3) := by
    simpa only [lead,mul_one] using h₁
  have h₂' : (fun x=>lead x*((1-u x)*(u x)⁻¹)) =O[l] (fun x=>e x^3) :=
    h₂.congr_right (fun x=>by ring)
  have htotal := h₁'.add h₂'
  apply htotal.congr' _ (Eventually.of_forall (fun _=>rfl))
  filter_upwards [hε.eventually F.factorization,hu.eventually_ne (by norm_num : (1:ℂ)≠0),
    hε.eventually self_mem_nhdsWithin] with x hfac hU hpos
  have hc (r : ℝ) : Complex.ofRealHom r=(r:ℂ) := rfl
  have he0 : e x≠0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hpos)
  have hθeq : e x*(F.thetaAt (ε x):ℂ)=1-(F.beta (ε x):ℂ) := by
    have hr : ε x*F.thetaAt (ε x)=1-F.beta (ε x) := by
      dsimp [thetaAt]
      field_simp [ne_of_gt hpos]
    dsimp only [e]
    exact_mod_cast hr
  have hleadEq : lead x=e x^2/(F.stepAt (ε x):ℂ)*w x*((F.thetaAt (ε x):ℂ)-w x) := by
    dsimp [lead,a₀,b₀,q₀,stepAt]
    push_cast
    by_cases hqzero : (F.quotient (ε x)).eval (1:ℝ)=0
    · simp [hqzero]
    · field_simp
  rw [←hleadEq]
  unfold curvature
  rw [hfac]
  simp only [eval₂_mul,eval₂_sub,eval₂_X,eval₂_C,hc,Complex.ofReal_one]
  change (a x*b x*q x-lead x)*(u x)⁻¹+lead x*((1-u x)*(u x)⁻¹)=
    (z x-1)*(z x-(F.beta (ε x):ℂ))*q x/u x-lead x
  have hbeq : z x-(F.beta (ε x):ℂ)=b x := by dsimp [b,a];rw [hθeq];ring
  rw [hbeq]
  change (a x*b x*q x-lead x)*(u x)⁻¹+lead x*((1-u x)*(u x)⁻¹)=
    a x*b x*q x/u x-lead x
  have hU' : u x≠0 := hU
  field_simp [hU']
  ring


/-- The source uniform O(ε³) statement on an arbitrary compact slow-mode set. -/
theorem normal_form_uniform {K : Set ℂ} (hK : IsCompact K) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ ε in 𝓝[>] (0:ℝ),∀ w∈K,
      ‖F.curvature ε (F.wave ε w)-(ε:ℂ)^2/(F.stepAt ε:ℂ)*w*((F.thetaAt ε:ℂ)-w)‖≤C*ε^3 := by
  let l : Filter (ℝ × ℂ) := (𝓝[>] (0:ℝ)) ×ˢ 𝓟 K
  have he : Tendsto (Prod.fst : ℝ × ℂ→ℝ) l (𝓝[>] (0:ℝ)) := tendsto_fst
  have hmem : ∀ᶠ p : ℝ × ℂ in l,p.2∈K :=
    tendsto_snd.eventually (show ∀ᶠ w in 𝓟 K,w∈K by simp)
  obtain ⟨R,hR⟩ := hK.isBounded.exists_norm_le
  have hw : (Prod.snd : ℝ × ℂ→ℂ) =O[l] (fun _=>(1:ℂ)) := by
    apply IsBigO.of_bound R
    filter_upwards [hmem] with p hp
    simpa using hR p.2 hp
  obtain ⟨C,hC,hbound⟩ := (F.normal_form_bounded he hw).exists_nonneg
  refine ⟨C,hC,?_⟩
  have hh : ∀ᶠ ε in 𝓝[>] (0:ℝ),∀ w∈K,
      ‖F.curvature ε (F.wave ε w)-(ε:ℂ)^2/(F.stepAt ε:ℂ)*w*((F.thetaAt ε:ℂ)-w)‖≤C*‖(ε:ℂ)^3‖ :=
    eventually_prod_principal_iff.mp hbound.bound
  filter_upwards [hh,self_mem_nhdsWithin] with ε hε hp w hw
  change 0<ε at hp
  simpa only [norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp] using hε w hw

end SecondOrderFamily
end
end nesterov.Slow
