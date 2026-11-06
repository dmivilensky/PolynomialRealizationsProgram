import nesterov.Optimal.NearCorner
import nesterov.Layer.RationalScale
import nesterov.Layer.Resonance

/-! Deep unbounded corner dips give actual rational periodic divergence. -/
namespace nesterov.TwoStep.Scaling
noncomputable section
open Filter Set
open scoped Topology
variable {A : Type*} {l : Filter A} (F : Scaling A l 3 2 (1/2))

private theorem cornerN_defect_identity (a : A) {ξ : ℝ}
    (hd : 0<F.cornerDefect a) :
    F.cornerNAt a ξ=12-4*ξ-2*F.cornerDefect a*ξ+
      (F.stabilityMargin a+5+F.cornerDefect a-12)*ξ^2+
        (F.thetaAt a-3)*(4+2*ξ-4*ξ^2) := by
  have hpos : 0<4*F.cornerAlpha a-5 := by
    have hh : 0<max (4*F.cornerAlpha a-5) 0 := hd
    exact (lt_max_iff.mp hh).resolve_right (lt_irrefl 0)
  unfold cornerDefect cornerNAt
  rw [max_eq_left hpos.le]
  ring

private theorem denominator_rescaling {D d ξ : ℝ} (hd : d≠0) :
    (D-12)*ξ^2=(D/d^2)*(d*ξ)^2-12*ξ^2 := by
  field_simp

theorem corner_deep_dip_divergence
    (hd : Tendsto F.cornerDefect l atTop)
    (hdepth : Tendsto (fun a=>(F.stabilityMargin a+5+F.cornerDefect a)/F.cornerDefect a^2)
      l (𝓝 0))
    (hstable : ∀ᶠ a in l,(F.tuning a).Stable (F.epsilon a^2) 1) :
    ∀ᶠ a in l,∃ K : ℕ,ResonanceWitness (F.tuning a) (F.epsilon a^2) 1 K := by
  let σ : A→ℝ := fun a=>(F.cornerDefect a)⁻¹
  let K : A→ℕ := fun a=>Layer.rationalPeriod 12 (σ a)
  let ξ : A→ℝ := fun a=>Layer.rationalXi 12 (σ a)
  have hσ : Tendsto σ l (𝓝[>] (0:ℝ)) := tendsto_inv_atTop_nhdsGT_zero.comp hd
  have hξ : Tendsto ξ l (𝓝 0) := by
    have hangle := (Layer.rationalAngle_tendsto (by norm_num : (0:ℝ)<12)).comp hσ
    have hh := (tendsto_const_nhds (x:=(1:ℝ))).sub (Real.continuous_cos.tendsto 0 |>.comp hangle)
    simpa only [Real.cos_zero,sub_self,Layer.rationalXi,ξ,Function.comp_def] using hh
  have hscaled : Tendsto (fun a=>F.cornerDefect a*ξ a) l (𝓝 12) := by
    have hh := (Layer.rationalXi_scaled_tendsto (by norm_num : (0:ℝ)<12)).comp hσ
    simpa only [σ,ξ,Function.comp_def,div_inv_eq_mul,mul_comm] using hh
  have hθ : Tendsto (fun a=>F.thetaAt a-3) l (𝓝 0) := by
    simpa only [thetaAt,sub_self] using F.theta_tendsto.sub_const 3
  have hrem : Tendsto (fun a=>(F.thetaAt a-3)*(4+2*ξ a-4*ξ a^2)) l (𝓝 0) := by
    have hp : Tendsto (fun a=>4+2*ξ a-4*ξ a^2) l (𝓝 4) := by
      simpa using (tendsto_const_nhds.add (hξ.const_mul 2)).sub ((hξ.pow 2).const_mul 4)
    simpa using hθ.mul hp
  have hN : Tendsto (fun a=>F.cornerNAt a (ξ a)) l (𝓝 (-12)) := by
    have h := ((((tendsto_const_nhds (x:=(12:ℝ))).sub (hξ.const_mul 4)).sub (hscaled.const_mul 2)).add
      ((hdepth.mul (hscaled.pow 2)).sub ((hξ.pow 2).const_mul 12))).add hrem
    norm_num at h
    apply h.congr'
    filter_upwards [hd.eventually_gt_atTop 0] with a ha
    rw [F.cornerN_defect_identity a ha,denominator_rescaling ha.ne']
    ring
  have herr := F.near_tail_error_tendsto (c₀:=0) (c:=fun _=>0) tendsto_const_nhds hξ
  have hsum : Tendsto (fun a=>F.cornerNAt a (ξ a)+F.nearTailError 0 (ξ a) a) l (𝓝 (-12)) :=
    by simpa using hN.add herr
  have hnegative := hsum.eventually (eventually_lt_nhds (by norm_num : (-12:ℝ)<0))
  have hK := hσ.eventually (Layer.rationalPeriod_eventually_ge_three (by norm_num : (0:ℝ)<12))
  filter_upwards [hnegative,hK,F.near_tail_exact 0,F.beta_eq,F.epsilon_pos,hstable,
    F.epsilon_zero.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))]
    with a hneg hk hex hb he hs he1
  refine ⟨K a,resonanceWitness_of_negative (F.tuning a) (sq_pos_of_pos he)
    (by nlinarith : F.epsilon a^2<1) hs hk ?_⟩
  have ht : scaledTail (F.epsilon a) 0 (F.thetaAt a) (F.tuning a).stepSize
      (F.tuning a).tau (ξ a)<0 := by
    rw [hex]
    simpa only [mul_zero,zero_mul,sub_zero] using mul_neg_of_pos_of_neg he hneg
  rw [scaledTail_zero,←hb] at ht
  simpa only [K,ξ,Layer.rationalXi,Layer.rationalAngle,mul_one] using ht

end
end nesterov.TwoStep.Scaling
