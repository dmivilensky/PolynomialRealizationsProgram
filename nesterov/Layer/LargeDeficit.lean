import nesterov.Layer.Resonance

/-! Divergence for deficits tending to plus infinity. The tunings need not
have a bounded layer coordinate. -/
namespace nesterov.TwoStep.Scaling
noncomputable section
open Filter Set
open scoped Topology
variable {A : Type*} {l : Filter A} {θ y : ℝ} (F : Scaling A l θ y (1/2))

def layerGap (a : A) : ℝ := 1/2-(F.tuning a).tau

theorem layerGap_exact : ∀ᶠ a in l,
    F.layerGap a=F.layerDeficit a*Real.sqrt (F.epsilon a) := by
  filter_upwards [F.epsilon_pos] with a ha
  unfold layerGap layerDeficit
  exact (div_mul_cancel₀ _ (Real.sqrt_pos.mpr ha).ne').symm

theorem layerGap_tendstoGT (hA : Tendsto F.layerDeficit l atTop) :
    Tendsto F.layerGap l (𝓝[>] (0:ℝ)) := by
  have hg : Tendsto F.layerGap l (𝓝 0) := by
    change Tendsto (fun a=>1/2-(F.tuning a).tau) l (𝓝 0)
    simpa only [sub_self,layerGap] using
      (tendsto_const_nhds (x:=(1/2:ℝ))).sub F.tau_tendsto
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨hg,?_⟩
  filter_upwards [F.layerGap_exact,F.epsilon_pos,hA.eventually_gt_atTop 0] with a hg he ha
  rw [hg]
  exact mul_pos ha (Real.sqrt_pos.mpr he)

private theorem constant_gap_rescale {ε s d D p : ℝ}
    (hs : s^2=ε) (hd : d=D*s) (hsp : s≠0) (hD : D≠0) :
    p/d^2=(p/ε)*(D⁻¹)^2 := by
  rw [hd,←hs]
  field_simp

private theorem linear_gap_rescale {s d D p y e : ℝ}
    (hd : d=D*s) (hp : p/s= -4*y*D+s*e) (hsp : s≠0) (hD : D≠0) :
    p/d= -4*y+(s*e)*D⁻¹ := by
  rw [hd]
  have hm : p=(-4*y*D+s*e)*s := (div_eq_iff hsp).mp hp
  rw [hm]
  field_simp

private theorem polynomial_gap_rescale {d p₀ p₁ p₂ x : ℝ} (hd : d≠0) :
    (p₀+p₁*x+p₂*x^2)/d^2=p₀/d^2+(p₁/d)*(x/d)+p₂*(x/d)^2 := by
  field_simp

theorem P1_gap_tendsto (hA : Tendsto F.layerDeficit l atTop) :
    Tendsto (fun a=>scaledP1 (F.epsilon a) 0 (F.thetaAt a) (F.tuning a).stepSize
      (F.tuning a).tau/(F.layerGap a)^2) l (𝓝 0) := by
  have hi : Tendsto (fun a=>(F.layerDeficit a)⁻¹) l (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hA
  have ht := (F.P1_div_tendsto 0).mul (hi.pow 2)
  simp only [zero_pow (by omega : 2≠0),mul_zero] at ht
  apply ht.congr'
  filter_upwards [F.layerGap_exact,F.epsilon_pos,hA.eventually_gt_atTop 0] with a hg he ha
  exact (constant_gap_rescale (Real.sq_sqrt he.le) hg (Real.sqrt_pos.mpr he).ne' ha.ne').symm

theorem P2_gap_tendsto (hA : Tendsto F.layerDeficit l atTop) :
    Tendsto (fun a=>scaledP2 (F.epsilon a) 0 (F.thetaAt a) (F.tuning a).stepSize
      (F.tuning a).tau/F.layerGap a) l (𝓝 (-4*y)) := by
  have hi : Tendsto (fun a=>(F.layerDeficit a)⁻¹) l (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hA
  have ht := (F.step_tendsto.const_mul (-4)).add
    ((F.sqrt_epsilon_tendsto.mul (F.layerError_tendsto 0 1)).mul hi)
  simp only [zero_mul,mul_zero,add_zero] at ht
  apply ht.congr'
  filter_upwards [F.layerGap_exact,F.epsilon_pos,hA.eventually_gt_atTop 0,F.P2_layer_exact 0]
    with a hg he ha hp
  exact (linear_gap_rescale hg hp (Real.sqrt_pos.mpr he).ne' ha.ne').symm

/-- The unbounded positive-deficit branch has real periodic-from-rest
witnesses. Its periods have the exact inverse-square-root gap scale. -/
theorem layer_divergence_atTop (hy2 : y<2)
    (hA : Tendsto F.layerDeficit l atTop)
    (hstable : ∀ᶠ a in l,(F.tuning a).Stable (F.epsilon a^2) 1) :
    ∃ K : A→ℕ,
      Tendsto (fun a=>(K a:ℝ)*Real.sqrt (F.layerGap a)) l
        (𝓝 (Real.pi*Real.sqrt (2/(y/(2-y))))) ∧
      ∀ᶠ a in l,ResonanceWitness (F.tuning a) (F.epsilon a^2) 1 (K a) := by
  let φ : ℝ := y/(2-y)
  have hφ : 0<φ := div_pos F.step_pos (by linarith)
  let K : A→ℕ := fun a=>Layer.rationalPeriod φ (F.layerGap a)
  let ξ : A→ℝ := fun a=>Layer.rationalXi φ (F.layerGap a)
  have hx : Tendsto (fun a=>ξ a/F.layerGap a) l (𝓝 φ) :=
    (Layer.rationalXi_scaled_tendsto hφ).comp (F.layerGap_tendstoGT hA)
  have hp3 : Tendsto (fun a=>scaledP3 (F.epsilon a) 0 (F.thetaAt a)
      (F.tuning a).stepSize (F.tuning a).tau) l (𝓝 (2*(2-y))) := by
    have hv : 4*(1-(1/2)*y)=2*(2-y) := by ring
    simpa only [hv] using F.P3_tendsto 0
  have hp := ((F.P1_gap_tendsto hA).add ((F.P2_gap_tendsto hA).mul hx)).add
    (hp3.mul (hx.pow 2))
  have hv : 0+(-4*y)*φ+2*(2-y)*φ^2= -2*y^2/(2-y) := by
    dsimp [φ]
    field_simp [show 2-y≠0 by linarith]
    ring
  rw [hv] at hp
  have hneg : -2*y^2/(2-y)<0 := div_neg_of_neg_of_pos
    (by nlinarith [sq_pos_of_pos F.step_pos]) (by linarith)
  have hK := (F.layerGap_tendstoGT hA).eventually (Layer.rationalPeriod_eventually_ge_three hφ)
  refine ⟨K,(Layer.rationalPeriod_scaled_tendsto hφ).comp (F.layerGap_tendstoGT hA),?_⟩
  filter_upwards [hp.eventually (eventually_lt_nhds hneg),hK,F.epsilon_pos,F.beta_eq,
    F.epsilon_zero.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1)),hstable,
    (F.layerGap_tendstoGT hA).eventually self_mem_nhdsWithin]
    with a hn hK he hb he1 hs hgap
  apply resonanceWitness_of_negative (F.tuning a) (sq_pos_of_pos he) (by nlinarith) hs hK
  have hpoly : scaledTail (F.epsilon a) 0 (F.thetaAt a) (F.tuning a).stepSize
      (F.tuning a).tau (ξ a)/(F.layerGap a)^2<0 := by
    rw [scaledTail,polynomial_gap_rescale (show F.layerGap a≠0 from hgap.ne')]
    exact hn
  have hneg' := (div_lt_iff₀ (sq_pos_of_pos hgap)).mp hpoly
  simp only [zero_mul] at hneg'
  rw [scaledTail_zero] at hneg'
  simpa only [K,ξ,φ,Layer.rationalXi,Layer.rationalAngle,mul_one,hb] using hneg'

end
end nesterov.TwoStep.Scaling
