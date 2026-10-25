import polyak.Global.Threshold.Parameters
import polyak.Levels.Threshold.KappaDerivative

/-! Uniform frequency control near condition number one. The exact inverse
formula reduces the whole compact cosine interval to one positive minimum;
there is no asymptotic or unproved endpoint premise. -/
noncomputable section
namespace polyak.Global.Threshold
open General Levels Set Filter
open scoped Topology

theorem exists_uniform_Xi_bound (p : ParameterStrip) (R : ℝ) :
    ∃δ : ℝ,0<δ ∧ ∀κ : ConditionNumber,κ.val<1+δ→
      ∀c∈Icc (-1:ℝ) 1,(tuning p κ).Xi c< -R := by
  let q:=tuning p ⟨2,by norm_num⟩
  let N : ℝ→ℝ:=fun c=>kappaNumerator q.y q.beta c/(q.y*(1-q.beta))
  have hNcont : Continuous N := by unfold N kappaNumerator; fun_prop
  have hNpos : ∀c∈Icc (-1:ℝ) 1,0<N c := fun c hc=>div_pos (kappaNumerator_pos q hc)
    (mul_pos q.y_pos (sub_pos.mpr q.beta_lt_one))
  obtain ⟨cmin,hcmin,hmin⟩:=isCompact_Icc.exists_isMinOn (by norm_num : (Icc (-1:ℝ) 1).Nonempty) hNcont.continuousOn
  have hXicont : Continuous (fun c=>XiAtKappa q 2 c) := by unfold XiAtKappa; fun_prop
  obtain ⟨cmax,hcmax,hmax⟩:=isCompact_Icc.exists_isMaxOn (by norm_num : (Icc (-1:ℝ) 1).Nonempty) hXicont.continuousOn
  let m:=N cmin
  let H:=XiAtKappa q 2 cmax
  let C:=|H|+|R|+m+1
  have hm : 0<m:=hNpos cmin hcmin
  have hC : 0<C:=by dsimp [C]; positivity
  let δ:=min (1/2:ℝ) (m/C)
  have hδ : 0<δ:=lt_min (by norm_num) (div_pos hm hC)
  refine ⟨δ,hδ,fun κ hκ c hc=>?_⟩
  have ht : 0<κ.val-1:=sub_pos.mpr κ.property
  have htd : κ.val-1<δ:=by linarith
  have ht1 : κ.val-1<1:=by have hh:=min_le_left (1/2:ℝ) (m/C); change δ≤1/2 at hh; linarith
  have hu : 1-(κ.val-1)⁻¹<0:=by
    have hh : 1<(κ.val-1)⁻¹ := (one_lt_inv₀ ht).mpr ht1
    linarith
  have hcoef : m≤N c:=hmin hc
  have hupper : XiAtKappa q 2 c≤H:=hmax hc
  have hscaled:=mul_le_mul_of_nonpos_right hcoef hu.le
  have htC : κ.val-1<m/C:=htd.trans_le (min_le_right _ _)
  have hmul : C*(κ.val-1)<m:=by nlinarith [(lt_div_iff₀ hC).mp htC]
  have hratio : C<m/(κ.val-1):=(lt_div_iff₀ ht).mpr hmul
  have hrough : H+m+R<C:=by dsimp [C]; linarith [le_abs_self H,le_abs_self R]
  have he : (tuning p κ).Xi c=XiAtKappa q 2 c+N c*(1-(κ.val-1)⁻¹) :=
    XiAtKappa_inverse_form q κ.property c
  have hid : m*(κ.val-1)⁻¹=m/(κ.val-1):=by rw [div_eq_mul_inv]
  rw [he]
  nlinarith [hscaled,hupper,hratio,hrough]

theorem shifted_infeasible_of_negative_profile (q : Tuning) (s : ℝ)
    (hneg : ∀ω∈Ioo (0:ℝ) Real.pi,Geometry.cotangent q ω+s<0) :
    ¬FP (Geometry.shiftedCurve q s) := by
  apply Levels.Threshold.fpOn_impossible_of_negative_minimizer
  intro ω
  rcases eq_or_lt_of_le ω.property.1 with h0|h0
  · have he : ω=frequencyZero:=Subtype.ext h0.symm
    rw [he,Curve.minimizer_at_zero]
    norm_num
  rcases eq_or_lt_of_le ω.property.2 with hp|hp
  · have he : ω=frequencyPi:=Subtype.ext hp
    rw [he,Curve.minimizer_at_pi]
    norm_num
  have he:=Geometry.cot_shiftedAngle q s ⟨h0,hp⟩
  have hmem:=Geometry.shiftedAngle_mem q s ⟨h0,hp⟩
  have hs:=Real.sin_pos_of_pos_of_lt_pi hmem.1 hmem.2
  have he':=(div_eq_iff hs.ne').mp he
  change Real.cos (Geometry.shiftedAngle q s ω)<0
  rw [he']
  exact mul_neg_of_neg_of_pos (hneg ω ⟨h0,hp⟩) hs

theorem exists_uniform_sigma_lower (p : ParameterStrip) (M : ℝ) :
    ∃δ : ℝ,0<δ ∧ ∀κ : ConditionNumber,κ.val<1+δ→M<fixedThreshold p κ := by
  let R:=max M 0+1
  have hR : 0<R:=by dsimp [R]; positivity
  obtain ⟨δ,hδ,hXi⟩:=exists_uniform_Xi_bound p R
  refine ⟨δ,hδ,fun κ hκ=>?_⟩
  apply lt_of_not_ge
  intro hsigma
  have hf:=(Levels.Threshold.shifted_fp_iff (tuning p κ) M).mpr hsigma
  apply shifted_infeasible_of_negative_profile (tuning p κ) M ?_ hf
  intro ω hω
  have hs:=Real.sin_pos_of_pos_of_lt_pi hω.1 hω.2
  have hc:=hXi κ hκ (Real.cos ω) ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩
  have hn : (tuning p κ).Xi (Real.cos ω)<0:=hc.trans (neg_neg_of_pos hR)
  have hdiv : Geometry.cotangent (tuning p κ) ω≤(tuning p κ).Xi (Real.cos ω) := by
    apply (div_le_iff₀ hs).mpr
    simpa only [mul_one] using mul_le_mul_of_nonpos_left (Real.sin_le_one ω) hn.le
  have hRM : M<R:=by dsimp [R]; linarith [le_max_left M 0]
  linarith

/-- On Ioi 1, atBot is precisely condition number decreasing to one. -/
theorem fixedThreshold_tendsto_atBot (p : ParameterStrip) :
    Tendsto (fixedThreshold p) atBot atTop := by
  apply tendsto_atTop.mpr
  intro M
  obtain ⟨δ,hδ,hbound⟩:=exists_uniform_sigma_lower p M
  let κ₀ : ConditionNumber:=⟨1+δ/2,by change (1:ℝ)<1+δ/2; linarith⟩
  filter_upwards [eventually_le_atBot κ₀] with κ hκ
  have hk : κ.val<1+δ:=by change κ.val≤1+δ/2 at hκ; linarith
  exact (hbound κ hk).le

theorem fixedThreshold_positive_somewhere (p : ParameterStrip) :
    ∃κ : ConditionNumber,0<fixedThreshold p κ := by
  obtain ⟨δ,hδ,hbound⟩:=exists_uniform_sigma_lower p 0
  exact ⟨⟨1+δ/2,by change (1:ℝ)<1+δ/2; linarith⟩,hbound _ (by linarith)⟩

theorem fixedPeriodicThreshold_positive_somewhere {k : ℕ} (hk : 3≤k) (p : ParameterStrip) :
    ∃κ : ConditionNumber,0<fixedPeriodicThreshold k p κ := by
  obtain ⟨κ,hκ⟩:=fixedThreshold_positive_somewhere p
  exact ⟨κ,hκ.trans_le (Levels.Threshold.sigma_le_sigmaPeriodic (tuning p κ) hk)⟩

end polyak.Global.Threshold
