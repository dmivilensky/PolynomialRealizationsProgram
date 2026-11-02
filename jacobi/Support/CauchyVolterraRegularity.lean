import jacobi.Support.CauchyVolterraBounds

/-!
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
Every continuous original bounded-growth candidate has the required
continuous ground quotient. The endpoint value is forced by the actual
equation and the two-power Cauchy action bound, rather than assumed as an
extra regularity condition in the original uniqueness class.
Use: extends a continuous regular factor outside the physical interval solely to apply triangular Fubini.
-/
namespace jacobi.Support
noncomputable section
open Real Set Complex Filter MeasureTheory jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The original nested ground operator depends only on its actual physical prefix input.
Use: extends a continuous regular factor outside the physical interval solely to apply triangular Fubini.
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
Proof: replace the input at every true inner integration point; both genuine interval integrals then agree. -/
theorem groundVolterra_congr {a t:ℝ} (ht:0≤t) {q r:ℝ→ℂ}
    (he:∀ s∈Icc (0:ℝ) t,q s=r s) : groundVolterra a q t=groundVolterra a r t := by
  -- Every nested source coordinate lies in the same original physical prefix.
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le ht] at hx
  unfold groundFlux
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le hx.1] at hs
  dsimp only
  rw [he s ⟨hs.1,hs.2.trans hx.2⟩]

/-- The literal Cauchy/nested identity applies to every factor continuous only on the original closed physical interval.
Use: the full bounded-growth candidate theorem requires no artificial continuity outside the article's domain.
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
Proof: extend the actual factor continuously by clamping to the physical half interval. The existing exact Fubini identity applies to that extension, and both original integral operators depend only on the unchanged physical prefix. -/
theorem groundCauchyAction_nested_on {a:ℝ} (ha:-1<a) {q:ℝ→ℂ}
    (hq:ContinuousOn q (Icc (0:ℝ) (1/2))) {t:ℝ} (ht:t∈Icc (0:ℝ) (1/2)) :
    groundCauchyAction a (fun s => (weight a s:ℂ)*q s) t=(weight a t:ℂ)*groundVolterra a q t := by
  -- The extension fixes every actual integration coordinate including both endpoints.
  let e : ℝ→ℂ := fun s => q (max 0 (min s (1/2)))
  have hec : Continuous e := hq.comp_continuous
    (continuous_const.max (continuous_id.min continuous_const))
    (fun s => ⟨le_max_left _ _,max_le (by norm_num) (min_le_right _ _)⟩)
  have he (s:ℝ) (hs:s∈Icc (0:ℝ) t) : e s=q s := by
    dsimp [e]
    rw [min_eq_left (hs.2.trans ht.2),max_eq_right hs.1]
  have hc : groundCauchyAction a (fun s => (weight a s:ℂ)*q s) t=
      groundCauchyAction a (fun s => (weight a s:ℂ)*e s) t := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    dsimp only
    rw [he s hs]
  rw [hc,groundCauchyAction_nested ha hec ht,groundVolterra_congr ht.1 he]

/-- The ground-normalized original candidate with its prescribed removable value at zero.
Use: proves this quotient continuous from the original equation, before invoking genuine full-class uniqueness.
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
-/
def cauchyRegularFactor (a:ℝ) (c:ℂ) (v:ℝ→ℂ) (t:ℝ) : ℂ :=
  if t=0 then c else v t/(weight a t:ℂ)

/-- Every original ground-bounded Volterra candidate has the prescribed genuinely continuous regular factor.
Use: removes the formerly extra normalized-continuity premise from the printed O(t^gamma) uniqueness theorem.
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
Proof: away from zero divide the actual continuous candidate by its positive ground weight. The original equation and the two-power Cauchy bound give |V/U-c|<=abs(delta)*M*t squared. This tends to zero at the endpoint and forces the chosen removable value c continuously. -/
theorem cauchyRegularFactor_continuous {a:ℝ} (ha:-1<a) {c δ:ℂ} {v:ℝ→ℂ}
    (hv:ContinuousOn v (Icc (0:ℝ) (1/2))) {M:ℝ} (hM:0≤M)
    (hbound:∀ t∈Icc (0:ℝ) (1/2),‖v t‖≤M*weight a t)
    (heq:∀ t∈Icc (0:ℝ) (1/2),v t=c*(weight a t:ℂ)+δ*groundCauchyAction a v t) :
    ContinuousOn (cauchyRegularFactor a c v) (Icc (0:ℝ) (1/2)) := by
  -- Endpoint regularity is a consequence of the true equation and growth bound, not a condition on the candidate.
  have herror (t:ℝ) (ht:t∈Icc (0:ℝ) (1/2)) :
      ‖cauchyRegularFactor a c v t-c‖≤(‖δ‖*M)*t^2 := by
    by_cases ht0 : t=0
    · simp [ht0,cauchyRegularFactor]
    have htp : 0<t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    have hw := weight_pos a ⟨htp,by linarith [ht.2]⟩
    have he : cauchyRegularFactor a c v t-c=δ*groundCauchyAction a v t/(weight a t:ℂ) := by
      rw [cauchyRegularFactor,ite_eq_right ht0,heq t ht,add_div,mul_div_cancel_right₀ c (Complex.ofReal_ne_zero.mpr hw.ne')]
      abel
    rw [he,norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hw]
    apply (div_le_iff₀ hw).mpr
    have hh := mul_le_mul_of_nonneg_left (groundCauchyAction_bound ha hM ht
      (fun s hs => hbound s ⟨hs.1.le,hs.2.trans ht.2⟩)) (norm_nonneg δ)
    nlinarith
  intro t ht
  by_cases ht0 : t=0
  · subst t
    have hlim : Tendsto (fun s:ℝ => (‖δ‖*M)*s^2) (𝓝[Icc (0:ℝ) (1/2)] 0) (𝓝 0) := by
      have hc : Continuous (fun s:ℝ => (‖δ‖*M)*s^2) := by fun_prop
      have he := (hc.continuousAt (x := (0:ℝ))).tendsto
      have he' : Tendsto (fun s:ℝ => (‖δ‖*M)*s^2) (𝓝 (0:ℝ)) (𝓝 0) := by simpa only [zero_pow (by norm_num : 2≠0),mul_zero] using he
      exact he'.mono_left nhdsWithin_le_nhds
    have hb : ∀ᶠ s in 𝓝[Icc (0:ℝ) (1/2)] 0,
        ‖cauchyRegularFactor a c v s-c‖≤(‖δ‖*M)*s^2 := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact herror s hs
    have hzero : Tendsto (fun s:ℝ => cauchyRegularFactor a c v s-c)
        (𝓝[Icc (0:ℝ) (1/2)] 0) (𝓝 0) :=
      squeeze_zero_norm' hb hlim
    change Tendsto (cauchyRegularFactor a c v) _ (𝓝 (cauchyRegularFactor a c v 0))
    have hq0 : cauchyRegularFactor a c v 0=c := by simp [cauchyRegularFactor]
    rw [hq0]
    simpa only [sub_add_cancel,zero_add] using hzero.add_const c
  · have htp : 0<t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    have hw : (weight a t:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (weight_pos a ⟨htp,by linarith [ht.2]⟩).ne'
    have hc := (hv t ht).div
      ((Complex.continuous_ofReal.comp (weight_properties ha).1).continuousAt.continuousWithinAt) hw
    apply hc.congr_of_eventuallyEq_of_mem ?_ ht
    filter_upwards [(eventually_ne_nhds ht0).filter_mono nhdsWithin_le_nhds] with s hs
    change cauchyRegularFactor a c v s=v s/(weight a s:ℂ)
    simp only [cauchyRegularFactor,ite_eq_right hs]

end
end jacobi.Support
