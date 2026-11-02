import jacobi.Support.CauchyVolterraRegularity

/-!
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
The exact single-kernel equation has uniqueness in the entire printed
continuous O(t^gamma) class. Its normalized quotient is proved continuous
by CauchyVolterraRegularity, so the original genuine Gronwall theorem
applies without any additional candidate regularity assumption.
Use: the original amplitude can be retained in full-class uniqueness and exact solution identification.
-/
namespace jacobi.Support
noncomputable section
open Real Set Complex Filter MeasureTheory jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The genuine nested ground Volterra operator preserves scalar multiplication.
Use: the original amplitude can be retained in full-class uniqueness and exact solution identification.
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
Proof: pull the same constant through each actual interval integral; division by the fixed endpoint ground square preserves the factor. -/
theorem groundVolterra_const_mul (a:ℝ) (c:ℂ) (q:ℝ→ℂ) (t:ℝ) :
    groundVolterra a (fun s => c*q s) t=c*groundVolterra a q t := by
  -- Both scalar extractions concern the literal original nested operator.
  unfold groundVolterra
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro r _
  unfold groundFlux
  have he : (fun s:ℝ => (weight a s:ℂ)^2*(c*q s))=
      fun s => c*((weight a s:ℂ)^2*q s) := funext (fun _ => by ring)
  rw [he,intervalIntegral.integral_const_mul]
  ring

/-- The regular nested Volterra problem has the actual reference core as its unique solution at any prescribed amplitude.
Use: identifies the removable ground quotient of every original bounded-growth Cauchy candidate.
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
Proof: the scalar multiple of the original reference core solves the genuine amplitude equation. Subtract it from the arbitrary continuous factor, use actual integral subtraction and apply the original homogeneous Gronwall theorem. -/
theorem regularWave_unique_amplitude {a:ℝ} (ha:-1<a) (E c:ℂ) {q:ℝ→ℂ}
    (hq:ContinuousOn q (Icc (0:ℝ) (1/2)))
    (heq:∀ t∈Icc (0:ℝ) (1/2),q t=c+((eigenvalue a 0:ℂ)-E)*groundVolterra a q t) :
    ∀ t∈Icc (0:ℝ) (1/2),q t=c*regularWave a E t := by
  -- The comparison core and its amplitude are the actual original reference solution.
  have hr := regularWave_continuous_half a E
  have hc : ContinuousOn (fun t => c*regularWave a E t) (Icc (0:ℝ) (1/2)) := continuousOn_const.mul hr
  have he (t:ℝ) (ht:t∈Icc (0:ℝ) (1/2)) :
      c*regularWave a E t=c+((eigenvalue a 0:ℂ)-E)*groundVolterra a (fun s => c*regularWave a E s) t := by
    rw [groundVolterra_const_mul,regularWave_groundVolterra ha E ht]
    ring
  have hz := groundVolterra_unique_zero ha (hq.sub hc) ((eigenvalue a 0:ℂ)-E) (fun t ht => by
    change q t-c*regularWave a E t=((eigenvalue a 0:ℂ)-E)*
      groundVolterra a (fun s => q s-c*regularWave a E s) t
    rw [groundVolterra_sub ha ht
      (hq.mono (fun _ hs => ⟨hs.1,hs.2.trans ht.2⟩))
      (hc.mono (fun _ hs => ⟨hs.1,hs.2.trans ht.2⟩)),heq t ht,he t ht]
    ring)
  exact fun t ht => sub_eq_zero.mp (hz t ht)

/-- The original ground-bounded candidate is exactly its genuine ground weight times the removable regular quotient.
Use: translates the literal source Cauchy equation to the already proved normalized nested equation, including zero.
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
Proof: at zero the original growth bound forces the actual candidate value to vanish. At positive physical points the true ground weight is nonzero, so division cancels exactly. -/
theorem cauchyRegularFactor_factorization {a:ℝ} (ha:-1<a) (c:ℂ) {v:ℝ→ℂ} {M:ℝ}
    (hbound:∀ t∈Icc (0:ℝ) (1/2),‖v t‖≤M*weight a t) :
    ∀ t∈Icc (0:ℝ) (1/2),v t=(weight a t:ℂ)*cauchyRegularFactor a c v t := by
  -- The removable endpoint is justified by the original source growth bound.
  intro t ht
  by_cases ht0 : t=0
  · subst t
    have hz := hbound 0 (by norm_num)
    rw [(weight_properties ha).2.1,mul_zero] at hz
    rw [norm_le_zero_iff.mp hz,(weight_properties ha).2.1,Complex.ofReal_zero,zero_mul]
  · have hw : (weight a t:ℂ)≠0 := Complex.ofReal_ne_zero.mpr
      (weight_pos a ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0),by linarith [ht.2]⟩).ne'
    rw [cauchyRegularFactor,ite_eq_right ht0]
    field_simp

/-- Every original ground-bounded continuous candidate of the literal single-integral equation is the genuine reference solution.
Use: supplies full-class uniqueness after proving normalized endpoint regularity, rather than assuming it.
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
Proof: the original equation forces a continuous removable ground quotient. Exact factorization and the proved physical-domain Cauchy/nested identity give its amplitude Volterra equation. The already proved genuine Gronwall uniqueness fixes this quotient, and restoring the original ground weight gives the actual reference solution. -/
theorem cauchy_candidate_eq_solution {a:ℝ} (ha:-1<a) (E c:ℂ) {v:ℝ→ℂ}
    (hv:ContinuousOn v (Icc (0:ℝ) (1/2))) {M:ℝ} (hM:0≤M)
    (hbound:∀ t∈Icc (0:ℝ) (1/2),‖v t‖≤M*weight a t)
    (heq:∀ t∈Icc (0:ℝ) (1/2),v t=c*(weight a t:ℂ)+
      ((eigenvalue a 0:ℂ)-E)*groundCauchyAction a v t) :
    ∀ t∈Icc (0:ℝ) (1/2),v t=c*solution a E t := by
  -- No regularity of V/U is among the candidate hypotheses.
  let q := cauchyRegularFactor a c v
  have hq := cauchyRegularFactor_continuous ha hv hM hbound heq
  have hfactor := cauchyRegularFactor_factorization ha c hbound
  have hc (t:ℝ) (ht:t∈Icc (0:ℝ) (1/2)) :
      groundCauchyAction a v t=(weight a t:ℂ)*groundVolterra a q t := by
    calc
      _ = groundCauchyAction a (fun s => (weight a s:ℂ)*q s) t := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le ht.1] at hs
        dsimp only
        rw [hfactor s ⟨hs.1,hs.2.trans ht.2⟩]
      _ = _ := groundCauchyAction_nested_on ha hq ht
  have he (t:ℝ) (ht:t∈Icc (0:ℝ) (1/2)) :
      q t=c+((eigenvalue a 0:ℂ)-E)*groundVolterra a q t := by
    by_cases ht0 : t=0
    · subst t
      simp [q,cauchyRegularFactor,groundVolterra]
    · have hw : (weight a t:ℂ)≠0 := Complex.ofReal_ne_zero.mpr
        (weight_pos a ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0),by linarith [ht.2]⟩).ne'
      change cauchyRegularFactor a c v t=_
      rw [cauchyRegularFactor,ite_eq_right ht0]
      apply (div_eq_iff hw).mpr
      rw [heq t ht,hc t ht]
      ring
  have hunique := regularWave_unique_amplitude ha E c hq he
  intro t ht
  rw [hfactor t ht,hunique t ht,solution_regularWave]
  ring

/-- Every continuous candidate in the full printed endpoint-power class of the original Cauchy equation equals the actual reference solution.
Use: discharges the formerly missing O(t^gamma) uniqueness statement in the exact original source class.
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
Proof: the genuine sine-power ground state is comparable to t^gamma on the closed physical half interval. Convert the actual printed growth bound by its proved fixed coefficient, and invoke the completed ground-bounded candidate theorem. -/
theorem cauchy_power_candidate_eq_solution {a:ℝ} (ha:-1<a) (E c:ℂ) {v:ℝ→ℂ}
    (hv:ContinuousOn v (Icc (0:ℝ) (1/2))) {M:ℝ} (hM:0≤M)
    (hbound:∀ t∈Icc (0:ℝ) (1/2),‖v t‖≤M*t^(gamma a))
    (heq:∀ t∈Icc (0:ℝ) (1/2),v t=c*(weight a t:ℂ)+
      ((eigenvalue a 0:ℂ)-E)*groundCauchyAction a v t) :
    ∀ t∈Icc (0:ℝ) (1/2),v t=c*solution a E t := by
  apply cauchy_candidate_eq_solution ha E c hv (M := M*(Real.pi/2)^(gamma a))
    (mul_nonneg hM (Real.rpow_nonneg (div_nonneg Real.pi_pos.le (by norm_num)) _)) ?_ heq
  intro t ht
  have hh := mul_le_mul_of_nonneg_left (endpointPower_le_weight ha ht) hM
  exact (hbound t ht).trans (by simpa only [mul_assoc] using hh)

end
end jacobi.Support
