import jacobi.Support.CauchyVolterraUniqueness
import jacobi.Support.EdgeLimit

/-!
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
The literal single-integral equation has the original reference solution
as its unique continuous solution in the full printed O(t^gamma) class.
Existence includes genuine integrability of the original Cauchy action.
The source normalization U, kappa_U and energy shift are retained exactly.
Use: identifies the proven sine-weight kernel with the source U-normalized kernel.
-/
namespace jacobi.Support
noncomputable section
open Real Set Complex Filter MeasureTheory jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Scaling the actual ground state by a nonzero constant leaves its literal reduction-of-order Cauchy kernel unchanged.
Use: identifies the proven sine-weight kernel with the source U-normalized kernel.
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
Proof: the inverse ground square contributes the reciprocal square of the constant, which can be pulled out of its genuine interval integral and cancels the two endpoint factors. -/
theorem groundCauchyKernel_scale (a:ℝ) (c:ℂ) (hc:c≠0) (t s:ℝ) :
    (c*(weight a t:ℂ))*(c*(weight a s:ℂ))*
      (∫ r in s..t,((c*(weight a r:ℂ))^2)⁻¹)=groundCauchyKernel a t s := by
  -- The cancellation is valid for the actual integral, including its total endpoint extension.
  simp_rw [mul_pow,mul_inv]
  rw [intervalIntegral.integral_const_mul]
  unfold groundCauchyKernel
  field_simp

/-- The actual support top profile gives precisely the same literal Cauchy kernel as the normalized reference ground weight.
Use: the complete continuum Volterra theorem below uses the exact U specified by the original support-chain limit.
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
Proof: the original top profile is its actual positive Gamma amplitude times the genuine ground weight on this entire interval. Substitute that exact identity at both endpoints and every true integration coordinate, then use the proved scaling cancellation. -/
theorem groundCauchyKernel_topProfile {a b t s:ℝ} (ha:-1<a) (hb:-1<b)
    (ht:t∈Icc (0:ℝ) (1/2)) (hs:s∈Icc (0:ℝ) t) :
    groundCauchyKernel a t s=(topProfile a b t:ℂ)*(topProfile a b s:ℂ)*
      (∫ r in s..t,((topProfile a b r:ℂ)^2)⁻¹) := by
  -- The original positive normalization is proved nonzero before it is cancelled.
  let c : ℂ := (Real.sqrt (topAmplitudeSquare a b):ℂ)
  have hc : c≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (topAmplitudeSquare_pos ha hb)).ne'
  have he (r:ℝ) (hr:r∈Icc (0:ℝ) (1/2)) : (topProfile a b r:ℂ)=c*(weight a r:ℂ) := by
    rw [topProfile_weight hr,Complex.ofReal_mul]
  rw [he t ht,he s ⟨hs.1,hs.2.trans ht.2⟩]
  have hi : (∫ r in s..t,((topProfile a b r:ℂ)^2)⁻¹)=
      ∫ r in s..t,((c*(weight a r:ℂ))^2)⁻¹ := by
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le hs.2] at hr
    dsimp only
    rw [he r ⟨hs.1.trans hr.1,hr.2.trans ht.2⟩]
  rw [hi,groundCauchyKernel_scale a c hc]

/-- The actual normalized reference solution supplies existence, genuine integral convergence and full bounded-growth uniqueness for the original single-kernel Volterra equation at arbitrary complex energy and amplitude.
Use: completes the continuum Volterra lemma before specializing to the printed support-chain normalization and energy coordinate.
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
Proof: the original solution is its genuine ground weight times the continuous regular core. Triangular Fubini gives the literal Cauchy equation and genuine integral convergence. The bounded core and ground envelope give the printed endpoint power bound. The full candidate theorem proves uniqueness for every original continuous O(t^gamma) competitor. -/
theorem continuum_volterra_complete {a:ℝ} (ha:-1<a) (E c:ℂ) :
    let V : ℝ→ℂ := fun t => c*solution a E t
    ContinuousOn V (Icc (0:ℝ) (1/2)) ∧
      (∃ M:ℝ,0≤M ∧ ∀ t∈Icc (0:ℝ) (1/2),‖V t‖≤M*t^(gamma a)) ∧
      (∀ t∈Icc (0:ℝ) (1/2),
        IntervalIntegrable (fun s => groundCauchyKernel a t s*V s) volume 0 t ∧
        V t=c*(weight a t:ℂ)+((eigenvalue a 0:ℂ)-E)*groundCauchyAction a V t) ∧
      ∀ W:ℝ→ℂ,ContinuousOn W (Icc (0:ℝ) (1/2)) →
        (∃ M:ℝ,0≤M ∧ ∀ t∈Icc (0:ℝ) (1/2),‖W t‖≤M*t^(gamma a)) →
        (∀ t∈Icc (0:ℝ) (1/2),W t=c*(weight a t:ℂ)+
          ((eigenvalue a 0:ℂ)-E)*groundCauchyAction a W t) → EqOn W V (Icc (0:ℝ) (1/2)) := by
  -- Existence, convergence and uniqueness all concern the same original reference function and literal Cauchy action.
  dsimp only
  let q : ℝ→ℂ := fun t => c*regularWave a E t
  have hq : ContinuousOn q (Icc (0:ℝ) (1/2)) := continuousOn_const.mul (regularWave_continuous_half a E)
  have hfactor (t:ℝ) : c*solution a E t=(weight a t:ℂ)*q t := by
    rw [solution_regularWave]
    dsimp only [q]
    ring
  have hv : ContinuousOn (fun t => c*solution a E t) (Icc (0:ℝ) (1/2)) := by
    have hc := ((Complex.continuous_ofReal.comp (weight_properties ha).1).continuousOn).mul hq
    exact hc.congr (fun t _ => hfactor t)
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hq
  have hM : 0≤|B|+1 := by positivity
  have hgrowth : ∀ t∈Icc (0:ℝ) (1/2),‖c*solution a E t‖≤(|B|+1)*t^(gamma a) := by
    intro t ht
    have hqn : ‖q t‖≤|B|+1 := (hB t ht).trans (by linarith [le_abs_self B])
    have hw : 0≤weight a t := Real.rpow_nonneg (div_nonneg
      (Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg Real.pi_pos.le ht.1)
        (by nlinarith [Real.pi_pos,ht.2])) Real.pi_pos.le) _
    have hupper : weight a t≤t^(gamma a) := by
      by_cases ht0 : t=0
      · rw [ht0,(weight_properties ha).2.1]
        exact Real.rpow_nonneg le_rfl _
      · exact weight_half_bound ha ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0),ht.2⟩
    rw [hfactor t,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hw]
    exact (mul_le_mul_of_nonneg_left hqn hw).trans
      (by nlinarith [mul_le_mul_of_nonneg_left hupper hM])
  refine ⟨hv,⟨|B|+1,hM,hgrowth⟩,?_,?_⟩
  · intro t ht
    have hc : groundCauchyAction a (fun s => c*solution a E s) t=
        (weight a t:ℂ)*(c*groundVolterra a (regularWave a E) t) := by
      calc
        _ = groundCauchyAction a (fun s => (weight a s:ℂ)*q s) t := by
          congr 1
          exact funext hfactor
        _ = (weight a t:ℂ)*groundVolterra a q t := groundCauchyAction_nested_on ha hq ht
        _ = _ := by rw [groundVolterra_const_mul]
    constructor
    · let e : ℝ→ℂ := fun s => q (max 0 (min s (1/2)))
      have hec : Continuous e := hq.comp_continuous
        (continuous_const.max (continuous_id.min continuous_const))
        (fun s => ⟨le_max_left _ _,max_le (by norm_num) (min_le_right _ _)⟩)
      apply (groundCauchyAction_integrable ha hec ht).congr_uIoo
      intro s hs
      rw [uIoo_of_le ht.1] at hs
      dsimp only
      rw [hfactor s]
      dsimp only [e]
      rw [min_eq_left (hs.2.le.trans ht.2),max_eq_right hs.1.le]
    · rw [hc,solution_regularWave,regularWave_groundVolterra ha E ht]
      ring
  · intro W hW hgrowth heq
    obtain ⟨M,hM,hbound⟩ := hgrowth
    exact cauchy_power_candidate_eq_solution ha E c hW hM hbound heq

/-- The original support-chain continuum Volterra lemma holds with its printed U, exact energy shift and full continuous bounded-growth uniqueness class.
Use: supplies the literal auxiliary statement of Appendix D in addition to the already proved original finite edge limits.
Article: jacobi, Appendix C.3 (continuum Volterra formula and uniqueness).
Proof: specialize the completed arbitrary-amplitude theorem to the genuine support Gamma amplitude and shifted source energy. The actual top-profile identity gives precisely U, and the reference ground eigenvalue gives exactly gamma squared pi squared after the energy shift cancels. -/
theorem source_continuum_volterra {a b:ℝ} (ha:-1<a) (hb:-1<b) (z:ℂ) :
    let V : ℝ→ℂ := fun t => (topConstant a b:ℂ)*((Real.pi^(gamma a):ℝ):ℂ)*
      solution a (z+(jacobi.Jacobi.endpointCorrection a:ℂ)) t
    ContinuousOn V (Icc (0:ℝ) (1/2)) ∧
      (∃ M:ℝ,0≤M ∧ ∀ t∈Icc (0:ℝ) (1/2),‖V t‖≤M*t^(gamma a)) ∧
      (∀ t∈Icc (0:ℝ) (1/2),∀ s∈Icc (0:ℝ) t,
        groundCauchyKernel a t s=(topProfile a b t:ℂ)*(topProfile a b s:ℂ)*
          (∫ r in s..t,((topProfile a b r:ℂ)^2)⁻¹)) ∧
      (∀ t∈Icc (0:ℝ) (1/2),
        IntervalIntegrable (fun s => groundCauchyKernel a t s*V s) volume 0 t ∧
        V t=(topProfile a b t:ℂ)-(z-((gamma a)^2*Real.pi^2:ℝ))*groundCauchyAction a V t) ∧
      ∀ W:ℝ→ℂ,ContinuousOn W (Icc (0:ℝ) (1/2)) →
        (∃ M:ℝ,0≤M ∧ ∀ t∈Icc (0:ℝ) (1/2),‖W t‖≤M*t^(gamma a)) →
        (∀ t∈Icc (0:ℝ) (1/2),W t=(topProfile a b t:ℂ)-
          (z-((gamma a)^2*Real.pi^2:ℝ))*groundCauchyAction a W t) → EqOn W V (Icc (0:ℝ) (1/2)) := by
  -- Both the printed physical ground state and the printed spectral energy coordinate are identified exactly.
  let c : ℂ := (topConstant a b:ℂ)*((Real.pi^(gamma a):ℝ):ℂ)
  have hc : c=(Real.sqrt (topAmplitudeSquare a b):ℂ) := by
    dsimp [c,topConstant]
    push_cast
    field_simp [(Real.rpow_pos_of_pos Real.pi_pos (gamma a)).ne']
  have hU (t:ℝ) (ht:t∈Icc (0:ℝ) (1/2)) : c*(weight a t:ℂ)=(topProfile a b t:ℂ) := by
    rw [hc,topProfile_weight ht,Complex.ofReal_mul]
  have hδ : (eigenvalue a 0:ℂ)-(z+(jacobi.Jacobi.endpointCorrection a:ℂ))=
      -(z-((gamma a)^2*Real.pi^2:ℝ)) := by
    unfold eigenvalue
    push_cast
    ring
  obtain ⟨hV,hgrowth,heq,hunique⟩ := continuum_volterra_complete ha
    (z+(jacobi.Jacobi.endpointCorrection a:ℂ)) c
  refine ⟨hV,hgrowth,fun _ ht _ hs => groundCauchyKernel_topProfile ha hb ht hs,?_,?_⟩
  · intro t ht
    obtain ⟨hi,he⟩ := heq t ht
    rw [hU t ht,hδ,neg_mul,← sub_eq_add_neg] at he
    exact ⟨hi,he⟩
  · intro W hW hg he
    apply hunique W hW hg
    intro t ht
    rw [hU t ht,hδ,neg_mul,← sub_eq_add_neg]
    exact he t ht

end
end jacobi.Support
