import jacobi.Analytic.KernelHolomorphy
import jacobi.GelfandLevitan.ShrinkingIntegral

/-!
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
The physical prefix product of two continuous kernels is a continuous
kernel, with a uniform norm bound. A fixed-domain affine average reuses
the original real GL integration machinery for real or complex scalars.
Use: the previously proved Banach-valued affine average integrates these same rows over the moving physical prefix.
-/
namespace jacobi.Analytic
noncomputable section
open Set MeasureTheory jacobi.Reference jacobi.GelfandLevitan
open scoped Topology
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {𝕜 : Type*} [RCLike 𝕜]

/-- Continuous rows of the literal bilinear integrand K(t,r)F(r,s).
Use: the previously proved Banach-valued affine average integrates these same rows over the moving physical prefix.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
-/
def prefixProductRows (K F : C(KernelSquare,𝕜)) : C(KernelSquare,C(HalfInterval,𝕜)) :=
  ⟨fun p => K p • F.curry p.2,
    K.continuous.smul (F.curry.continuous.comp continuous_snd)⟩

/-- The genuine physical prefix product, packaged as a continuous kernel on the whole half square.
Use: defines the continuous GL operator uniformly in the physical endpoint, with a fixed Banach space for analytic inversion.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
The fixed-domain affine average only parametrizes that same physical integral. -/
def prefixProduct (K F : C(KernelSquare,𝕜)) : C(KernelSquare,𝕜) :=
  (⟨fun t : HalfInterval => (t:ℝ) • affineAverage (prefixProductRows K F) ⟨0,by norm_num⟩ t,
    continuous_subtype_val.smul (affineAverage (prefixProductRows K F) ⟨0,by norm_num⟩).continuous⟩ :
    C(HalfInterval,C(HalfInterval,𝕜))).uncurry

/-- The continuous prefix product is exactly the original real physical interval integral of its defining bilinear kernel factors.
Use: identifies the norm-continuous operator construction with the actual GL equation and its original real inverse.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: at the zero endpoint both sides vanish. Else the proved genuine affine-average substitution gives the physical integral divided by its interval length; multiply by that length and commute continuous evaluation with the Bochner integral. -/
theorem prefixProduct_apply (K F : C(KernelSquare,𝕜)) (t s : HalfInterval) :
    prefixProduct K F (t,s)=∫ r in (0:ℝ)..(t:ℝ),K (t,halfParameterClamp r)*F (halfParameterClamp r,s) := by
  -- The affine average preserves every actual integration point and the original physical measure.
  change ((t:ℝ) • affineAverage (prefixProductRows K F) ⟨0,by norm_num⟩ t) s=_
  by_cases ht : t=⟨0,by norm_num⟩
  · subst t
    change (((0:ℝ) • _) : C(HalfInterval,𝕜)) s=∫ r in (0:ℝ)..0,_
    simp only [ContinuousMap.smul_apply,zero_smul,intervalIntegral.integral_same]
  have ht0 : (t:ℝ)≠0 := fun h => ht (Subtype.ext h)
  rw [affineAverage_integral _ _ _ ht]
  simp only [sub_zero,smul_smul,mul_inv_cancel₀ ht0,one_smul]
  have hi : IntervalIntegrable (fun r : ℝ => prefixProductRows K F (t,halfParameterClamp r)) volume 0 (t:ℝ) :=
    (show Continuous (fun r : ℝ => prefixProductRows K F (t,halfParameterClamp r)) by fun_prop).intervalIntegrable _ _
  have hh := (ContinuousMap.evalCLM ℝ s).intervalIntegral_comp_comm hi
  simpa only [ContinuousMap.evalCLM_apply,prefixProductRows,ContinuousMap.coe_mk,
    ContinuousMap.smul_apply,ContinuousMap.curry_apply,smul_eq_mul] using hh.symm

/-- The actual physical prefix product has norm at most the product of the two original kernel norms.
Use: gives the bounded bilinear operator needed to transfer kernel-norm analyticity to GL operator-norm analyticity.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: each actual integrand is bounded by the product of the two supremum norms, and every physical prefix has length at most one half, hence at most one. Apply the community norm bound for Bochner interval integrals. -/
theorem prefixProduct_norm_le (K F : C(KernelSquare,𝕜)) :
    ‖prefixProduct K F‖≤‖K‖*‖F‖ := by
  -- The bound is uniform in both physical coordinates, including the collapsed zero interval.
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro p
  rw [prefixProduct_apply]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := (p.1:ℝ)) (C := ‖K‖*‖F‖)
    (f := fun r => K (p.1,halfParameterClamp r)*F (halfParameterClamp r,p.2)) (fun r _ => by
      rw [norm_mul]
      exact mul_le_mul (K.norm_coe_le_norm _) (F.norm_coe_le_norm _) (norm_nonneg _) (norm_nonneg _))
  rw [sub_zero,abs_of_nonneg p.1.property.1] at hh
  have ht : (p.1:ℝ)≤1 := by linarith [p.1.property.2]
  exact hh.trans (by nlinarith [mul_nonneg (norm_nonneg K) (norm_nonneg F)])

/-- The physical prefix product is complex or real linear in its first kernel input.
Use: packages the actual integral as a bounded GL operator without adding an abstract representation assumption.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the defining physical integrands are continuous, so interval integration preserves their sums and scalar multiples. Extensionality gives the same identities in the original continuous-kernel space. -/
def prefixProductLinear (F : C(KernelSquare,𝕜)) : C(KernelSquare,𝕜) →ₗ[𝕜] C(KernelSquare,𝕜) where
  toFun K := prefixProduct K F
  map_add' K L := by
    -- Genuine continuous integrands justify splitting the original physical integral.
    apply ContinuousMap.ext
    rintro ⟨t,s⟩
    simp only [prefixProduct_apply,ContinuousMap.add_apply,add_mul]
    exact intervalIntegral.integral_add
      (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)
  map_smul' c K := by
    apply ContinuousMap.ext
    rintro ⟨t,s⟩
    simp only [prefixProduct_apply,ContinuousMap.smul_apply,smul_eq_mul,mul_assoc,RingHom.id_apply]
    exact intervalIntegral.integral_const_mul c _

/-- The actual continuous GL integral operator with fixed continuous kernel F.
Use: analytic inversion uses this original operator in a fixed continuous-kernel Banach space.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Source: mathlib's bounded-linear-map construction from a genuine norm bound. -/
def prefixOperator (F : C(KernelSquare,𝕜)) : C(KernelSquare,𝕜) →L[𝕜] C(KernelSquare,𝕜) :=
  (prefixProductLinear F).mkContinuous ‖F‖ (fun K => by
    change ‖prefixProduct K F‖≤‖F‖*‖K‖
    simpa only [mul_comm] using prefixProduct_norm_le K F)

end
end jacobi.Analytic
