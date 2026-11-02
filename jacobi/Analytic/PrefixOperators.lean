import jacobi.Analytic.PrefixProduct

/-!
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
The genuine GL prefix integral is bounded bilinear in its two continuous
kernels. Thus the actual holomorphic kernel defines a holomorphic family
of bounded GL operators on one fixed continuous-kernel Banach space.
Use: compares the continued GL operator with the previously proved original real forced inverse and its equation.
-/
namespace jacobi.Analytic
noncomputable section
open Set MeasureTheory jacobi.Reference jacobi.GelfandLevitan
open scoped Topology
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {𝕜 : Type*} [RCLike 𝕜]

/-- The continuous prefix product uses exactly the original subtype prefix integral.
Use: compares the continued GL operator with the previously proved original real forced inverse and its equation.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: convert the real interval integral by the proved original prefix identity. On that actual prefix every coordinate lies below one half, so both continuous physical clamps preserve precisely the same point. -/
theorem prefixProduct_subtype (K F : C(KernelSquare,𝕜)) (t s : HalfInterval) :
    prefixProduct K F (t,s)=∫ r : Interval in prefixSet (t:ℝ),
      K (t,halfClamp r)*F (halfClamp r,s) := by
  -- Both integrals retain the original Lebesgue measure, including the zero endpoint.
  rw [prefixProduct_apply,← prefix_integral
    (fun r => K (t,halfParameterClamp r)*F (halfParameterClamp r,s))
    (show (t:ℝ)∈Icc (0:ℝ) 1 from ⟨t.property.1,by linarith [t.property.2]⟩)]
  apply setIntegral_congr_fun (prefixSet_measurable _)
  intro r hr
  have hrh : (r:ℝ)∈Icc (0:ℝ) (1/2) := ⟨r.property.1,hr.trans t.property.2⟩
  have he : halfParameterClamp (r:ℝ)=halfClamp r := by
    apply Subtype.ext
    change ((Set.projIcc (0:ℝ) (1/2) (by norm_num) (r:ℝ)):ℝ)=min (r:ℝ) (1/2)
    rw [Set.projIcc_of_mem (by norm_num : (0:ℝ)≤1/2) hrh,min_eq_left hrh.2]
  dsimp only
  rw [he]

/-- Evaluation of the bounded prefix operator is the original continuous prefix product.
Use: identifies analytic bounded-operator identities with the literal physical GL equation.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the bounded-linear-map construction preserves its defining linear map pointwise. -/
theorem prefixOperator_apply (F K : C(KernelSquare,𝕜)) : prefixOperator F K=prefixProduct K F := rfl

/-- The genuine prefix operator has norm at most its continuous kernel norm, uniformly in every physical prefix.
Use: perturbing the analytic kernel in its proved Banach norm perturbs the actual GL operator in operator norm.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: apply the community operator-norm criterion to the proved genuine prefix-product norm estimate. -/
theorem prefixOperator_norm_le (F : C(KernelSquare,𝕜)) : ‖prefixOperator F‖≤‖F‖ :=
  (prefixOperator F).opNorm_le_bound (norm_nonneg F) (fun K => by
    rw [prefixOperator_apply]
    simpa only [mul_comm] using prefixProduct_norm_le K F)

/-- Dependence of the actual physical GL integral operator on its continuous kernel, as a linear map.
Use: packages the genuine second-variable linearity before proving operator-norm continuity and analytic dependence.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: continuous physical integrands justify additivity and scalar linearity of their original interval integrals; evaluate both kernels and operators to verify the identities. -/
def prefixOperatorsLinear : C(KernelSquare,𝕜) →ₗ[𝕜]
    (C(KernelSquare,𝕜) →L[𝕜] C(KernelSquare,𝕜)) where
  toFun := prefixOperator
  map_add' F G := by
    -- The true bilinear product has no complex conjugation in either argument.
    apply ContinuousLinearMap.ext
    intro K
    apply ContinuousMap.ext
    rintro ⟨t,s⟩
    simp only [add_apply,prefixOperator_apply,prefixProduct_apply,
      ContinuousMap.add_apply,mul_add]
    exact intervalIntegral.integral_add
      (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)
  map_smul' c F := by
    apply ContinuousLinearMap.ext
    intro K
    apply ContinuousMap.ext
    rintro ⟨t,s⟩
    simp only [smul_apply,prefixOperator_apply,prefixProduct_apply,
      ContinuousMap.smul_apply,smul_eq_mul,RingHom.id_apply]
    simp_rw [mul_left_comm _ c]
    exact intervalIntegral.integral_const_mul c _

/-- The actual kernel-to-prefix-operator map is bounded complex or real linear.
Use: transports the proved analytic continuous-kernel family to the original GL operator family in operator norm.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Source: mathlib's bounded linear map construction from the proved operator norm estimate. -/
def prefixOperators : C(KernelSquare,𝕜) →L[𝕜]
    (C(KernelSquare,𝕜) →L[𝕜] C(KernelSquare,𝕜)) :=
  LinearMap.mkContinuous (𝕜 := 𝕜) (𝕜₂ := 𝕜) (E := C(KernelSquare,𝕜))
    (F := C(KernelSquare,𝕜) →L[𝕜] C(KernelSquare,𝕜))
    (prefixOperatorsLinear (𝕜 := 𝕜)) 1 (fun F : C(KernelSquare,𝕜) => by
    change ‖prefixOperator F‖≤1*‖F‖
    simpa only [one_mul] using prefixOperator_norm_le F)

/-- The actual identity-plus-GL-prefix operator on one fixed complex continuous-kernel space.
Use: its original real inverse is continued analytically to construct the genuine complex GL kernel.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
-/
def OrderDisk.GLoperator {a0 : ℝ} (D : OrderDisk a0) (a : ℂ) :
    C(KernelSquare,ℂ) →L[ℂ] C(KernelSquare,ℂ) :=
  1+prefixOperators (D.kernelMap a)

/-- The original continued GL operator is holomorphic in operator norm on the common order disk.
Use: the Banach inverse theorem applies to the same physical integral operator after real-base invertibility is proved.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: compose the proved genuine kernel Banach holomorphy with the bounded complex-linear kernel-to-integral-operator map, then add the identity operator. -/
theorem OrderDisk.GLoperator_holomorphic {a0 : ℝ} (D : OrderDisk a0) :
    DifferentiableOn ℂ D.GLoperator (Metric.ball (a0:ℂ) D.radius) := by
  intro a ha
  have hL := ContinuousLinearMap.differentiableAt (𝕜 := ℂ) (E := C(KernelSquare,ℂ))
    (F := C(KernelSquare,ℂ) →L[ℂ] C(KernelSquare,ℂ)) (prefixOperators (𝕜 := ℂ))
    (x := D.kernelMap a)
  convert! (differentiableWithinAt_const (𝕜 := ℂ)
    (c := (1 : C(KernelSquare,ℂ) →L[ℂ] C(KernelSquare,ℂ)))).add
      (hL.comp_differentiableWithinAt (F := C(KernelSquare,ℂ))
        (G := C(KernelSquare,ℂ) →L[ℂ] C(KernelSquare,ℂ)) a (D.kernelMap_holomorphic a ha)) using 1

end
end jacobi.Analytic
