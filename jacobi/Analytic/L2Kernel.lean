import jacobi.Analytic.ComplexL2
import jacobi.Analytic.KernelHolomorphy
import jacobi.GelfandLevitan.KernelAction
import Mathlib.Topology.ContinuousMap.Star

/-!
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Every continuous complex physical kernel defines its genuine integral
operator on complex L2. Conjugating its Hilbert row cancels the conjugate
in the inner product. The unit measure of the ambient interval gives
the uniform operator norm bound by the kernel supremum norm.
Use: represents the actual integral action on zero-extended physical inputs.
-/
namespace jacobi.Analytic
noncomputable section
open Set MeasureTheory Filter jacobi.Reference jacobi.GelfandLevitan
open scoped Topology InnerProductSpace
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The unchanged compact physical kernel row, extended to the shared unit interval by the original clamp.
Use: represents the actual integral action on zero-extended physical inputs.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
-/
def complexRow (F : C(KernelSquare,ℂ)) (s : Interval) : C(Interval,ℂ) :=
  (F.curry (halfClamp s)).comp halfClamp

/-- The genuine continuous-function inclusion into complex L2 has norm at most one on the original unit measure.
Use: bounds the actual kernel action and all interval compressions by the kernel supremum norm.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Source: mathlib, ContinuousMap.toLp_norm_le.
Proof: substitute the proved unit total Lebesgue measure into the community continuous-function L2 inclusion bound. -/
theorem complex_toLp_norm_le :
    ‖(ContinuousMap.toLp (𝕜 := ℂ) (p := 2) volume : C(Interval,ℂ) →L[ℂ] ComplexL2)‖≤1 := by
  have hm : measureUnivNNReal (volume : Measure Interval)=1 := by
    apply ENNReal.coe_injective
    rw [coe_measureUnivNNReal,interval_volume_univ,ENNReal.coe_one]
  simpa only [hm,NNReal.coe_one,Real.one_rpow] using
    (ContinuousMap.toLp_norm_le (𝕜 := ℂ) (E := ℂ) (p := 2) (volume : Measure Interval))

/-- Genuine complex L2 rows with the conjugation required by the Hilbert inner product.
Use: constructs a continuous representative of the kernel action for every actual L2 input.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
-/
def complexHilbertRow (F : C(KernelSquare,ℂ)) : C(Interval,ComplexL2) where
  toFun s := ContinuousMap.toLp (𝕜 := ℂ) (p := 2) volume (star (complexRow F s))
  continuous_toFun := by
    have hc : Continuous (complexRow F) :=
      (ContinuousMap.compCLM ℂ ℂ halfClamp).continuous.comp (F.curry.continuous.comp halfClamp.continuous)
    exact (ContinuousMap.toLp (𝕜 := ℂ) (p := 2) volume).continuous.comp hc.star

/-- Each genuine Hilbert row is bounded by the actual kernel supremum norm.
Use: gives an operator perturbation bound independent of the physical endpoint t.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: apply the unit-measure L2 inclusion bound, invariance of the continuous-function norm under conjugation, and the original kernel supremum bound. -/
theorem complexHilbertRow_norm (F : C(KernelSquare,ℂ)) (s : Interval) :
    ‖complexHilbertRow F s‖≤‖F‖ := by
  -- Conjugating the row preserves pointwise modulus and the original supremum bound.
  calc
    _ ≤ 1*‖star (complexRow F s)‖ :=
      (ContinuousMap.toLp (𝕜 := ℂ) (p := 2) volume).le_of_opNorm_le complex_toLp_norm_le _
    _ ≤ ‖complexRow F s‖ := by
      rw [one_mul]
      apply ((star (complexRow F s)).norm_le (norm_nonneg _)).mpr
      intro r
      change ‖star (complexRow F s r)‖≤_
      rw [norm_star]
      exact (complexRow F s).norm_coe_le_norm r
    _ ≤ ‖F‖ := ((complexRow F s).norm_le (norm_nonneg F)).mpr
      (fun r => F.norm_coe_le_norm (halfClamp s,halfClamp r))

/-- The actual continuous kernel image of an arbitrary complex L2 input.
Use: its L2 inclusion is the original source integral operator, rather than an abstract spectral replacement.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
-/
def complexKernelAction (F : C(KernelSquare,ℂ)) : ComplexL2 →L[ℂ] C(Interval,ℂ) :=
  LinearMap.mkContinuous
    { toFun := fun v => ⟨fun s => inner ℂ (complexHilbertRow F s) v,
        (complexHilbertRow F).continuous.inner continuous_const⟩
      map_add' := fun v w => ContinuousMap.ext (fun s => inner_add_right _ v w)
      map_smul' := fun z v => ContinuousMap.ext (fun s => inner_smul_right _ v z) }
    ‖F‖ (fun v => by
      apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg F) (norm_nonneg v))).mpr
      intro s
      exact (norm_inner_le_norm (𝕜 := ℂ) (complexHilbertRow F s) v).trans
        (mul_le_mul_of_nonneg_right (complexHilbertRow_norm F s) (norm_nonneg v)))

/-- The genuine bounded integral operator of the actual continuous physical kernel on complex L2.
Use: its physical prefix compressions are precisely the operators in Appendix E.1.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
-/
def complexKernelOperator (F : C(KernelSquare,ℂ)) : ComplexL2 →L[ℂ] ComplexL2 :=
  ContinuousMap.toLp (𝕜 := ℂ) (p := 2) volume ∘L complexKernelAction F

/-- The actual continuous kernel action is the literal physical integral against the original L2 input.
Use: identifies the compressed operator with I+F_t and its real quadratic form with the previously proved source form.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: unfold the L2 inner product and replace the continuous conjugated row by its genuine almost-everywhere representative; the two conjugations cancel. -/
theorem complexKernelAction_apply (F : C(KernelSquare,ℂ)) (v : ComplexL2) (s : Interval) :
    complexKernelAction F v s=∫ r:Interval,F (halfClamp s,halfClamp r)*v r := by
  -- The conjugation in the Hilbert row cancels the one in the first inner-product entry.
  change inner ℂ (complexHilbertRow F s) v=_
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) volume (star (complexRow F s))] with r hr
  change inner ℂ (ContinuousMap.toLp (𝕜 := ℂ) (p := 2) volume (star (complexRow F s)) r) (v r)=_
  rw [hr,RCLike.inner_apply']
  change star (star (F (halfClamp s,halfClamp r)))*v r=_
  rw [star_star]

/-- The genuine complex kernel operator has norm bounded by the true physical kernel supremum norm.
Use: controls every complex-order perturbation uniformly for all physical prefix domains.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the actual action has the row bound used in its construction; compose with the unit-norm L2 inclusion. -/
theorem complexKernelOperator_norm (F : C(KernelSquare,ℂ)) : ‖complexKernelOperator F‖≤‖F‖ := by
  have ha : ‖complexKernelAction F‖≤‖F‖ := LinearMap.mkContinuous_norm_le _ (norm_nonneg F) _
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul complex_toLp_norm_le ha (norm_nonneg (complexKernelAction F)) (by norm_num)).trans_eq (one_mul _))

/-- The true complex kernel action integrand is integrable for every actual L2 input.
Use: permits linearity under the literal kernel integral when comparing two continued orders.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the input is L1 on the finite original domain and the continuous physical row is bounded by its compact norm. -/
theorem complexRow_integrable (F : C(KernelSquare,ℂ)) (v : ComplexL2) (s : Interval) :
    Integrable (fun r:Interval => F (halfClamp s,halfClamp r)*v r) := by
  have hv := (Lp.memLp v).integrable (by norm_num)
  have hh := hv.mul_bdd (complexRow F s).continuous.aestronglyMeasurable
    (Eventually.of_forall (fun r => (complexRow F s).norm_coe_le_norm r))
  simpa only [complexRow,ContinuousMap.comp_apply,ContinuousMap.curry_apply,mul_comm] using hh

/-- Subtracting the actual physical kernels subtracts their genuine complex L2 integral operators.
Use: bounds the continued operator difference by the actual uniform kernel difference on one common order disk.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: linearity of the integrable row integral identifies the continuous action difference, and the true L2 inclusion preserves subtraction. -/
theorem complexKernelOperator_sub (F G : C(KernelSquare,ℂ)) :
    complexKernelOperator (F-G)=complexKernelOperator F-complexKernelOperator G := by
  -- This equality uses the literal integral formula on every genuine Hilbert input.
  have he : complexKernelAction (F-G)=complexKernelAction F-complexKernelAction G := by
    ext v s
    rw [complexKernelAction_apply]
    change (∫ r:Interval,(F (halfClamp s,halfClamp r)-G (halfClamp s,halfClamp r))*v r)=
      complexKernelAction F v s-complexKernelAction G v s
    simp_rw [sub_mul]
    rw [integral_sub (complexRow_integrable F v s) (complexRow_integrable G v s),
      complexKernelAction_apply,complexKernelAction_apply]
  apply ContinuousLinearMap.ext
  intro v
  change ContinuousMap.toLp (𝕜 := ℂ) (p := 2) volume (complexKernelAction (F-G) v)=_
  rw [he]
  exact map_sub (ContinuousMap.toLp (𝕜 := ℂ) (p := 2) volume) _ _

/-- The original complex kernel bilinear integrand is genuinely integrable on the unchanged product measure.
Use: justifies Fubini and real-part passage in the complexification of the original quadratic form.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: both inputs are L1, conjugation preserves integrability, and their independent-variable product is integrable; multiply by the bounded continuous extended physical kernel. -/
theorem complexKernelBilinear_integrable (F : C(KernelSquare,ℂ)) (v w : ComplexL2) :
    Integrable (fun p:Interval×Interval =>
      (star (w p.1)*v p.2)*F (halfClamp p.1,halfClamp p.2)) (volume.prod volume) := by
  -- Independent-variable L1 factors provide the integrable product before multiplication by F.
  let E : C(Interval×Interval,ℂ) := F.comp
    ⟨fun p => (halfClamp p.1,halfClamp p.2),by fun_prop⟩
  have hw : Integrable (fun s:Interval => star (w s)) :=
    _root_.Complex.conjCLE.toContinuousLinearMap.integrable_comp
      ((Lp.memLp w).integrable (by norm_num))
  exact (hw.mul_prod
    ((Lp.memLp v).integrable (by norm_num))).mul_bdd E.continuous.aestronglyMeasurable
      (Eventually.of_forall (fun p => E.norm_coe_le_norm p))

/-- The genuine complex kernel operator pairing is its literal original double integral.
Use: transfers the proved original real quadratic coercivity to arbitrary complex physical inputs.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: replace the continuous L2 output almost everywhere, insert the proved row integral, pull out its scalar factor, and apply Fubini for the proved integrable product integrand. -/
theorem complexKernelOperator_inner (F : C(KernelSquare,ℂ)) (v w : ComplexL2) :
    inner ℂ w (complexKernelOperator F v)=∫ p:Interval×Interval,
      (star (w p.1)*v p.2)*F (halfClamp p.1,halfClamp p.2) ∂(volume.prod volume) := by
  -- L2 representatives enter only through almost-everywhere identities.
  rw [L2.inner_def,integral_prod _ (complexKernelBilinear_integrable F v w)]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) volume (complexKernelAction F v)] with s hs
  change inner ℂ (w s) (ContinuousMap.toLp (𝕜 := ℂ) (p := 2) volume (complexKernelAction F v) s)=_
  rw [hs,RCLike.inner_apply']
  change star (w s)*complexKernelAction F v s=_
  rw [complexKernelAction_apply,← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall (fun r => by ring)

end
end jacobi.Analytic
