import jacobi.GelfandLevitan.KernelRows

/-!
Article: jacobi, Theorem 2.1.
Pairing the continuous original Hilbert row with an arbitrary genuine
input gives a continuous representative of its kernel image. Fubini
identifies this actual operator with the previously constructed norm
sum. This prevents an implicit assumption that the spectral operator
has the desired pointwise integral kernel.
Use: represents the true continuous original kernel image on the fixed shared unit domain before its actual half-space projection.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set MeasureTheory Filter jacobi.Reference
open scoped Topology InnerProductSpace
attribute [local instance] Measure.Subtype.measureSpace
attribute [local irreducible] kernel

/-- The genuine physical coordinate clamped continuously to the original half interval.
Use: represents the true continuous original kernel image on the fixed shared unit domain before its actual half-space projection.
Article: jacobi, Proposition C.2.
-/
def halfClamp : C(Interval,HalfInterval) where
  toFun s := ⟨halfTime s,halfTime_mem s⟩
  continuous_toFun := halfTime.continuous.subtype_mk _

/-- The continuous original source kernel image represented by genuine Hilbert row pairings.
Use: supplies the pointwise integral representative of F*v needed to reconstruct K from the actual inverse solution row.
Article: jacobi, Theorem 2.1.
-/
def kernelActionMap (a : ℝ) (ha : -1<a) (v : halfSubspace) : C(Interval,ℝ) where
  toFun s := inner ℝ (kernelRowVector a ha (halfClamp s)) v
  continuous_toFun := ((kernelRowVector a ha).continuous.comp halfClamp.continuous).inner continuous_const

/-- The genuine source kernel action as a bounded linear map into actual continuous spatial functions.
Use: its original L2 inclusion can be compared with the already proved compact spectral kernel operator by real polarization.
Article: jacobi, Proposition C.2.
-/
def kernelActionCLM (a : ℝ) (ha : -1<a) : halfSubspace →L[ℝ] C(Interval,ℝ) :=
  LinearMap.mkContinuous
    { toFun := kernelActionMap a ha
      map_add' := by
        intro v w
        apply ContinuousMap.ext
        intro s
        change inner ℝ (kernelRowVector a ha (halfClamp s)) (v+w)=_
        exact inner_add_right _ _ _
      map_smul' := by
        intro r v
        apply ContinuousMap.ext
        intro s
        change inner ℝ (kernelRowVector a ha (halfClamp s)) (r • v)=
          r*inner ℝ (kernelRowVector a ha (halfClamp s)) v
        exact real_inner_smul_right (kernelRowVector a ha (halfClamp s)) v r }
    ‖kernelRowVector a ha‖ (fun v => by
      apply ((kernelActionMap a ha v).norm_le (by positivity)).mpr
      intro s
      exact (norm_inner_le_norm (𝕜 := ℝ) (kernelRowVector a ha (halfClamp s)) v).trans
        (mul_le_mul_of_nonneg_right ((kernelRowVector a ha).norm_coe_le_norm _) (norm_nonneg v)))

/-- The actual integral kernel action included in the original half-domain Hilbert space.
Use: its proven equality with the original norm-sum operator justifies every subsequent pointwise GL reconstruction step.
Article: jacobi, Proposition C.2.
-/
def integralKernelOperator (a : ℝ) (ha : -1<a) : halfSubspace →L[ℝ] halfSubspace :=
  halfSubspace.orthogonalProjectionOnto ∘L
    (ContinuousMap.toLp (𝕜 := ℝ) (p := 2) volume) ∘L kernelActionCLM a ha

/-- The true double source integrand is integrable for two arbitrary original L2 inputs.
Use: Fubini proves the actual integral action symmetric and identifies its quadratic form with the genuine source form already computed spectrally.
Article: jacobi, Proposition C.2.
Proof: both actual inputs are L1 on the finite original domain. Their independent-variable product is integrable and the genuine continuous kernel is bounded by its actual compact norm. -/
theorem kernelBilinear_integrable (a : ℝ) (ha : -1<a) (v w : Space) :
    Integrable (fun p:Interval×Interval =>
      (v p.1*w p.2)*kernel a ha (halfTime p.1) (halfTime p.2)) (volume.prod volume) :=
  ((space_integrable v).mul_prod (space_integrable w)).mul_bdd
    (kernelMap a ha).continuous.aestronglyMeasurable
    (Eventually.of_forall (fun p => (kernelMap a ha).norm_coe_le_norm p))

/-- Pairing the original integral operator is its literal original double spatial integral.
Use: proves true symmetry and the exact quadratic identity, which identify the actual operator with the spectral norm sum.
Article: jacobi, Proposition C.2.
Proof: the genuine half-space projection preserves pairing with the
original input. Its actual continuous L2 representative is the source
row pairing, already identified with the original integral.
Pull the spatial scalar into that integral and apply genuine Fubini. -/
theorem integralKernelOperator_inner (a : ℝ) (ha : -1<a) (v w : halfSubspace) :
    inner ℝ (integralKernelOperator a ha v) w=
      ∫ p:Interval×Interval,((w:Space) p.1*(v:Space) p.2)*
        kernel a ha (halfTime p.1) (halfTime p.2) ∂(volume.prod volume) := by
  -- The actual source quotient map is only replaced by its continuous representative almost everywhere.
  change inner ℝ (halfSubspace.orthogonalProjectionOnto
    (ContinuousMap.toLp (𝕜 := ℝ) (p := 2) volume (kernelActionMap a ha v))) w=_
  rw [halfSubspace.inner_orthogonalProjectionOnto_eq_of_mem_right,L2.inner_def,
    integral_prod _ (kernelBilinear_integrable a ha (w:Space) (v:Space))]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 2) volume (kernelActionMap a ha v)] with s hs
  rw [hs]
  change (w:Space) s*inner ℝ (kernelRowVector a ha (halfClamp s)) v=_
  rw [kernelRowVector_inner,← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall (fun r => by
    change (w:Space) s*((v:Space) r*kernel a ha (halfTime s) (halfTime r)) = _
    ring)

/-- The original integral kernel operator is genuinely symmetric.
Use: real polarization can identify it from its true quadratic form with the source compact spectral operator.
Article: jacobi, Proposition C.2.
Proof: use the proved true double-integral pairing, interchange the
two original spatial coordinates by the community product-measure swap,
and use actual source kernel symmetry. The two genuine integrands then
agree pointwise by commutativity of real multiplication. -/
theorem integralKernelOperator_symmetric (a : ℝ) (ha : -1<a) :
    (integralKernelOperator a ha).IsSymmetric := by
  -- Both pairings are the original source integral, so the coordinate swap changes no spectral data.
  intro v w
  change inner ℝ (integralKernelOperator a ha v) w=inner ℝ v (integralKernelOperator a ha w)
  have hc : inner ℝ v (integralKernelOperator a ha w)=inner ℝ (integralKernelOperator a ha w) v :=
    real_inner_comm _ _
  rw [hc,integralKernelOperator_inner,integralKernelOperator_inner]
  rw [← integral_prod_swap (fun p:Interval×Interval =>
    ((w:Space) p.1*(v:Space) p.2)*kernel a ha (halfTime p.1) (halfTime p.2))]
  apply integral_congr_ae
  exact Eventually.of_forall (fun p => by
    dsimp only [Prod.swap]
    rw [kernel_symmetric]
    ring)

/-- The original integral action is exactly the compact operator constructed from the genuine spectral correction series.
Use: proves that the actual inverse GL solution equation is the original spatial integral equation, rather than merely an equation for an unrelated abstract Hilbert operator.
Article: jacobi, Proposition C.2.
Source: real polarization for symmetric operators.
Proof: the two actual symmetric operators have the same genuine
quadratic form, the original kernel double integral. Their symmetric
difference has identically zero form. The community real polarization
theorem makes that actual difference zero. -/
theorem integralKernelOperator_eq (a : ℝ) (ha : -1<a) :
    integralKernelOperator a ha=kernelOperator a ha := by
  -- Equality is proved for the original operators, not stipulated as a property of a certificate.
  have hs := (integralKernelOperator_symmetric a ha).sub (kernelOperator_symmetric a ha)
  have hz : (integralKernelOperator a ha-kernelOperator a ha).toLinearMap=0 :=
    hs.inner_map_self_eq_zero.mp (fun v => by
      change inner ℝ (integralKernelOperator a ha v-kernelOperator a ha v) v=0
      rw [inner_sub_left,integralKernelOperator_inner,kernelOperator_quadratic]
      exact sub_self _)
  apply sub_eq_zero.mp
  apply ContinuousLinearMap.ext
  intro v
  exact congrArg (fun L:halfSubspace →ₗ[ℝ] halfSubspace => L v) hz

end
end jacobi.GelfandLevitan
