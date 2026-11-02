import jacobi.Analytic.ReferenceSpectralMaps
import jacobi.GelfandLevitan.TransformedSolution

/-!
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
The physical GL transformation is bounded bilinear in its genuine
continuous kernel and reference vector. Applying it to the proved
analytic inverse and actual spectral reference function gives the
original norm-holomorphic transformed spectral vectors.
Use: embeds a reference vector as the actual column f(r) in the GL prefix product.
-/
namespace jacobi.Analytic
noncomputable section
open Set Metric MeasureTheory jacobi.Reference jacobi.GelfandLevitan jacobi.ComplexReference
open scoped Topology
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The continuous first physical coordinate of the original half square.
Use: embeds a reference vector as the actual column f(r) in the GL prefix product.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
-/
def columnProjection : C(KernelSquare,HalfInterval) := ⟨Prod.fst,continuous_fst⟩

/-- The continuous physical row at zero second coordinate.
Use: extracts the original transformation integral from its constant-column prefix product.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
-/
def zeroRowInclusion : C(HalfInterval,KernelSquare) :=
  ⟨fun t => (t,halfZero),continuous_id.prodMk continuous_const⟩

/-- The original continuous GL transformation of a physical reference vector.
Use: defines the same actual u(t,sigma_k) while keeping fixed continuous-function Banach spaces for holomorphy.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
-/
def transformReference (K : C(KernelSquare,ℂ)) (f : C(HalfInterval,ℂ)) : C(HalfInterval,ℂ) :=
  f+(prefixProduct K (f.comp columnProjection)).comp zeroRowInclusion

/-- The continuous GL transform evaluates to the literal original physical-prefix integral.
Use: verifies the exact source formula and real identification of the continued transformed waves.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: evaluate the zero row of the actual prefix product. Its second kernel is the unchanged reference column, so the proved subtype prefix formula is precisely the original transformation integral. -/
theorem transformReference_apply (K : C(KernelSquare,ℂ)) (f : C(HalfInterval,ℂ)) (t : HalfInterval) :
    transformReference K f t=f t+∫ r : Interval in prefixSet (t:ℝ),K (t,halfClamp r)*f (halfClamp r) := by
  change f t+prefixProduct K (f.comp columnProjection) (t,halfZero)=_
  rw [prefixProduct_subtype]
  rfl

/-- Continuous precomposition cannot increase the original supremum norm.
Use: bounds the actual GL column insertion and physical row extraction in the transformed spectral vector estimate.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Source: the supremum norm on continuous functions on compact spaces.
Proof: every composed point value is an original point value and is bounded by the original supremum norm. -/
theorem continuousMap_norm_comp_le {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [CompactSpace Y] (f : C(Y,ℂ)) (g : C(X,Y)) : ‖f.comp g‖≤‖f‖ :=
  (ContinuousMap.norm_le _ (norm_nonneg _)).mpr (fun x => f.norm_coe_le_norm (g x))

/-- The genuine continuous GL transform has norm at most (1+norm K) times the original reference norm.
Use: retains the same spectral index power after transformation, so it cancels the original reference norm in the analytic profile series.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: use the triangle inequality, the proved actual bilinear prefix norm bound and the supremum-norm contraction of the unchanged column and row coordinate maps. -/
theorem transformReference_norm_le (K : C(KernelSquare,ℂ)) (f : C(HalfInterval,ℂ)) :
    ‖transformReference K f‖≤(1+‖K‖)*‖f‖ := by
  calc
    _ ≤ ‖f‖+‖(prefixProduct K (f.comp columnProjection)).comp zeroRowInclusion‖ := norm_add_le _ _
    _ ≤ ‖f‖+‖K‖*‖f‖ := by
      have hh := (continuousMap_norm_comp_le (prefixProduct K (f.comp columnProjection)) zeroRowInclusion).trans ((prefixProduct_norm_le _ _).trans
        (mul_le_mul_of_nonneg_left (continuousMap_norm_comp_le _ _) (norm_nonneg _)))
      linarith
    _ = _ := by ring

/-- Applying the actual continuous GL transformation to two holomorphic Banach-valued parameter curves gives a holomorphic transformed curve.
Use: proves original complex-order holomorphy of u at every genuine spectral branch.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: column insertion and zero-row extraction are bounded complex-linear maps. The actual kernel-to-prefix-operator map is also bounded linear. Compose these maps with the analytic curves and use bounded operator evaluation for the bilinear prefix integral. -/
theorem transformReference_holomorphic {K : ℂ → C(KernelSquare,ℂ)} {f : ℂ → C(HalfInterval,ℂ)}
    {U : Set ℂ} (hK : DifferentiableOn ℂ K U) (hf : DifferentiableOn ℂ f U) :
    DifferentiableOn ℂ (fun a => transformReference (K a) (f a)) U := by
  -- All integral operations are the proved bounded maps for the original physical prefix.
  intro a ha
  let col := ContinuousMap.compCLM ℂ ℂ columnProjection
  let row := ContinuousMap.compCLM ℂ ℂ zeroRowInclusion
  have hc := col.differentiableAt.comp_differentiableWithinAt
    (F := C(HalfInterval,ℂ)) (G := C(KernelSquare,ℂ)) a (hf a ha)
  have hP0 := ContinuousLinearMap.differentiableAt (𝕜 := ℂ) (E := C(KernelSquare,ℂ))
    (F := C(KernelSquare,ℂ) →L[ℂ] C(KernelSquare,ℂ)) (prefixOperators (𝕜 := ℂ)) (x := col (f a))
  have hP := hP0.comp_differentiableWithinAt (F := C(KernelSquare,ℂ))
    (G := C(KernelSquare,ℂ) →L[ℂ] C(KernelSquare,ℂ)) a hc
  have hB := hP.clm_apply (hK a ha)
  convert! (hf a ha).add (row.differentiableAt.comp_differentiableWithinAt
    (F := C(KernelSquare,ℂ)) (G := C(HalfInterval,ℂ)) a hB) using 1

/-- The original transformed spectral reference vector at the actual continued Bessel energy.
Use: defines the genuine analytic squared profiles and their persymmetric energy.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
-/
def OrderDisk.transformedMap {a0 : ℝ} (D : OrderDisk a0) (k : ℕ) (a : ℂ) : C(HalfInterval,ℂ) :=
  transformReference (D.GLsolution a) (D.referenceMap k a)

/-- The actual transformed spectral vectors are holomorphic in the physical continuous-function norm on each genuine inverse subdisk.
Use: their actual squares are the analytic terms of the original persymmetric profile series.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: both original factors are proved Banach holomorphic on the same disk; apply the genuine bounded bilinear transformation theorem. -/
theorem OrderDisk.transformedMap_holomorphic {a0 r : ℝ} (D : OrderDisk a0) (hrD : r≤D.radius)
    (hunit : ∀ a∈ball (a0:ℂ) r,IsUnit (D.GLoperator a)) (k : ℕ) :
    DifferentiableOn ℂ (D.transformedMap k) (ball (a0:ℂ) r) :=
  transformReference_holomorphic (D.GLsolution_holomorphic hrD hunit)
    ((D.referenceMap_holomorphic k).mono (ball_subset_ball hrD))

/-- The genuine transformed spectral vectors retain the full original index-power norm bound wherever the true GL kernel is uniformly bounded.
Use: gives the summable actual squared-profile majorant after cancellation against the original reference norm.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the original reference vectors have a proved all-index amplitude bound. Apply the actual GL norm estimate and its supplied genuine kernel bound; the factor (1+norm K) is uniform in order and index. -/
theorem OrderDisk.transformedMap_bounds {a0 r B : ℝ} (D : OrderDisk a0) (hrD : r≤D.radius)
    (hB : 0<B) (hbound : ∀ a : ℂ,‖a-(a0:ℂ)‖≤r → ‖D.GLsolution a‖≤B) :
    ∃ C : ℝ,0<C ∧ ∀ a : ℂ,‖a-(a0:ℂ)‖≤r → ∀ k : ℕ,
      ‖D.transformedMap k a‖≤C/(k+1:ℝ)^(gamma a).re := by
  obtain ⟨A,hA,href⟩ := D.referenceMap_bounds
  refine ⟨(1+B)*A,by positivity,fun a ha k => ?_⟩
  have hh := transformReference_norm_le (D.GLsolution a) (D.referenceMap k a)
  have hplus : 1+‖D.GLsolution a‖≤1+B := by linarith [hbound a ha]
  have hm := mul_le_mul hplus
    (href a (ha.trans hrD) k) (norm_nonneg _) (by linarith : 0≤1+B)
  exact hh.trans (hm.trans_eq (by ring))

/-- At every real disk order the actual spectral reference vector equals the original real-order reference function at the same numbered energy.
Use: identifies the analytic transformed solution and the original squared spectral profile term by term.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the actual spectral branch has its proved original real zero, and the continued energy solution has its exact original real-order value at the unchanged physical point. -/
theorem OrderDisk.referenceMap_real {a0 b : ℝ} (D : OrderDisk a0) (hb : -1<b)
    (hbd : ‖(b:ℂ)-(a0:ℂ)‖≤D.radius) (k : ℕ) (t : HalfInterval) :
    D.referenceMap k (b:ℂ) t= jacobi.Reference.solution b (jacobi.Bessel.sigma b hb k:ℂ) (t:ℝ) := by
  rw [D.referenceMap_apply hbd k t,D.real_eq b hb hbd k,
    jacobi.ComplexReference.solution_real b _ ⟨t.property.1,by linarith [t.property.2]⟩]

/-- The actual continued transformed spectral vector restricts exactly to the original real GL-transformed solution at the same numbered Bessel energy.
Use: verifies the genuine original real profiles and persymmetric energy, including the actual physical integration measure.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: both constructions have the proved literal reference-plus-prefix-integral formula. Their genuine reference factors and full-square GL kernels have exact original real values; substitute those equalities in the unchanged physical integral. -/
theorem OrderDisk.transformedMap_real {a0 b : ℝ} (D : OrderDisk a0) (hb : -1<b)
    (hbd : ‖(b:ℂ)-(a0:ℂ)‖≤D.radius) (k : ℕ) (t : HalfInterval) :
    D.transformedMap k (b:ℂ) t=transformedSolution b hb t (jacobi.Bessel.sigma b hb k:ℂ) := by
  -- The comparison is between the original actual integral formulas, including every finite spectral index.
  rw [OrderDisk.transformedMap,transformReference_apply,D.referenceMap_real hb hbd,
    transformedSolution_integral]
  congr 1
  apply setIntegral_congr_fun (prefixSet_measurable _)
  intro r _
  have hK : D.GLsolution (b:ℂ) (t,halfClamp r)=
      (transformationKernel b hb t (halfClamp r):ℂ) :=
    congrArg (fun f : C(KernelSquare,ℂ) => f (t,halfClamp r)) (D.GLsolution_real hb hbd)
  dsimp only
  rw [hK,D.referenceMap_real hb hbd]
  rfl

end
end jacobi.Analytic
