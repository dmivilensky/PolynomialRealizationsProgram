import jacobi.GelfandLevitan.TransformationOperator
import jacobi.GelfandLevitan.FactorizationRows

/-!
Article: jacobi, Proposition C.2.
The triangular Volterra bilinear form is its literal product integral.
Adding its transposed form gives the continuous symmetric triangular
kernel. The diagonal is discarded only after proving that it is null
for the original product Lebesgue measure.
Use: supplies the actual bounded measurable kernel in the Volterra bilinear integral.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set MeasureTheory Filter jacobi.Reference
open scoped Topology InnerProductSpace
attribute [local instance] Measure.Subtype.measureSpace
attribute [local irreducible] transformationKernel kernel solutionRow

/-- The original GL kernel on the fixed compact product domain.
Use: supplies the actual bounded measurable kernel in the Volterra bilinear integral.
Article: jacobi, Proposition C.2.
-/
def transformationKernelMap (a : ℝ) (ha : -1<a) : C(Interval×Interval,ℝ) :=
  ⟨fun p => transformationKernel a ha (halfClamp p.1) (halfClamp p.2),
    (transformationKernel_continuous a ha).comp
      ((halfClamp.continuous.comp continuous_fst).prodMk (halfClamp.continuous.comp continuous_snd))⟩

/-- The measurable lower triangle in the unchanged physical coordinate square.
Use: its indicator is the causal kernel in transformationOperator_bilinear.
Article: jacobi, Proposition C.2.
-/
def lowerTriangle : Set (Interval×Interval) := {p | (p.2:ℝ)≤(p.1:ℝ)}

/-- The original physical lower triangle is measurable.
Use: its indicator preserves the integrable bounded-kernel bilinear form.
Article: jacobi, Proposition C.2.
Proof: it is the closed comparison set of the two continuous physical coordinates. -/
theorem lowerTriangle_measurable : MeasurableSet lowerTriangle :=
  (isClosed_le (continuous_subtype_val.comp continuous_snd)
    (continuous_subtype_val.comp continuous_fst)).measurableSet

/-- The actual causal transformation kernel, with an immaterial closed diagonal.
Use: represents the original Volterra operator and its adjoint in product integrals.
Article: jacobi, Proposition C.2.
-/
def causalTransformationKernel (a : ℝ) (ha : -1<a) : Interval×Interval → ℝ :=
  lowerTriangle.indicator (transformationKernelMap a ha)

/-- The original triangular bilinear kernel is integrable for arbitrary actual L2 inputs.
Use: Fubini and transposition in the factorization require this genuine product-integrability assertion.
Article: jacobi, Proposition C.2.
Proof: multiply the independent-variable L1 product by the actual bounded continuous K, then take its measurable triangular indicator. -/
theorem causalTransformation_integrable (a : ℝ) (ha : -1<a) (v w : halfSubspace) :
    Integrable (fun p:Interval×Interval =>
      ((v:Space) p.1*(w:Space) p.2)*causalTransformationKernel a ha p)
      (volume.prod volume) := by
  -- Restriction to the original measurable triangle preserves the independent-variable integrable majorant.
  have h := (((space_integrable (v:Space)).mul_prod (space_integrable (w:Space))).mul_bdd
    (transformationKernelMap a ha).continuous.aestronglyMeasurable
    (Eventually.of_forall (transformationKernelMap a ha).norm_coe_le_norm)).indicator
      lowerTriangle_measurable
  convert h using 1
  funext p
  by_cases hp : p∈lowerTriangle
  · simp only [causalTransformationKernel,indicator_of_mem hp]
  · simp only [causalTransformationKernel,indicator_of_notMem hp,mul_zero]

/-- Pairing the original Volterra operator is its genuine causal product-kernel integral.
Use: adds the transposed operator form in the GL covariance factorization.
Article: jacobi, Proposition C.2.
Proof: use the actual continuous representative of its output and the literal prefix integral. Fubini is justified by the independent product-integrability bound. Outside the original half interval the testing input is zero almost everywhere. -/
theorem transformationOperator_bilinear (a : ℝ) (ha : -1<a) (v w : halfSubspace) :
    inner ℝ (transformationOperator a ha v) w=
      ∫ p:Interval×Interval,((w:Space) p.1*(v:Space) p.2)*
        causalTransformationKernel a ha p ∂(volume.prod volume) := by
  -- The only replacement outside the actual half domain is multiplied by the genuine zero-extended test vector.
  change inner ℝ (halfSubspace.orthogonalProjectionOnto
    (ContinuousMap.toLp (𝕜 := ℝ) (p := 2) volume (transformationActionMap a ha v))) w=_
  rw [halfSubspace.inner_orthogonalProjectionOnto_eq_of_mem_right,L2.inner_def,
    integral_prod _ (causalTransformation_integrable a ha w v)]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 2) volume (transformationActionMap a ha v),
    halfSubspace_supported w] with t ht hw
  rw [ht]
  change (w:Space) t*transformationActionMap a ha v t=_
  by_cases hp : (t:ℝ)≤1/2
  · rw [transformationActionMap_integral,← integral_const_mul,
      ← integral_indicator (prefixSet_measurable (halfTime t))]
    apply integral_congr_ae
    exact Eventually.of_forall (fun s => by
      have hc : halfTime t=(t:ℝ) := min_eq_left hp
      dsimp only
      rw [hc]
      by_cases hst : (s:ℝ)≤(t:ℝ)
      · rw [indicator_of_mem (show s∈prefixSet (t:ℝ) from hst)]
        simp only [causalTransformationKernel,indicator_of_mem (show (t,s)∈lowerTriangle from hst),
          transformationKernelMap,ContinuousMap.coe_mk]
        ring
      · rw [indicator_of_notMem (show s∉prefixSet (t:ℝ) from hst)]
        simp only [causalTransformationKernel,indicator_of_notMem (show (t,s)∉lowerTriangle from hst),mul_zero])
  · rw [hw (lt_of_not_ge hp),zero_mul]
    symm
    apply integral_eq_zero_of_ae
    exact Eventually.of_forall (fun s => by dsimp only; rw [zero_mul,zero_mul,Pi.zero_apply])

/-- Almost every original coordinate pair is off the diagonal.
Use: replaces the sum of the two causal kernels by the symmetric triangular kernel without assigning a false diagonal identity.
Article: jacobi, Proposition C.2.
Source: atomless Lebesgue measure and Fubini.
Proof: each vertical section of the diagonal is a singleton of measure zero. -/
theorem physicalSquare_offDiagonal :
    ∀ᵐ p:Interval×Interval ∂(volume.prod volume),p.1≠p.2 := by
  apply (Measure.ae_prod_iff_ae_ae
    (isClosed_eq continuous_fst continuous_snd).measurableSet.compl).mpr
  exact Eventually.of_forall (fun t => (volume.ae_ne t).mono (fun _ h => h.symm))

/-- The two genuine causal kernels sum to the symmetric triangular kernel off the diagonal.
Use: combines the K and K* forms in the actual GL covariance cancellation.
Article: jacobi, Proposition C.2.
Proof: sort the original coordinates. Their continuous clamps preserve order, so exactly one of the two causal indicators contributes. -/
theorem causalTransformation_add_swap (a : ℝ) (ha : -1<a) (t s : Interval) (hne : t≠s) :
    causalTransformationKernel a ha (t,s)+causalTransformationKernel a ha (s,t)=
      symmetricTransformationKernel a ha (halfClamp t) (halfClamp s) := by
  -- The closed indicators overlap only on the excluded original diagonal.
  have hc : Monotone halfClamp := fun _ _ h => min_le_min_right (1/2:ℝ) h
  have hval : (t:ℝ)≠(s:ℝ) := fun h => hne (Subtype.ext h)
  unfold causalTransformationKernel symmetricTransformationKernel
  rcases lt_or_gt_of_ne hval with hts|hst
  · rw [indicator_of_notMem (show (t,s)∉lowerTriangle from not_le.mpr hts),
      indicator_of_mem (show (s,t)∈lowerTriangle from hts.le),zero_add,
      max_eq_right (hc hts.le),min_eq_left (hc hts.le)]
    rfl
  · rw [indicator_of_mem (show (t,s)∈lowerTriangle from hst.le),
      indicator_of_notMem (show (s,t)∉lowerTriangle from not_le.mpr hst),add_zero,
      max_eq_left (hc hst.le),min_eq_right (hc hst.le)]
    rfl

/-- Twice the actual Volterra quadratic form is the integral against the symmetric triangular kernel.
Use: supplies the K+K* term in the original GL factorization quadratic form.
Article: jacobi, Proposition C.2.
Proof: transpose a copy of the genuine causal product integral, add the integrable forms, and use the proved null diagonal to identify the actual symmetric kernel. -/
theorem transformationOperator_quadratic_twice (a : ℝ) (ha : -1<a) (v : halfSubspace) :
    2*inner ℝ (transformationOperator a ha v) v=
      ∫ p:Interval×Interval,((v:Space) p.1*(v:Space) p.2)*
        symmetricTransformationKernel a ha (halfClamp p.1) (halfClamp p.2) ∂(volume.prod volume) := by
  -- Product-coordinate swapping preserves the original Lebesgue measure and keeps the true input unchanged.
  have hs := (causalTransformation_integrable a ha v v).swap
  rw [transformationOperator_bilinear,two_mul]
  conv_lhs => arg 2; rw [← integral_prod_swap]
  dsimp only [Function.comp_def,Prod.swap,Prod.fst,Prod.snd] at hs ⊢
  rw [← integral_add (causalTransformation_integrable a ha v v) hs]
  apply integral_congr_ae
  filter_upwards [physicalSquare_offDiagonal] with p hp
  rw [mul_comm ((v:Space) p.2) ((v:Space) p.1),← mul_add,
    causalTransformation_add_swap a ha p.1 p.2 hp]

end
end jacobi.GelfandLevitan
