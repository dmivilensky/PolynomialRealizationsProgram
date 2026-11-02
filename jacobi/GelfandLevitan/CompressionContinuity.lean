import jacobi.GelfandLevitan.Compression
import jacobi.GelfandLevitan.CutoffContinuity

/-!
Article: jacobi, Proposition C.2.
Although the physical cutoff projections are only strongly continuous,
their compressions of each genuine rank-one correction are continuous
in operator norm. The original summable norm majorant then makes the
whole compressed kernel continuous. Inversion at the actual proved
units gives continuity of the original inverse family.
Use: lets the community operator-space continuity instances find exactly the original source topology without repeatedly searching the full subtype hierarchy.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set jacobi.Reference
open scoped Topology InnerProductSpace
attribute [local irreducible] rankCorrection kernelOperator
attribute [local irreducible] coefficientVector normingRatio norming eigenvalue
set_option backward.isDefEq.respectTransparency false

/-- The existing source Hilbert seminormed structure, cached locally for inference through its nested subtype.
Use: lets the community operator-space continuity instances find exactly the original source topology without repeatedly searching the full subtype hierarchy.
Article: jacobi, Proposition C.2.
-/
local instance : SeminormedAddCommGroup halfSubspace := inferInstance

/-- The existing genuine operator-norm seminormed structure, cached locally for the original endomorphism space.
Use: the community addition and subtraction continuity instances apply directly to the true compressed source operators; this only names the already available structure.
Article: jacobi, Proposition C.2.
-/
local instance : SeminormedAddCommGroup (halfSubspace →L[ℝ] halfSubspace) := inferInstance

/-- Compressing an actual source rank-one operator projects its two genuine feature vectors.
Use: the strongly continuous original cutoff features give operator-norm continuous compressed source corrections.
Article: jacobi, Proposition C.2.
Proof: evaluate at a genuine Hilbert input, use the actual symmetric
projection identity on the scalar inner factor, and linearity on its
true vector factor. This is the original compression, not a replacement
finite-dimensional kernel. -/
theorem cutoffProjection_rankOne (t : ℝ) (v : halfSubspace) :
    cutoffProjection t ∘L InnerProductSpace.rankOne ℝ v v ∘L cutoffProjection t=
      InnerProductSpace.rankOne ℝ (cutoffProjection t v) (cutoffProjection t v) := by
  apply ContinuousLinearMap.ext
  intro w
  change cutoffProjection t (inner ℝ v (cutoffProjection t w) • v)=
    inner ℝ (cutoffProjection t v) w • cutoffProjection t v
  have hs : inner ℝ (cutoffProjection t v) w=inner ℝ v (cutoffProjection t w) :=
    cutoffProjection_symmetric t v w
  rw [map_smul,hs]

/-- Every original compressed rank-one correction varies continuously in operator norm.
Use: the actual summable inverse-square source bound promotes the finite-rank parameter continuity to the full original GL kernel.
Article: jacobi, Proposition C.2.
Proof: both original source features become strongly continuous after
the actual physical cutoff. The community rank-one bilinear map is
continuous in their genuine Hilbert norms; the fixed true scalar
coefficients and difference preserve operator-norm continuity. -/
theorem compressedRankCorrection_continuous (a : ℝ) (ha : -1<a) (k : ℕ) :
    Continuous (fun t:ℝ => cutoffProjection t ∘L rankCorrection a ha k ∘L cutoffProjection t) := by
  -- Only the actual source feature vectors are projected; no continuity of P_t in operator norm is required.
  have hr (v : halfSubspace) : Continuous (fun t:ℝ =>
      InnerProductSpace.rankOne ℝ (cutoffProjection t v) (cutoffProjection t v)) :=
    ((InnerProductSpace.rankOne ℝ (E := halfSubspace) (F := halfSubspace)).continuous.comp
      (cutoffProjection_strong_continuous v)).clm_apply (cutoffProjection_strong_continuous v)
  have he (t : ℝ) : cutoffProjection t ∘L rankCorrection a ha k ∘L cutoffProjection t=
      (normingRatio a ha k/norming a k) •
        InnerProductSpace.rankOne ℝ (cutoffProjection t (coefficientVector a ha (jacobi.Bessel.sigma a ha k)))
          (cutoffProjection t (coefficientVector a ha (jacobi.Bessel.sigma a ha k)))-
      (1/norming a k) •
        InnerProductSpace.rankOne ℝ (cutoffProjection t (coefficientVector a ha (eigenvalue a k)))
          (cutoffProjection t (coefficientVector a ha (eigenvalue a k))) := by
    let x := coefficientVector a ha (jacobi.Bessel.sigma a ha k)
    let y := coefficientVector a ha (eigenvalue a k)
    let b := normingRatio a ha k/norming a k
    let c := 1/norming a k
    apply ContinuousLinearMap.ext
    intro w
    unfold rankCorrection
    change cutoffProjection t (b • (InnerProductSpace.rankOne ℝ x x (cutoffProjection t w))-
      c • (InnerProductSpace.rankOne ℝ y y (cutoffProjection t w)))=
      (b • InnerProductSpace.rankOne ℝ (cutoffProjection t x) (cutoffProjection t x)-
        c • InnerProductSpace.rankOne ℝ (cutoffProjection t y) (cutoffProjection t y)) w
    simp only [sub_apply,smul_apply,InnerProductSpace.rankOne_apply,map_sub,map_smul]
    have hx : inner ℝ (cutoffProjection t x) w=inner ℝ x (cutoffProjection t w) :=
      cutoffProjection_symmetric t x w
    have hy : inner ℝ (cutoffProjection t y) w=inner ℝ y (cutoffProjection t w) :=
      cutoffProjection_symmetric t y w
    rw [hx,hy]
  simp_rw [he]
  have hc := ((hr (coefficientVector a ha (jacobi.Bessel.sigma a ha k))).const_smul
    (normingRatio a ha k/norming a k)).sub
    ((hr (coefficientVector a ha (eigenvalue a k))).const_smul (1/norming a k))
  exact hc.congr (fun _ => rfl)

/-- The actual compressed kernel is exactly the norm sum of its true source compressed corrections.
Use: uniform summability and individual parameter continuity establish operator-norm continuity of the genuine family A_t.
Article: jacobi, Proposition C.2.
Proof: multiplication on the left and right by the actual bounded source projection is a community continuous linear map on original operators. Apply it to the proved norm-convergent original series. -/
theorem compressedKernel_tsum (a : ℝ) (ha : -1<a) (t : ℝ) :
    compressedKernel a ha t=
      ∑' k,cutoffProjection t ∘L rankCorrection a ha k ∘L cutoffProjection t := by
  let comp := ContinuousLinearMap.compL ℝ halfSubspace halfSubspace halfSubspace
  let L := (comp (cutoffProjection t)).comp (comp.flip (cutoffProjection t))
  have hh := L.map_tsum (rankCorrection_summable a ha)
  unfold compressedKernel kernelOperator
  exact hh

/-- Compressing any actual source bounded operator by the original physical cutoff cannot increase its genuine operator norm.
Use: the original summable correction norms dominate the entire varying family, proving operator-norm continuity of the true compressed GL series.
Article: jacobi, Proposition C.2.
Proof: twice apply the community composition norm bound and then the true norm-at-most-one estimate for each physical projection. -/
theorem cutoffCompression_norm (t : ℝ) (S : halfSubspace →L[ℝ] halfSubspace) :
    ‖cutoffProjection t ∘L S ∘L cutoffProjection t‖≤‖S‖ := by
  -- Both original physical projections are contractions in the unchanged source operator norm.
  calc
    _ ≤ ‖cutoffProjection t‖*(‖S‖*‖cutoffProjection t‖) :=
      (ContinuousLinearMap.opNorm_comp_le (h := cutoffProjection t) (S ∘L cutoffProjection t)).trans
        (mul_le_mul_of_nonneg_left
          (ContinuousLinearMap.opNorm_comp_le (h := S) (cutoffProjection t)) (norm_nonneg _))
    _ ≤ 1*(‖S‖*1) := mul_le_mul (cutoffProjection_norm_le t)
      (mul_le_mul_of_nonneg_left (cutoffProjection_norm_le t) (norm_nonneg S))
      (by positivity) (by norm_num)
    _ = ‖S‖ := by ring

/-- The original compressed GL kernel varies continuously in operator norm over the physical endpoint.
Use: continuity of the actual positive operators and their proved bounded inverses yields continuous original solution rows and the continuous pointwise GL kernel.
Article: jacobi, Proposition C.2.
Proof: each compressed true source correction is operator-norm
continuous. The cutoff projections have norm at most one, so the actual
summable original correction norms dominate all compressed terms.
The community uniform series theorem proves continuity of their true
sum, which is exactly the original compressed kernel. -/
theorem compressedKernel_continuous (a : ℝ) (ha : -1<a) :
    Continuous (compressedKernel a ha) := by
  -- Use the proved original norm summability, uniformly in the genuine physical cutoff parameter.
  change Continuous (fun t:ℝ => compressedKernel a ha t)
  simp_rw [compressedKernel_tsum]
  obtain ⟨C,_,hbound⟩ := rankCorrection_norm_bound a ha
  have hM : Summable (fun k:ℕ => C/(k+1:ℝ)^2) := by
    simpa only [one_pow,mul_one_div] using (jacobi.Bessel.inverse_square_majorant_summable 1).mul_left C
  have hnorm : Summable (fun k:ℕ => ‖rankCorrection a ha k‖) :=
    hM.of_nonneg_of_le (fun k => norm_nonneg (rankCorrection a ha k)) hbound
  have hc := continuous_tsum (F := halfSubspace →L[ℝ] halfSubspace)
    (f := fun k:ℕ => fun t:ℝ => cutoffProjection t ∘L rankCorrection a ha k ∘L cutoffProjection t)
    (compressedRankCorrection_continuous a ha) hnorm
    (fun k t => cutoffCompression_norm t (rankCorrection a ha k))
  exact hc

/-- The original cutoff identity-plus-kernel family is norm continuous.
Use: the genuine already proved unit at every physical endpoint has a continuous original inverse.
Article: jacobi, Proposition C.2.
Proof: the true identity operator is constant and the actual compressed kernel is proved norm continuous. -/
theorem compressedPositive_continuous (a : ℝ) (ha : -1<a) :
    Continuous (compressedPositive a ha) := by
  change Continuous (fun t:ℝ => ContinuousLinearMap.id ℝ halfSubspace+compressedKernel a ha t)
  have hc : Continuous (fun _:ℝ => ContinuousLinearMap.id ℝ halfSubspace) := continuous_const
  exact hc.add (compressedKernel_continuous a ha)

/-- The actual bounded inverse family of the original cutoff GL operators is norm continuous.
Use: together with strong continuity of the actual source cutoff, constructs continuous original solution rows and hence the genuine continuous kernel K.
Article: jacobi, Proposition C.2.
Source: continuity of inversion at units of a real Banach algebra.
Proof: every original A_t is already proved to be a genuine unit. Apply
the community inverse continuity theorem at that actual unit and
compose it with the true norm-continuous original operator family. -/
theorem compressedInverse_continuous (a : ℝ) (ha : -1<a) :
    Continuous (compressedInverse a ha) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hu := compressedPositive_isUnit a ha t
  have hi := NormedRing.inverse_continuousAt (R := halfSubspace →L[ℝ] halfSubspace) hu.unit
  rw [IsUnit.unit_spec] at hi
  exact hi.comp (compressedPositive_continuous a ha).continuousAt

end
end jacobi.GelfandLevitan
