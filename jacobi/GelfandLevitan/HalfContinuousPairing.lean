import jacobi.GelfandLevitan.TransformedHilbertGreen
import jacobi.Reference.ContinuousExpansion

/-!
Article: jacobi, Proposition C.2.
Complex continuous waves are tested against the actual real half-interval
Hilbert space by taking their real and imaginary parts. Almost-everywhere
vanishing fixes every point of the physical half interval by continuity.
These bridges let the two proved real bases exclude additional complex
characteristic zeros.
Use: half_complex_pairing_total turns completeness of the real transformed basis into pointwise vanishing of a complex wave.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set MeasureTheory Filter jacobi.Reference
open scoped Topology InnerProductSpace
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false

/-- A continuous wave whose genuine half-space vector vanishes is zero at every physical half-interval point.
Use: half_complex_pairing_total turns completeness of the real transformed basis into pointwise vanishing of a complex wave.
Article: jacobi, Proposition C.2.
Source: uniqueness of continuous representatives on a nondegenerate Lebesgue interval, mathlib Measure.eqOn_Icc_of_ae_eq.
Proof: insert the actual projected continuous representative, transfer its prefix almost-everywhere identity to real Lebesgue measure, and use continuity on the closed half interval, including both endpoints. -/
theorem rowEmbedding_zero_on_half (f : C(Interval,ℝ)) (hf : rowEmbedding f=0)
    (t : HalfInterval) : f (halfInclusion t)=0 := by
  -- The measure restriction is the physical half interval; no value of an L2 equivalence class is evaluated at an endpoint.
  have hAE := halfProjection_toLp_ae f
  change (rowEmbedding f:Space)=ᵐ[volume] _ at hAE
  rw [hf] at hAE
  change (0:Space)=ᵐ[volume] _ at hAE
  have hzero := (Lp.coeFn_zero ℝ 2 (volume : Measure Interval)).symm.trans hAE
  have hu : ∀ᵐ r:Interval, (r:ℝ)≤(1/2:ℝ) → f r=0 := by
    filter_upwards [hzero] with r hr hp
    rw [indicator_of_mem (show r∈prefixSet (1/2) from hp)] at hr
    exact hr.symm
  let P : ℝ → Interval := Set.projIcc 0 1 (by norm_num)
  have hreal : ∀ᵐ x ∂volume.restrict (Icc (0:ℝ) 1),
      x≤(1/2:ℝ) → f (P x)=0 := by
    apply (ae_restrict_iff_subtype measurableSet_Icc).mpr
    filter_upwards [hu] with r hr
    simpa only [P,Set.projIcc_of_mem (by norm_num : (0:ℝ)≤1) r.property] using hr
  have hsmall := ae_restrict_of_ae_restrict_of_subset
    (show Icc (0:ℝ) (1/2)⊆Icc (0:ℝ) 1 from fun _ hx => ⟨hx.1,by linarith [hx.2]⟩) hreal
  have he : (fun x => f (P x))=ᵐ[volume.restrict (Icc (0:ℝ) (1/2))] (fun _ => 0) := by
    filter_upwards [hsmall,ae_restrict_mem measurableSet_Icc] with x hx hmem
    exact hx hmem.2
  have hpoint := Measure.eqOn_Icc_of_ae_eq volume (by norm_num : (0:ℝ)≠1/2) he
    (f.continuous.comp (show Continuous P from continuous_projIcc)).continuousOn continuousOn_const
  have hp : P (t:ℝ)=halfInclusion t :=
    Set.projIcc_of_mem (by norm_num : (0:ℝ)≤1) (halfInclusion t).property
  simpa only [hp] using hpoint t.property

/-- The real part of a continuous complex physical wave.
Use: half_complex_pairing_total tests its actual half-space vector against the original real Hilbert basis.
Article: jacobi, Proposition C.2.
-/
def waveRealPart (W : C(Interval,ℂ)) : C(Interval,ℝ) :=
  ⟨fun t => (W t).re,Complex.continuous_re.comp W.continuous⟩

/-- The imaginary part of a continuous complex physical wave.
Use: half_complex_pairing_total tests its actual half-space vector against the original real Hilbert basis.
Article: jacobi, Proposition C.2.
-/
def waveImagPart (W : C(Interval,ℂ)) : C(Interval,ℝ) :=
  ⟨fun t => (W t).im,Complex.continuous_im.comp W.continuous⟩

/-- The real part of the genuine complex integral is exactly the real Hilbert pairing with the embedded real wave.
Use: half_complex_pairing_total applies real completeness to an arbitrary complex-energy solution.
Article: jacobi, Proposition C.2.
Proof: the original row embedding has its actual integral pairing; bounded real-part projection commutes with the genuinely integrable coefficient integral. -/
theorem waveRealPart_pairing (W : C(Interval,ℂ)) (v : halfSubspace) :
    inner ℝ (rowEmbedding (waveRealPart W)) v=(coefficientFunctional (v:Space) W).re := by
  rw [rowEmbedding_inner]
  change (∫ r:Interval,(v:Space) r*(W r).re)=(∫ r:Interval,((v:Space) r:ℂ)*W r).re
  simpa only [waveRealPart,ContinuousMap.coe_mk,RCLike.re_eq_complex_re,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using
    integral_re (coefficient_integrable (v:Space) W)

/-- The imaginary part of the genuine complex integral is exactly the real Hilbert pairing with the embedded imaginary wave.
Use: half_complex_pairing_total applies real completeness to an arbitrary complex-energy solution.
Article: jacobi, Proposition C.2.
Proof: the actual embedding pairing is the original integral; bounded imaginary-part projection commutes with that integrable complex integral. -/
theorem waveImagPart_pairing (W : C(Interval,ℂ)) (v : halfSubspace) :
    inner ℝ (rowEmbedding (waveImagPart W)) v=(coefficientFunctional (v:Space) W).im := by
  rw [rowEmbedding_inner]
  change (∫ r:Interval,(v:Space) r*(W r).im)=(∫ r:Interval,((v:Space) r:ℂ)*W r).im
  simpa only [waveImagPart,ContinuousMap.coe_mk,RCLike.im_eq_complex_im,
    Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero] using
    integral_im (coefficient_integrable (v:Space) W)

/-- A continuous complex wave orthogonal to either complete actual transformed parity family vanishes everywhere on the physical half interval.
Use: the actual separated characteristic has no zeros outside its prescribed original parity spectrum.
Article: jacobi, Proposition C.2.
Proof: apply the proved real completeness separately to the genuine embedded real and imaginary parts; their continuous representatives vanish at every half-interval point. -/
theorem half_complex_pairing_total (a : ℝ) (ha : -1<a) (p : Fin 2)
    (W : C(Interval,ℂ))
    (hW : ∀ k,coefficientFunctional
      (transformedVector a ha (jacobi.Bessel.sigma a ha (parityIndex p k)):Space) W=0)
    (t : HalfInterval) : W (halfInclusion t)=0 := by
  -- The complex function is reduced to two vectors of the actual real Hilbert space, so completeness needs no complexification premise.
  have hre : rowEmbedding (waveRealPart W)=0 := by
    apply transformed_parity_total a ha p
    intro k
    rw [real_inner_comm, waveRealPart_pairing,hW k]
    rfl
  have him : rowEmbedding (waveImagPart W)=0 := by
    apply transformed_parity_total a ha p
    intro k
    rw [real_inner_comm, waveImagPart_pairing,hW k]
    rfl
  apply Complex.ext
  · exact rowEmbedding_zero_on_half (waveRealPart W) hre t
  · exact rowEmbedding_zero_on_half (waveImagPart W) him t

end
end jacobi.GelfandLevitan
