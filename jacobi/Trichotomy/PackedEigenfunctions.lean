import jacobi.Trichotomy.PackingWaves

/-!
Article: jacobi, Proposition 2.2.
The transferred original target waves are orthonormal real-line L2 vectors.
The actual density kernel acts on them with the original eigenvalues 2/sigma_k.
Source: the exact Green-coordinate kernel and the original Green inverse.
Use: PackedSpectrum combines this infinite eigenframe with the exact mass
trace to exclude any additional nonzero eigenvalues or multiplicities.
-/
namespace jacobi.Trichotomy
noncomputable section
open Real Set Filter Function MeasureTheory jacobi.Reference jacobi.GelfandLevitan
open chebyshev2.Continuum
open scoped Topology InnerProductSpace
attribute [local instance] Measure.Subtype.measureSpace

/-- The actual full real-line kernel operator of the constructed packed density.
Use: packedKernel_basis proves its genuine eigenvectors; packedDensity_spectrum
identifies its entire sorted nonzero spectrum with multiplicities.
Article: jacobi, Proposition 2.2.
-/
def packedKernel (a : ℝ) (ha : -1<a) : FeatureSpace →L[ℝ] FeatureSpace :=
  kernelOperator (packedDensity_integrable a ha) (packedDensity_nonneg a ha)

/-- The genuine real-line L2 transfer of the original normalized target eigenfunction.
Use: the packed eigenframe and exact trace determine the entire nonzero
density spectrum without a redundant whole-space unitary construction.
Article: jacobi, Proposition 2.2.
-/
def packedBasis (a : ℝ) (ha : -1<a) (k : ℕ) : FeatureSpace :=
  packedWaveVector a ha (fullWaveMap a ha k)

/-- The actual transported original target waves form an orthonormal sequence.
Use: PackedSpectrum applies the community finite-eigenframe sorted spectral
bound at every index, then closes it by equality of the total trace.
Article: jacobi, Proposition 2.2.
Proof: the actual coordinate transfer preserves pairings, and the original
physical representatives are the independently proved full target Hilbert basis. -/
theorem packedBasis_orthonormal (a : ℝ) (ha : -1<a) : Orthonormal ℝ (packedBasis a ha) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [packedBasis,packedBasis,packedWave_pairing]
  have he : (∫ t : Interval,fullWaveMap a ha i t*fullWaveMap a ha j t)=
      inner ℝ (fullTargetBasis a ha j) (fullTargetBasis a ha i) := by
    rw [← fullWaveMap_coefficient]
    apply integral_congr_ae
    filter_upwards [fullTargetBasis_wave_ae a ha i] with t ht
    rw [ht]
  rw [he]
  simpa only [eq_comm] using (orthonormal_iff_ite.mp (fullTargetBasis a ha).orthonormal j i)

/-- The original continuous target Green kernel acts on each true normalized
wave with its actual inverse-sigma eigenvalue, at every physical point.
Use: packedKernel_basis transports this pointwise identity through the
actual Green coordinate, rather than merely assuming the spectrum.
Article: jacobi, Proposition 2.2.
Proof: the actual Green-action map embeds as the true bounded inverse.
Its basis action and injectivity of the continuous L2 inclusion determine
the map at every physical point. -/
theorem targetGreen_wave_integral (a : ℝ) (ha : -1<a) (k : ℕ) (t : Interval) :
    (∫ s : Interval,fullWaveMap a ha k s*targetGreenKernel a ha t s)=
      (jacobi.Bessel.sigma a ha k)⁻¹*fullWaveMap a ha k t := by
  have hm : targetGreenActionMap a ha (fullTargetBasis a ha k)=
      (jacobi.Bessel.sigma a ha k)⁻¹ • fullWaveMap a ha k := by
    apply physical_toLp_injective
    rw [targetGreenActionMap_toLp,map_smul,fullWaveMap_toLp,targetGreen_basis]
  have he := congrArg (fun F : C(Interval,ℝ) => F t) hm
  rw [targetGreenActionMap_apply] at he
  change (∫ s : Interval,_)= (jacobi.Bessel.sigma a ha k)⁻¹*fullWaveMap a ha k t at he
  rw [← he]
  apply integral_congr_ae
  filter_upwards [fullTargetBasis_wave_ae a ha k] with s hs
  rw [hs]

/-- The original real-coordinate Green integral on the open physical
interval equals its true inverse-sigma eigenfunction value.
Use: packedKernel_wave_integral performs the actual whole-line eigenfunction
substitution with the same unchanged original physical wave.
Article: jacobi, Proposition 2.2.
Proof: the open and closed physical intervals differ only by null endpoints;
the original continuous representatives agree with their projections. -/
theorem targetGreen_wave_integral_real (a : ℝ) (ha : -1<a) (k : ℕ) (t : Interval) :
    (∫ s in Ioo (0:ℝ) 1,physicalGreenKernel a ha t s*
      fullWaveMap a ha k (projIcc 0 1 (by norm_num) s))=
        (jacobi.Bessel.sigma a ha k)⁻¹*fullWaveMap a ha k t := by
  rw [← integral_Icc_eq_integral_Ioo,← integral_subtype measurableSet_Icc]
  convert targetGreen_wave_integral a ha k t using 1
  apply integral_congr_ae
  exact Eventually.of_forall (fun s => by
    dsimp only
    rw [physicalGreenKernel_eq a ha t s,projIcc_of_mem (by norm_num) s.property,mul_comm])

/-- The actual printed density-kernel integral sends the transferred wave
to its prescribed eigenvalue at every intrinsic physical coordinate.
Use: packedKernel_basis upgrades this actual pointwise integral statement
to the genuine real-line L2 kernel operator's eigenvector identity.
Article: jacobi, Proposition 2.2.
Proof: substitute the genuine intrinsic Jacobian, then use the proved
exponential Green identity. The remaining physical integral is precisely
the original Green inverse applied to its actual normalized wave. -/
theorem packedKernel_wave_integral (a : ℝ) (ha : -1<a) (k : ℕ)
    {t : ℝ} (ht : t∈Ioo (0:ℝ) 1) :
    sqrt (packedDensity a ha (packingCoordinate a ha t))*
      (∫ y : ℝ,exp (-|packingCoordinate a ha t-y|)*sqrt (packedDensity a ha y)*
        packedWave a ha (fullWaveMap a ha k) y)=
      jacobi.Bessel.edgeValue a ha k*packedWave a ha (fullWaveMap a ha k) (packingCoordinate a ha t) := by
  let v := fullWaveMap a ha k
  have hφ := physicalProfile_pos a ha ht
  rw [packedDensity_coordinate a ha ht,sqrt_sq_eq_abs,abs_of_pos hφ,← integral_const_mul]
  rw [packing_integral a ha _ (fun y hy => by simp [packedWave,indicator_of_notMem hy])]
  have he : (∫ s in Ioo (0:ℝ) 1,(1/physicalProfile a ha s)*
      (physicalProfile a ha t*(exp (-|packingCoordinate a ha t-packingCoordinate a ha s|)*
        sqrt (packedDensity a ha (packingCoordinate a ha s))*
        packedWave a ha v (packingCoordinate a ha s))))=
      ∫ s in Ioo (0:ℝ) 1,(2*sqrt (physicalProfile a ha t))*
        (physicalGreenKernel a ha t s*v (projIcc 0 1 (by norm_num) s)) := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro s hs
    dsimp only
    rw [packedDensity_coordinate a ha hs,sqrt_sq_eq_abs,abs_of_pos (physicalProfile_pos a ha hs),
      packedWave_coordinate a ha v hs,projIcc_of_mem (by norm_num) ⟨hs.1.le,hs.2.le⟩]
    have hg := targetGreen_exponential a ha ht hs
    rw [sqrt_mul hφ.le] at hg
    have hsq := sq_sqrt hφ.le
    have he' := congrArg (fun z : ℝ => sqrt (physicalProfile a ha t)*
      v ⟨s,⟨hs.1.le,hs.2.le⟩⟩*z) hg
    field_simp [(physicalProfile_pos a ha hs).ne']
    nlinarith [he',congrArg (fun z : ℝ =>
      exp (-|packingCoordinate a ha t-packingCoordinate a ha s|)*sqrt (physicalProfile a ha s)*
        v ⟨s,⟨hs.1.le,hs.2.le⟩⟩*z) hsq]
  rw [he,integral_const_mul,targetGreen_wave_integral_real a ha k ⟨t,⟨ht.1.le,ht.2.le⟩⟩,
    packedWave_coordinate a ha (fullWaveMap a ha k) ht,jacobi.Bessel.edgeValue]
  ring

/-- The genuine full real-line density kernel has each transported target
wave as an eigenvector with exactly the prescribed original eigenvalue.
Use: packedDensity_spectrum derives the complete sorted spectral sequence
from these actual eigenvectors and the already proved exact mass trace.
Article: jacobi, Proposition 2.2.
Proof: the literal kernel integral has the proved value on the actual
coordinate image and vanishes off it. Replace the L2 input by its genuine
transferred representative inside the integral, then use the community
kernel operator's actual almost-everywhere integral formula. -/
theorem packedKernel_basis (a : ℝ) (ha : -1<a) (k : ℕ) :
    packedKernel a ha (packedBasis a ha k)=
      jacobi.Bessel.edgeValue a ha k • packedBasis a ha k := by
  let F := fullWaveMap a ha k
  have hrep : packedBasis a ha k=ᵐ[volume] packedWave a ha F :=
    (packedWave_memLp a ha F).coeFn_toLp
  have hint (x : ℝ) :
      (∫ y : ℝ,exp (-|x-y|)*sqrt (packedDensity a ha y)*(packedBasis a ha k) y)=
        ∫ y : ℝ,exp (-|x-y|)*sqrt (packedDensity a ha y)*packedWave a ha F y := by
    apply integral_congr_ae
    filter_upwards [hrep] with y hy
    rw [hy]
  have hraw (x : ℝ) : sqrt (packedDensity a ha x)*
      (∫ y : ℝ,exp (-|x-y|)*sqrt (packedDensity a ha y)*packedWave a ha F y)=
        jacobi.Bessel.edgeValue a ha k*packedWave a ha F x := by
    by_cases hx : x∈packingImage a ha
    · obtain ⟨t,ht,rfl⟩ := hx
      exact packedKernel_wave_integral a ha k ht
    · simp only [packedDensity_zero_outside a ha hx,sqrt_zero,zero_mul,packedWave,
        indicator_of_notMem hx,mul_zero]
  apply Lp.ext
  filter_upwards [kernelOperator_coe (packedDensity_integrable a ha)
    (packedDensity_nonneg a ha) (packedBasis a ha k),
    Lp.coeFn_smul (jacobi.Bessel.edgeValue a ha k) (packedBasis a ha k),hrep] with x hK hsm hx
  change (kernelOperator (packedDensity_integrable a ha) (packedDensity_nonneg a ha)
    (packedBasis a ha k)) x=_
  rw [hK,hsm,hint x,hraw x]
  change _= jacobi.Bessel.edgeValue a ha k*(packedBasis a ha k) x
  rw [hx]

end
end jacobi.Trichotomy
