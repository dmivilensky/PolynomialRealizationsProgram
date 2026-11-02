import jacobi.GelfandLevitan.MidpointDirichlet
import jacobi.GelfandLevitan.FullTransformedBasis
import jacobi.GelfandLevitan.Profiles

/-!
Article: jacobi, Theorem 2.1.
The actual full reflected target basis has continuous representatives
on the closed physical interval. The odd representatives are continuous
at the midpoint because their genuine Dirichlet values are proved zero.
Their pointwise squares are the original spectral profiles Phi_k.
Use: fullWaveMap and fullTargetBasis_wave_ae identify the continuous original v_k with the actual full Hilbert basis vector.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference
open scoped Topology InnerProductSpace
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false

/-- The original full-interval normalization of each genuine transformed wave.
Use: fullWaveMap and fullTargetBasis_wave_ae identify the continuous original v_k with the actual full Hilbert basis vector.
Article: jacobi, Theorem 2.1.
-/
def targetWaveScale (a : ℝ) (ha : -1<a) (k : ℕ) : ℝ :=
  (halfNormalization a k*Real.sqrt (normingRatio a ha k))/Real.sqrt 2

/-- The genuine full wave normalization has exactly the original profile squared weight.
Use: fullWaveMap_sq identifies v_k(t)^2 with the already constructed original Phi_k(t).
Article: jacobi, Theorem 2.1.
Proof: the independently proved half normalization has square 2*rho_k/N_k; the genuine sqrt(2) full-extension factor cancels the two. -/
theorem targetWaveScale_sq (a : ℝ) (ha : -1<a) (k : ℕ) :
    (targetWaveScale a ha k)^2=normingRatio a ha k/norming a k := by
  rw [targetWaveScale,div_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤2),halfNormalization_weight_sq]
  ring

/-- Every actual target spectral wave has precisely the midpoint value compatibility required by its original reflection sign.
Use: fullWaveMap is continuous across the genuine midpoint for both actual parity classes.
Article: jacobi, Theorem 2.1.
Proof: zero-based even indices have reflection sign one. Zero-based odd indices have actual midpoint value zero by the independently proved exact original Dirichlet class. -/
theorem transformed_midpoint_value_parity (a : ℝ) (ha : -1<a) (n : ℕ) :
    (transformedSolution a ha halfMidpoint (jacobi.Bessel.sigma a ha n:ℂ)).re=
      (-1:ℝ)^n*(transformedSolution a ha halfMidpoint (jacobi.Bessel.sigma a ha n:ℂ)).re := by
  obtain ⟨k,hk|hk⟩ := Nat.even_or_odd' n <;> subst n
  · simp only [pow_mul,neg_one_sq,one_pow,one_mul]
  · have hz : transformedSolution a ha halfMidpoint (jacobi.Bessel.sigma a ha (2*k+1):ℂ)=0 :=
      (midpointValue_zero_iff a ha _).mpr ⟨k,rfl⟩
    rw [hz,Complex.zero_re,mul_zero]

/-- The actual normalized full reflected transformed wave as a continuous function on the original closed physical interval.
Use: targetGreenKernel is the uniformly convergent series of the genuine continuous rank-one wave kernels; fullTargetBasis_wave_ae connects them with the actual spectral inverse.
Article: jacobi, Proposition 2.2.
-/
def fullWaveMap (a : ℝ) (ha : -1<a) (n : ℕ) : C(Interval,ℝ) where
  toFun t := targetWaveScale a ha n*(if (t:ℝ)≤1/2 then
    transformedRealWave a ha (jacobi.Bessel.sigma a ha n) t else
      (-1:ℝ)^n*transformedRealWave a ha (jacobi.Bessel.sigma a ha n) (physicalReflection t))
  continuous_toFun := continuous_const.mul (Continuous.if_le
    (transformedRealWave a ha (jacobi.Bessel.sigma a ha n)).continuous
    (continuous_const.mul ((transformedRealWave a ha (jacobi.Bessel.sigma a ha n)).continuous.comp physicalReflection.continuous))
    continuous_subtype_val continuous_const (fun t ht => by
      have hl : halfClamp t=halfMidpoint := Subtype.ext (by change min (t:ℝ) (1/2)=1/2; rw [ht,min_self])
      have hr : halfClamp (physicalReflection t)=halfMidpoint := Subtype.ext (by
        change min (1-(t:ℝ)) (1/2)=1/2
        rw [ht]
        norm_num)
      change (transformedSolution a ha (halfClamp t) (jacobi.Bessel.sigma a ha n:ℂ)).re=_
      change _=(-1:ℝ)^n*(transformedSolution a ha (halfClamp (physicalReflection t)) (jacobi.Bessel.sigma a ha n:ℂ)).re
      rw [hl,hr]
      exact transformed_midpoint_value_parity a ha n))

/-- The actual full target Hilbert basis vector is exactly the normalized parity extension of the original unnormalized transformed half vector.
Use: fullTargetBasis_wave_ae computes its genuine continuous spatial representative by the original zero-extension and reflection formulas.
Article: jacobi, Proposition 2.2.
Proof: insert the actual transformed half-basis entries into the original full parity extension. Their original index is reconstructed by Euclidean division, and the genuine scalar factors combine into targetWaveScale. -/
theorem fullTargetBasis_extension (a : ℝ) (ha : -1<a) (n : ℕ) :
    fullTargetBasis a ha n=targetWaveScale a ha n •
      ((transformedVector a ha (jacobi.Bessel.sigma a ha n):Space)+
        (-1:ℝ)^n • reflectionUnitary (transformedVector a ha (jacobi.Bessel.sigma a ha n):Space)) := by
  -- The normalization is expanded before any L2 representative is used, so the actual quotient vectors remain unchanged.
  rw [fullTargetBasis_apply,fullTransformedVector,transformedParityBasis_apply,
    parityIndex_spectralParity,normalizedTransformedVector,normalizedParityExtension,halfParityExtension]
  have he : (-1:ℝ)^(spectralParity n:ℕ)=(-1:ℝ)^n := by
    change (-1:ℝ)^(n%2)=(-1:ℝ)^n
    rw [← parityIndex_spectralParity n,parityIndex,pow_add,pow_mul]
    norm_num [spectralParity]
  change (Real.sqrt 2)⁻¹ •
    (((halfNormalization a n*Real.sqrt (normingRatio a ha n)) •
        (transformedVector a ha (jacobi.Bessel.sigma a ha n):Space))+
      (-1:ℝ)^(spectralParity n:ℕ) • reflectionUnitary
        ((halfNormalization a n*Real.sqrt (normingRatio a ha n)) •
          (transformedVector a ha (jacobi.Bessel.sigma a ha n):Space)))=_
  rw [map_smul,he]
  dsimp [targetWaveScale]
  module

/-- Every original full target Hilbert basis vector has the actual continuous reflected transformed wave as its genuine almost-everywhere representative.
Use: the original Green kernel series and its true integral action use the same original continuous v_k functions as the actual full spectral operator.
Article: jacobi, Theorem 2.1.
Proof: expand the proved actual extension identity and insert the genuine transformed half-vector representative and its measure-preserving reflected representative. Off the null midpoint exactly one original half indicator contributes, yielding the literal original continuous reflected wave. -/
theorem fullTargetBasis_wave_ae (a : ℝ) (ha : -1<a) (n : ℕ) :
    fullTargetBasis a ha n=ᵐ[volume] fullWaveMap a ha n := by
  -- The actual single midpoint is excluded only for the indicator partition; continuity has already proved its original pointwise representative separately.
  let v : Space := transformedVector a ha (jacobi.Bessel.sigma a ha n)
  let ε := (-1:ℝ)^n
  rw [fullTargetBasis_extension]
  filter_upwards [Lp.coeFn_smul (targetWaveScale a ha n) (v+ε • reflectionUnitary v),
    Lp.coeFn_add v (ε • reflectionUnitary v),Lp.coeFn_smul ε (reflectionUnitary v),
    reflectionUnitary_ae v,transformedVector_ae a ha (jacobi.Bessel.sigma a ha n),
    unitInterval.measurePreserving_symm.quasiMeasurePreserving.ae_eq_comp
      (transformedVector_ae a ha (jacobi.Bessel.sigma a ha n)),
    volume.ae_ne (⟨1/2,by norm_num⟩:Interval)] with t hS hAdd hε hR hv hvR ht
  dsimp only [Function.comp_apply] at hvR
  rw [hS]
  dsimp only [Pi.smul_apply,smul_eq_mul]
  rw [hAdd]
  dsimp only [Pi.add_apply]
  rw [hε]
  dsimp only [Pi.smul_apply,smul_eq_mul]
  rw [hR,hv,hvR]
  change targetWaveScale a ha n*((prefixSet (1/2)).indicator
    (transformedRealWave a ha (jacobi.Bessel.sigma a ha n)) t+
    ε*(prefixSet (1/2)).indicator (transformedRealWave a ha (jacobi.Bessel.sigma a ha n))
      (unitInterval.symm t))=fullWaveMap a ha n t
  have ht' : (t:ℝ)≠1/2 := fun h => ht (Subtype.ext h)
  have href : unitInterval.symm t=physicalReflection t := Subtype.ext (unitInterval.coe_symm_eq t)
  by_cases hp : (t:ℝ)≤1/2
  · have hr : unitInterval.symm t∉prefixSet (1/2) := by
      change ¬(unitInterval.symm t:ℝ)≤1/2
      rw [unitInterval.coe_symm_eq]
      have hlt := lt_of_le_of_ne hp ht'
      linarith
    rw [indicator_of_mem (show t∈prefixSet (1/2) from hp),indicator_of_notMem hr,mul_zero,add_zero]
    exact (congrArg (fun x:ℝ => targetWaveScale a ha n*x) (ite_eq_left hp)).symm
  · have hr : unitInterval.symm t∈prefixSet (1/2) := by
      change (unitInterval.symm t:ℝ)≤1/2
      rw [unitInterval.coe_symm_eq]
      linarith [lt_of_not_ge hp]
    rw [indicator_of_notMem (show t∉prefixSet (1/2) from hp),indicator_of_mem hr,zero_add,href]
    exact (congrArg (fun x:ℝ => targetWaveScale a ha n*x) (ite_eq_right hp)).symm

end
end jacobi.GelfandLevitan
