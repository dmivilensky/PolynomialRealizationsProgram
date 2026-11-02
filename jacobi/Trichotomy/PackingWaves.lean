import jacobi.Trichotomy.PackingMoments
import jacobi.Trichotomy.GreenExponential
import chebyshev2.Continuum.KernelOperator

/-!
Article: jacobi, Proposition 2.2.
The original intrinsic coordinate transfers continuous physical functions
to actual square-integrable functions on the line. Pairings are preserved
exactly, including the zero extension for compact coordinate images.
Source: the one-dimensional Jacobian theorem and the positive profile.
Use: PackedSpectrum transfers the genuine target eigenfunctions, then uses
the exact trace to prove completeness of the nonzero density spectrum.
-/
namespace jacobi.Trichotomy
noncomputable section
open Real Set Filter Function MeasureTheory jacobi.Reference jacobi.GelfandLevitan
open scoped Topology InnerProductSpace
attribute [local instance] Measure.Subtype.measureSpace

/-- Integrability of any function supported in the actual coordinate image
is equivalent to integrability of its genuine Jacobian pullback.
Use: packedWave_memLp proves square integrability before any inner product
or spectral assertion is formed.
Article: jacobi, Proposition 2.2.
Proof: replace the supported function by its actual image indicator and
apply the community injective one-dimensional Jacobian theorem. -/
theorem packing_integrable_iff (a : ℝ) (ha : -1<a) (f : ℝ → ℝ)
    (hf : ∀ x,x∉packingImage a ha → f x=0) :
    Integrable f ↔ IntegrableOn
      (fun t => (1/physicalProfile a ha t)*f (packingCoordinate a ha t)) (Ioo (0:ℝ) 1) := by
  have he : f=(packingImage a ha).indicator f := by
    funext x
    by_cases hx : x∈packingImage a ha <;> simp [hx,hf x]
  rw [he,integrable_indicator_iff (packingImage_open a ha).measurableSet]
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo
    (fun t ht => (packingCoordinate_hasDerivAt a ha ht).hasDerivWithinAt)
    (packingCoordinate_strictMono a ha).injOn f
  apply h.trans
  apply integrableOn_congr_fun _ measurableSet_Ioo
  intro t ht
  simp only [abs_of_pos (one_div_pos.mpr (physicalProfile_pos a ha ht)),smul_eq_mul,
    indicator_of_mem (show packingCoordinate a ha t∈packingImage a ha from ⟨t,ht,rfl⟩)]

/-- The integral of every function supported in the actual coordinate image
is its original physical Jacobian integral.
Use: packedWave_pairing and packed kernel eigenfunction identities use this
same actual coordinate, with no support-regime assumption.
Article: jacobi, Proposition 2.2.
Proof: the complement is identically zero; apply the actual injective
Jacobian integral theorem and the proved positive coordinate derivative. -/
theorem packing_integral (a : ℝ) (ha : -1<a) (f : ℝ → ℝ)
    (hf : ∀ x,x∉packingImage a ha → f x=0) :
    (∫ x : ℝ,f x)=∫ t in Ioo (0:ℝ) 1,
      (1/physicalProfile a ha t)*f (packingCoordinate a ha t) := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := packingImage a ha) hf]
  rw [show packingImage a ha=packingCoordinate a ha '' Ioo (0:ℝ) 1 from rfl,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
      (fun t ht => (packingCoordinate_hasDerivAt a ha ht).hasDerivWithinAt)
      (packingCoordinate_strictMono a ha).injOn]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  simp only [abs_of_pos (one_div_pos.mpr (physicalProfile_pos a ha ht)),smul_eq_mul]

/-- The actual coordinate transfer of a continuous physical function,
multiplied by sqrt(phi_alpha) and extended by zero outside the true image.
Use: packedWaveVector and PackedSpectrum use these exact functions as
the actual density-kernel eigenfunctions.
Article: jacobi, Proposition 2.2.
-/
def packedWave (a : ℝ) (ha : -1<a) (F : C(Interval,ℝ)) (x : ℝ) : ℝ :=
  (packingImage a ha).indicator (fun y => sqrt (physicalProfile a ha (packingInverse a ha y))*
    F (projIcc 0 1 (by norm_num) (packingInverse a ha y))) x

/-- The transferred function has exactly its original coordinate formula.
Use: all norm, pairing and kernel substitutions retain the true original
physical function and the same positive profile multiplier.
Article: jacobi, Proposition 2.2.
Proof: the coordinate lies in its image and its actual inverse returns t. -/
theorem packedWave_coordinate (a : ℝ) (ha : -1<a) (F : C(Interval,ℝ))
    {t : ℝ} (ht : t∈Ioo (0:ℝ) 1) :
    packedWave a ha F (packingCoordinate a ha t)=sqrt (physicalProfile a ha t)*
      F ⟨t,⟨ht.1.le,ht.2.le⟩⟩ := by
  simp only [packedWave,indicator_of_mem (show packingCoordinate a ha t∈packingImage a ha from ⟨t,ht,rfl⟩),
    packingInverse_coordinate a ha ht,projIcc_of_mem (by norm_num) ⟨ht.1.le,ht.2.le⟩]

/-- The actual transferred function is measurable on the whole line.
Use: packedWave_memLp gives genuine L2 functions, including compact-image
cases, before defining their quotient vectors.
Article: jacobi, Proposition 2.2.
Proof: its nonzero branch is continuous on the open coordinate image;
the complementary zero branch is continuous, so the piecewise function
is measurable. Endpoint values require no extra limiting assertion. -/
theorem packedWave_measurable (a : ℝ) (ha : -1<a) (F : C(Interval,ℝ)) :
    Measurable (packedWave a ha F) := by
  classical
  have hc : ContinuousOn (fun y => sqrt (physicalProfile a ha (packingInverse a ha y))*
      F (projIcc 0 1 (by norm_num) (packingInverse a ha y))) (packingImage a ha) :=
    (((physicalProfile_continuous a ha).sqrt).mul (F.continuous.comp continuous_projIcc)
      ).comp_continuousOn (packingInverse_continuousOn a ha)
  exact hc.measurable_piecewise continuousOn_const (packingImage_open a ha).measurableSet

/-- Every actual transferred continuous physical function is square integrable.
Use: packedWaveVector is an actual L2 vector; the subsequent eigenframe
and trace argument never use a totalized norm of a nonintegrable function.
Article: jacobi, Proposition 2.2.
Proof: under the proved actual coordinate substitution its squared norm
has integrand F(t)^2, since the positive profile cancels its reciprocal
Jacobian. This continuous physical integrand is integrable on [0,1]. -/
theorem packedWave_memLp (a : ℝ) (ha : -1<a) (F : C(Interval,ℝ)) :
    MemLp (packedWave a ha F) 2 volume := by
  apply (memLp_two_iff_integrable_sq (packedWave_measurable a ha F).aestronglyMeasurable).mpr
  apply (packing_integrable_iff a ha (fun x => (packedWave a ha F x)^2)
    (fun x hx => by simp [packedWave,indicator_of_notMem hx])).mpr
  have hi : IntegrableOn (fun t : ℝ => (F (projIcc 0 1 (by norm_num) t))^2) (Ioo (0:ℝ) 1) :=
    ((F.continuous.comp continuous_projIcc).pow 2).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  apply hi.congr_fun _ measurableSet_Ioo
  intro t ht
  dsimp only
  rw [packedWave_coordinate a ha F ht,mul_pow,sq_sqrt (physicalProfile_pos a ha ht).le,
    projIcc_of_mem (by norm_num) ⟨ht.1.le,ht.2.le⟩]
  field_simp [(physicalProfile_pos a ha ht).ne']

/-- The transferred physical function as a genuine real-line L2 quotient vector.
Use: PackedSpectrum takes F to be each actual target basis wave and
proves the original density kernel's full spectrum by eigenframes and trace.
Article: jacobi, Proposition 2.2.
-/
def packedWaveVector (a : ℝ) (ha : -1<a) (F : C(Interval,ℝ)) :
    chebyshev2.Continuum.FeatureSpace :=
  (packedWave_memLp a ha F).toLp (packedWave a ha F)

/-- The genuine coordinate transfer preserves every continuous physical pairing.
Use: PackedSpectrum obtains an actual orthonormal sequence from the
original complete target eigenbasis before applying the sorted spectral bound.
Article: jacobi, Proposition 2.2.
Proof: substitute the actual L2 representatives, use the actual Jacobian
formula, cancel the squared positive square root, and remove the null endpoints. -/
theorem packedWave_pairing (a : ℝ) (ha : -1<a) (F G : C(Interval,ℝ)) :
    inner ℝ (packedWaveVector a ha F) (packedWaveVector a ha G)=
      ∫ t : Interval,F t*G t := by
  rw [L2.inner_def]
  have he : (∫ x : ℝ,(packedWaveVector a ha G) x*(packedWaveVector a ha F) x)=
      ∫ x : ℝ,packedWave a ha F x*packedWave a ha G x := by
    apply integral_congr_ae
    filter_upwards [(packedWave_memLp a ha F).coeFn_toLp,
      (packedWave_memLp a ha G).coeFn_toLp] with x hF hG
    dsimp only [packedWaveVector]
    rw [hF,hG,mul_comm]
  change (∫ x : ℝ,(packedWaveVector a ha G) x*(packedWaveVector a ha F) x)=_
  rw [he,packing_integral a ha _ (fun x hx => by simp [packedWave,indicator_of_notMem hx])]
  have hfun : (∫ t in Ioo (0:ℝ) 1,(1/physicalProfile a ha t)*
      (packedWave a ha F (packingCoordinate a ha t)*packedWave a ha G (packingCoordinate a ha t)))=
      ∫ t in Ioo (0:ℝ) 1,F (projIcc 0 1 (by norm_num) t)*G (projIcc 0 1 (by norm_num) t) := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro t ht
    dsimp only
    rw [packedWave_coordinate a ha F ht,packedWave_coordinate a ha G ht,
      projIcc_of_mem (by norm_num) ⟨ht.1.le,ht.2.le⟩]
    have hs := sq_sqrt (physicalProfile_pos a ha ht).le
    field_simp [(physicalProfile_pos a ha ht).ne']
    nlinarith [congrArg (fun z : ℝ => F ⟨t,⟨ht.1.le,ht.2.le⟩⟩*G ⟨t,⟨ht.1.le,ht.2.le⟩⟩*z) hs]
  rw [hfun,← integral_Icc_eq_integral_Ioo,← integral_subtype measurableSet_Icc]
  apply integral_congr_ae
  exact Eventually.of_forall (fun t => by
    simp only [projIcc_of_mem (by norm_num) t.property])

end
end jacobi.Trichotomy
