import jacobi.Analysis.CompactTest
import jacobi.GelfandLevitan.TargetDifferentialOperator
import jacobi.GelfandLevitan.TargetGreenAction

/-!
Article: jacobi, Theorem 2.1.
Every compactly supported C2 function in (0,1) belongs to the actual spectral
domain, and its image is its classical Schrodinger expression. In particular
this applies to all smooth compact tests used by Proposition 2.2.
Source: compact-test Green identity and the complete Hilbert basis expansion.
Use: targetOperator_compact_test and targetGreen_compact_test provide the
differential realization and its genuine inverse identity on every test.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter MeasureTheory Function jacobi.Reference
open scoped Topology InnerProductSpace
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The original classical Schrodinger expression on a real test function.
Use: targetOperator_compact_test identifies this expression with the actual
unbounded spectral operator, rather than defining the operator by it.
Article: jacobi, Proposition 2.2.
-/
def testExpression (a : ℝ) (ha : -1<a) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  -deriv (deriv f) t+targetPotential a ha t*f t

/-- The differential expression has support contained in the original test support.
Use: its continuity and coefficient integrals require no potential regularity
at the singular ends or outside the physical interval.
Article: jacobi, Theorem 2.1.
Proof: both derivatives vanish off the closed support, as does the test. -/
theorem testExpression_tsupport (a : ℝ) (ha : -1<a) (f : ℝ → ℝ) :
    tsupport (testExpression a ha f) ⊆ tsupport f := by
  apply closure_minimal _ (isClosed_tsupport f)
  intro t ht
  by_contra hn
  have hn1 : t ∉ tsupport (deriv f) := fun h => hn (tsupport_deriv_subset h)
  exact ht (by simp [testExpression,image_eq_zero_of_notMem_tsupport hn,
    deriv_of_notMem_tsupport hn1])

/-- The actual differential expression of a compact interior C2 test is continuous.
Use: its ordinary continuous representative embeds into the physical L2 space
and witnesses membership in the genuine weighted spectral domain.
Article: jacobi, Theorem 2.1.
Proof: the second derivative is continuous; the supported potential product
is continuous even at the singular ends because the test is locally zero. -/
theorem testExpression_continuous (a : ℝ) (ha : -1<a) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hs : tsupport f ⊆ Ioo (0:ℝ) 1) :
    Continuous (testExpression a ha f) := by
  have hfd : ContDiff ℝ 1 (deriv f) := (show ContDiff ℝ (1+1) f from hf).deriv'
  exact (hfd.continuous_deriv (by norm_num)).neg.add
    (by simpa only [mul_comm] using (jacobi.Analysis.continuous_supported_mul
      hf.continuous isOpen_Ioo hs (targetPotential_continuousOn a ha)))

/-- An interior-supported physical pairing equals the same real-line integral.
Use: compact_test_coefficient transfers the compact Green identity to the
actual original full-target Hilbert basis.
Article: jacobi, Theorem 2.1.
Proof: the true wave representative agrees on the original interval, and
the supported factor makes the complement's integral zero. -/
theorem supported_wave_integral (a : ℝ) (ha : -1<a) (k : ℕ) {f : ℝ → ℝ}
    (hs : tsupport f ⊆ Ioo (0:ℝ) 1) :
    (∫ t : Interval, f t*fullWaveMap a ha k t)=
      ∫ t : ℝ, f t*fullWavePhysical a ha k t := by
  simp_rw [← fullWavePhysical_eq_map]
  rw [integral_subtype (s := Icc (0:ℝ) 1) measurableSet_Icc
    (fun t : ℝ => f t*fullWavePhysical a ha k t)]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro t ht
  have hn : t ∉ tsupport f := fun h => ht ⟨(hs h).1.le,(hs h).2.le⟩
  simp [image_eq_zero_of_notMem_tsupport hn]

/-- The Fourier coefficient of the actual differential expression is sigma_k
times the coefficient of the test, for every original target eigenfunction.
Use: targetOperator_compact_test obtains a witness in the full spectral graph
from these exact coefficients; no undischarged boundary premise remains.
Article: jacobi, Theorem 2.1.
Proof: two compact integrations by parts transfer the actual second
derivative to the actual C2 wave. Its already proved ODE cancels the potential. -/
theorem compact_test_coefficient (a : ℝ) (ha : -1<a) (k : ℕ) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ Ioo (0:ℝ) 1) :
    (∫ t : Interval, testExpression a ha f t*fullWaveMap a ha k t)=
      jacobi.Bessel.sigma a ha k*(∫ t : Interval, f t*fullWaveMap a ha k t) := by
  rw [supported_wave_integral a ha k ((testExpression_tsupport a ha f).trans hs),
    supported_wave_integral a ha k hs]
  let g := fullWavePhysical a ha k
  have hg := fullWavePhysical_contDiffOn_two a ha k
  have hd := jacobi.Analysis.compact_test_second_derivative hf hc isOpen_Ioo hs hg
  have hfd : ContDiff ℝ 1 (deriv f) := (show ContDiff ℝ (1+1) f from hf).deriv'
  have hi1 : Integrable (fun t => deriv (deriv f) t*g t) :=
    (jacobi.Analysis.continuous_supported_mul (hfd.continuous_deriv (by norm_num)) isOpen_Ioo
      (tsupport_deriv_subset.trans (tsupport_deriv_subset.trans hs)) hg.continuousOn
      ).integrable_of_hasCompactSupport hc.deriv.deriv.mul_right
  have hc2 : Continuous (fun t => targetPotential a ha t*f t*g t) := by
    have h := jacobi.Analysis.continuous_supported_mul hf.continuous isOpen_Ioo hs
      ((targetPotential_continuousOn a ha).mul hg.continuousOn)
    convert h using 1
    ext t
    dsimp only [g,Pi.mul_apply]
    ring
  have hi2 : Integrable (fun t => targetPotential a ha t*f t*g t) :=
    hc2.integrable_of_hasCompactSupport (hc.mul_left.mul_right)
  simp_rw [testExpression,add_mul,neg_mul]
  change (∫ t : ℝ, -(deriv (deriv f) t*g t)+targetPotential a ha t*f t*g t)=
    jacobi.Bessel.sigma a ha k*(∫ t : ℝ, f t*g t)
  change (∫ t : ℝ, deriv (deriv f) t*g t)=(∫ t : ℝ, f t*deriv (deriv g) t) at hd
  have hadd := integral_add hi1.neg hi2
  simp only [Pi.neg_apply] at hadd
  rw [hadd,integral_neg,hd,← integral_const_mul]
  have hgd : ContDiffOn ℝ 1 (deriv g) (Ioo (0:ℝ) 1) :=
    hg.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hgdd := hgd.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hi3 : Integrable (fun t => f t*deriv (deriv g) t) :=
    (jacobi.Analysis.continuous_supported_mul hf.continuous isOpen_Ioo hs hgdd
      ).integrable_of_hasCompactSupport hc.mul_right
  have hadd3 := integral_add hi3.neg hi2
  simp only [Pi.neg_apply] at hadd3
  rw [← integral_neg,← hadd3]
  apply integral_congr_ae
  exact Eventually.of_forall (fun t => by
    by_cases ht : t ∈ tsupport f
    · have he := fullWavePhysical_equation a ha k (hs ht)
      change -(f t*deriv (deriv g) t)+targetPotential a ha t*f t*g t=_
      dsimp [g] at *
      nlinarith [congrArg (fun z : ℝ => f t*z) he]
    · simp [image_eq_zero_of_notMem_tsupport ht])

/-- Restriction of an actual continuous real function to the original physical interval.
Use: targetOperator_compact_test keeps the true continuous representatives of
both the test and its differential expression in the same L2 space.
Article: jacobi, Theorem 2.1.
-/
def physicalTestMap (f : ℝ → ℝ) (hf : Continuous f) : C(Interval,ℝ) :=
  ⟨fun t => f t,hf.comp continuous_subtype_val⟩

/-- Every original compactly supported C2 test lies in the full target
spectral domain, with its actual classical differential expression as graph output.
Use: targetOperator_compact_test evaluates H on every smooth compact test,
and targetGreen_compact_test obtains the exact Green inverse test identity.
Article: jacobi, Theorem 2.1.
Proof: the compact Green identity fixes every coefficient of the continuous
L2 differential expression. This very L2 vector witnesses membership in
the full weighted spectral graph. -/
theorem compact_test_graph (a : ℝ) (ha : -1<a) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ Ioo (0:ℝ) 1) :
    chebyshev2.Continuum.UnboundedDiagonalGraph (fullTargetBasis a ha)
      (jacobi.Bessel.sigma a ha)
      (ContinuousMap.toLp (𝕜 := ℝ) (p := 2) volume (physicalTestMap f hf.continuous))
      (ContinuousMap.toLp (𝕜 := ℝ) (p := 2) volume
        (physicalTestMap (testExpression a ha f) (testExpression_continuous a ha hf hs))) := by
  intro k
  simp only [(fullTargetBasis a ha).repr_apply_apply,← fullWaveMap_coefficient]
  have he (g : ℝ → ℝ) (hg : Continuous g) :
      (∫ t : Interval, (ContinuousMap.toLp (𝕜 := ℝ) (p := 2) volume
        (physicalTestMap g hg)) t*fullWaveMap a ha k t)=
          ∫ t : Interval,g t*fullWaveMap a ha k t := by
    apply integral_congr_ae
    filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 2) volume
      (physicalTestMap g hg)] with t ht
    rw [ht]
    rfl
  rw [he,he]
  exact compact_test_coefficient a ha k hf hc hs

/-- The genuine full unbounded target operator acts as -f''+V_alpha*f
on every compactly supported C2 interior test, hence on all C_c^infinity tests.
Use: targetGreen_compact_test tests the actual Green inverse against the
classical expression; this is the differential-realization assertion of Theorem 2.1.
Article: jacobi, Theorem 2.1.
Proof: the full spectral graph has the independently constructed continuous
differential expression as its unique output. -/
theorem targetOperator_compact_test (a : ℝ) (ha : -1<a) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ Ioo (0:ℝ) 1) :
    ∃ h : ContinuousMap.toLp (𝕜 := ℝ) (p := 2) volume
        (physicalTestMap f hf.continuous) ∈ (targetOperator a ha).domain,
      targetOperator a ha ⟨_,h⟩=ContinuousMap.toLp (𝕜 := ℝ) (p := 2) volume
        (physicalTestMap (testExpression a ha f) (testExpression_continuous a ha hf hs)) := by
  -- The graph witness is the actual L2 differential expression, not a
  -- postulated derivative or a domain-membership premise.
  have hg := compact_test_graph a ha hf hc hs
  refine ⟨⟨_,hg⟩,?_⟩
  exact chebyshev2.Continuum.UnboundedDiagonalGraph.unique
    (chebyshev2.Continuum.unboundedDiagonalOperator_graph _ _ _) hg

/-- The actual full Green inverse returns every compact C2 test when applied
to its true differential expression. No endpoint boundary premise is assumed.
Use: Proposition 2.2 obtains the distributional Green
equation from this identity and the already proved continuous kernel action.
Article: jacobi, Theorem 2.1.
Proof: substitute the proved compact-test graph in the existing full-domain
inverse identity for the same original self-adjoint target operator. -/
theorem targetGreen_compact_test (a : ℝ) (ha : -1<a) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ Ioo (0:ℝ) 1) :
    targetGreenOperator a ha (ContinuousMap.toLp (𝕜 := ℝ) (p := 2) volume
      (physicalTestMap (testExpression a ha f) (testExpression_continuous a ha hf hs)))=
      ContinuousMap.toLp (𝕜 := ℝ) (p := 2) volume (physicalTestMap f hf.continuous) := by
  obtain ⟨h,he⟩ := targetOperator_compact_test a ha hf hc hs
  rw [← he]
  exact targetGreen_operator_inverse a ha ⟨_,h⟩

/-- The physical continuous-to-L2 inclusion is injective, including endpoint values.
Use: targetGreen_test_identity upgrades the genuine L2 inverse identity to
its pointwise continuous kernel identity at every physical point.
Article: jacobi, Theorem 2.1.
Proof: subtype almost-everywhere equality becomes restricted Lebesgue
almost-everywhere equality; continuity on the closed interval determines
all its values, including the two null endpoints. -/
theorem physical_toLp_injective : Function.Injective
    (ContinuousMap.toLp (𝕜 := ℝ) (p := 2) volume : C(Interval,ℝ) → Space) := by
  intro F G h
  have he : (fun t : Interval => F t)=ᵐ[volume] fun t : Interval => G t :=
    (ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 2) volume F).symm.trans
      ((Lp.ext_iff.mp h).trans (ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 2) volume G))
  let p := projIcc (0:ℝ) 1 (by norm_num)
  have heR : (fun x : ℝ => F (p x))=ᵐ[volume.restrict (Icc (0:ℝ) 1)] fun x => G (p x) := by
    change ∀ᵐ x ∂volume.restrict (Icc (0:ℝ) 1), F (p x)=G (p x)
    rw [ae_restrict_iff_subtype measurableSet_Icc]
    filter_upwards [he] with t ht
    simpa only [p,projIcc_of_mem (by norm_num) t.property] using ht
  have hpoint := Measure.eqOn_Icc_of_ae_eq volume (by norm_num : (0:ℝ)≠1) heR
    (F.continuous.comp continuous_projIcc).continuousOn
    (G.continuous.comp continuous_projIcc).continuousOn
  ext t
  have ht := hpoint t.property
  simpa only [p,projIcc_of_mem (by norm_num) t.property] using ht

/-- The original continuous Green kernel satisfies its distributional source
identity at every physical point, for all compactly supported C2 tests.
Use: the Green-coordinate normalization uses this exact unit point source,
which fixes the derivative jump and excludes an arbitrary coordinate scale.
Article: jacobi, Proposition 2.2.
Proof: the full inverse identity holds in L2; its genuine continuous integral
representative and continuity of the test upgrade equality to every point. -/
theorem targetGreen_test_identity (a : ℝ) (ha : -1<a) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ Ioo (0:ℝ) 1) (t : Interval) :
    (∫ s : Interval, testExpression a ha f s*targetGreenKernel a ha t s)=f t := by
  let F := physicalTestMap (testExpression a ha f) (testExpression_continuous a ha hf hs)
  have he : targetGreenActionMap a ha (ContinuousMap.toLp (𝕜 := ℝ) (p := 2) volume F)=
      physicalTestMap f hf.continuous := by
    apply physical_toLp_injective
    rw [targetGreenActionMap_toLp]
    exact targetGreen_compact_test a ha hf hc hs
  have hp := congrArg (fun g : C(Interval,ℝ) => g t) he
  rw [targetGreenActionMap_apply] at hp
  change (∫ s : Interval, testExpression a ha f s*targetGreenKernel a ha t s)=_
  change (∫ s : Interval, _) = f t at hp
  rw [← hp]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 2) volume F] with s h
  rw [h]
  rfl

end
end jacobi.GelfandLevitan
