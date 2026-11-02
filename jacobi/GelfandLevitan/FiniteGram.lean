import jacobi.GelfandLevitan.FiniteFeatures
import jacobi.GelfandLevitan.CandidateRows
import jacobi.GelfandLevitan.KernelRowEquation

/-!
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
The actual finite feature system is exactly the printed I+C*X(t),
where X is the genuine original physical Gram integral. Each entry
has its true physical endpoint derivative h_i(t)h_j(t), including
the midpoint one-sided interpretation. These are the original data
needed to differentiate the finite-system inverse.
Use: finiteFeatureSystem_apply identifies the actual finite system with I+C*X, and finiteFeatureGram_integral identifies X with the article's genuine original interval integrals.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference
open scoped Topology InnerProductSpace
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] realSolution realSlope coefficientVector

/-- The genuine Gram matrix of the original physically restricted finite reference features.
Use: finiteFeatureSystem_apply identifies the actual finite system with I+C*X, and finiteFeatureGram_integral identifies X with the article's genuine original interval integrals.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def finiteFeatureGram (a : ℝ) (ha : -1<a) (N : ℕ) (t : ℝ) : Matrix (FeatureIndex N) (FeatureIndex N) ℝ :=
  fun i j => inner ℝ (finiteFeatureVector a ha t i) (finiteFeatureVector a ha t j)

/-- The original finite reference feature as a continuous real-coordinate function, unchanged on the physical half interval.
Use: finiteFeatureGram_integral and its actual FTC derivative use globally continuous integrands while preserving every genuine original physical value.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def finiteFeatureWave (a : ℝ) (ha : -1<a) {N : ℕ} (i : FeatureIndex N) : C(ℝ,ℝ) :=
  (⟨fun r : HalfInterval => realSolution a (finiteFeatureEnergy a ha i) r,
    continuous_iff_continuousAt.mpr (fun r => (realSolution_continuousAt ha _ r.property).comp_of_eq
      continuous_subtype_val.continuousAt rfl)⟩ : C(HalfInterval,ℝ)).comp halfParameterClamp

/-- The continuously extended original finite feature retains its exact genuine physical value.
Use: the genuine Gram endpoint derivative is exactly the article's original h_i(t)h_j(t).
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: the explicit half-interval projection fixes the original physical point. -/
theorem finiteFeatureWave_value {a x : ℝ} (ha : -1<a) {N : ℕ} (i : FeatureIndex N)
    (hx : x∈Icc (0:ℝ) (1/2)) :
    finiteFeatureWave a ha i x=realSolution a (finiteFeatureEnergy a ha i) x := by
  change realSolution a _ ((halfParameterClamp x):ℝ)=_
  rw [show halfParameterClamp x=(⟨x,hx⟩:HalfInterval) from Set.projIcc_of_mem (by norm_num) hx]

/-- The genuine finite coefficient system acts exactly as the original I+C*X(t).
Use: differentiating the actual finite-system inverse uses this same literal original finite Gram matrix, rather than an abstract unrelated invertible matrix.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: evaluate the actual weighted feature analysis of the genuine synthesis and distribute the original Hilbert inner product over the actual finite feature sum. -/
theorem finiteFeatureSystem_apply (a : ℝ) (ha : -1<a) (N : ℕ) (t : ℝ)
    (y : FeatureIndex N→ℝ) (i : FeatureIndex N) :
    finiteFeatureSystem a ha N t y i=y i+finiteFeatureWeight a ha i*
      ∑ j : FeatureIndex N,finiteFeatureGram a ha N t i j*y j := by
  change y i+finiteFeatureWeight a ha i*inner ℝ (finiteFeatureVector a ha t i) (finiteFeatureSynthesis a ha N t y)=_
  rw [finiteFeatureSynthesis_apply,inner_sum]
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  rw [real_inner_smul_right (finiteFeatureVector a ha t i) (finiteFeatureVector a ha t j) (y j)]
  change y j*inner ℝ _ _=inner ℝ _ _*y j
  ring

/-- The genuine finite physical Gram entry is exactly its original subtype-prefix integral.
Use: finiteFeatureGram_integral converts this same actual original Hilbert Gram matrix to the literal original real-coordinate integral before differentiation.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: each actual restricted feature is the genuine physical-prefix candidate vector. Substitute their proved original indicator representatives in the true L2 pairing; the actual original product integral is exactly its prefix restriction. -/
theorem finiteFeatureGram_prefix (a : ℝ) (ha : -1<a) (N : ℕ) (t : HalfInterval) (i j : FeatureIndex N) :
    finiteFeatureGram a ha N t i j=
      ∫ r : Interval in prefixSet (t:ℝ),realSolution a (finiteFeatureEnergy a ha j) (halfTime r)*
        realSolution a (finiteFeatureEnergy a ha i) (halfTime r) := by
  -- The actual zero extensions and the original physical integration measure are retained throughout.
  have hfeature (k : FeatureIndex N) : finiteFeatureVector a ha t k=
      candidateVector t (realHalfWave a ha (finiteFeatureEnergy a ha k)) := by
    rw [finiteFeatureVector,coefficientVector,fullCoefficientVector]
    rfl
  rw [finiteFeatureGram,hfeature i,hfeature j]
  change inner ℝ (candidateVector t (realHalfWave a ha (finiteFeatureEnergy a ha i)):Space)
    (candidateVector t (realHalfWave a ha (finiteFeatureEnergy a ha j)):Space)=_
  rw [L2.inner_def,← integral_indicator (prefixSet_measurable (t:ℝ))]
  apply integral_congr_ae
  filter_upwards [candidateVector_ae t (realHalfWave a ha (finiteFeatureEnergy a ha i)),
    candidateVector_ae t (realHalfWave a ha (finiteFeatureEnergy a ha j))] with r hi hj
  rw [hi,hj]
  by_cases hp : r∈prefixSet (t:ℝ)
  · rw [indicator_of_mem hp,indicator_of_mem hp,indicator_of_mem hp]
    rfl
  · rw [indicator_of_notMem hp,indicator_of_notMem hp,indicator_of_notMem hp]
    exact inner_zero_left _

/-- The actual finite physical Gram matrix is precisely the original real-coordinate Gram integral at every original endpoint.
Use: finiteFeatureGram_hasDerivWithinAt obtains the genuine derivative of the original finite matrix entry by the community FTC.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: the actual original Gram entry has its genuine physical-prefix integral. The explicit original half clamp agrees with the existing unit-coordinate half clamp; use the already proved unchanged physical-prefix interval identity and real product commutativity. -/
theorem finiteFeatureGram_integral (a : ℝ) (ha : -1<a) (N : ℕ) (t : HalfInterval) (i j : FeatureIndex N) :
    finiteFeatureGram a ha N t i j=
      ∫ r in (0:ℝ)..(t:ℝ),finiteFeatureWave a ha i r*finiteFeatureWave a ha j r := by
  -- The actual original subtype and real interval integrals are identified before any endpoint derivative is taken.
  rw [finiteFeatureGram_prefix]
  have hp := prefix_integral (fun r : ℝ => finiteFeatureWave a ha i r*finiteFeatureWave a ha j r)
    (show (t:ℝ)∈Icc (0:ℝ) 1 from ⟨t.property.1,by linarith [t.property.2]⟩)
  rw [← hp]
  apply setIntegral_congr_fun (prefixSet_measurable (t:ℝ))
  intro r _
  change _=realSolution a (finiteFeatureEnergy a ha i) ((halfParameterClamp r):ℝ)*
    realSolution a (finiteFeatureEnergy a ha j) ((halfParameterClamp r):ℝ)
  rw [halfParameterClamp_unit,halfClamp_val]
  ring

/-- Every genuine original finite Gram entry has its actual displayed endpoint derivative on the whole required physical strip, including its midpoint one-sided derivative.
Use: supplies the actual original finite-system derivative X'=h*h^T used to differentiate its independently proved genuine inverse and derive the finite transformed differential equation.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Source: mathlib's endpoint fundamental theorem of calculus.
Proof: the actual original Gram entry equals its genuine continuous-integrand primitive at every physical point. Apply the community FTC and restrict to the unchanged physical strip, retaining its original selected-solution endpoint values. -/
theorem finiteFeatureGram_hasDerivWithinAt {a d t : ℝ} (ha : -1<a) (hd : 0<d)
    (N : ℕ) (ht : t∈Icc d (1/2)) (i j : FeatureIndex N) :
    HasDerivWithinAt (fun x => finiteFeatureGram a ha N x i j)
      (realSolution a (finiteFeatureEnergy a ha i) t*realSolution a (finiteFeatureEnergy a ha j) t) (Icc d (1/2)) t := by
  -- The finite matrix derivative is proved from the actual original integral; differentiability of the infinite kernel is not used.
  have hc : Continuous (fun r : ℝ => finiteFeatureWave a ha i r*finiteFeatureWave a ha j r) :=
    (finiteFeatureWave a ha i).continuous.mul (finiteFeatureWave a ha j).continuous
  have h := (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable (μ := volume) (0:ℝ) t)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).hasDerivWithinAt (s := Icc d (1/2))
  have hp : t∈Icc (0:ℝ) (1/2) := ⟨(hd.trans_le ht.1).le,ht.2⟩
  rw [finiteFeatureWave_value ha i hp,finiteFeatureWave_value ha j hp] at h
  apply h.congr
  · intro x hx
    exact finiteFeatureGram_integral a ha N ⟨x,⟨(hd.trans_le hx.1).le,hx.2⟩⟩ i j
  · exact finiteFeatureGram_integral a ha N ⟨t,hp⟩ i j

end
end jacobi.GelfandLevitan
