import jacobi.GelfandLevitan.FiniteKernelAction
import jacobi.GelfandLevitan.SylvesterInverse

/-!
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Use: the finite feature system represents the literal original F^(N), without a separate distinct-energy reduction.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology InnerProductSpace
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] coefficientVector normingRatio norming

/-- The actual finite target/reference feature index, retaining all original terms even when energies coincide.
Use: the finite feature system represents the literal original F^(N), without a separate distinct-energy reduction.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
abbrev FeatureIndex (N : ℕ) := Fin N×Bool

/-- The original energy of each actual finite reference feature.
Use: finiteFeatureVector and the later differential identities use precisely the original f(.,sigma_k) and f(.,tau_k).
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def finiteFeatureEnergy (a : ℝ) (ha : -1<a) {N : ℕ} (i : FeatureIndex N) : ℝ :=
  if i.2 then jacobi.Bessel.sigma a ha i.1 else eigenvalue a i.1

/-- The original nonzero signed norming weight of each literal finite spectral feature.
Use: the finite weighted analysis forms exactly the original finite F^(N), preserving its positive target and negative reference contributions.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def finiteFeatureWeight (a : ℝ) (ha : -1<a) {N : ℕ} (i : FeatureIndex N) : ℝ :=
  if i.2 then normingRatio a ha i.1/norming a i.1 else -(1/norming a i.1)

/-- The genuine original finite reference feature vector restricted to its actual physical prefix.
Use: finiteFeatureSynthesis and finiteFeatureAnalysis factor the actual finite GL compression in the original half-Hilbert space.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def finiteFeatureVector (a : ℝ) (ha : -1<a) {N : ℕ} (t : ℝ) (i : FeatureIndex N) : halfSubspace :=
  cutoffProjection t (coefficientVector a ha (finiteFeatureEnergy a ha i))

/-- The genuine bounded synthesis of the actual finite physical reference features.
Use: the original finite GL operator is identity plus synthesis composed with weighted analysis; the swapped system is the article's actual finite feature system.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def finiteFeatureSynthesis (a : ℝ) (ha : -1<a) (N : ℕ) (t : ℝ) :
    (FeatureIndex N→ℝ) →L[ℝ] halfSubspace :=
  ∑ i : FeatureIndex N,(ContinuousLinearMap.toSpanSingleton ℝ (finiteFeatureVector a ha t i)) ∘L
    ContinuousLinearMap.proj i

/-- The genuine original weighted feature coefficient map on the physical prefix.
Use: the swapped finite system is exactly I+C*X, while its original product with synthesis is the proved actual finite compressed F operator.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def finiteFeatureAnalysis (a : ℝ) (ha : -1<a) (N : ℕ) (t : ℝ) :
    halfSubspace →L[ℝ] (FeatureIndex N→ℝ) :=
  ContinuousLinearMap.pi (fun i => finiteFeatureWeight a ha i • innerSL ℝ (finiteFeatureVector a ha t i))

/-- The actual finite feature system on the original finite coefficient space.
Use: finiteFeatureSystem_isUnit proves its genuine inverse exists from the actual finite GL coercivity, so the original finite kernel admits a differentiable finite-system representation.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def finiteFeatureSystem (a : ℝ) (ha : -1<a) (N : ℕ) (t : ℝ) :
    (FeatureIndex N→ℝ) →L[ℝ] (FeatureIndex N→ℝ) :=
  ContinuousLinearMap.id ℝ (FeatureIndex N→ℝ)+finiteFeatureAnalysis a ha N t ∘L finiteFeatureSynthesis a ha N t

/-- The actual finite synthesis evaluates to the original finite linear combination of the genuine physical reference features.
Use: finiteFeatureFactorization and the finite kernel representation use precisely the source finite feature combination, rather than an abstract coordinate substitute.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: evaluate the original finite sum of coordinate-projection and scalar-span maps. -/
theorem finiteFeatureSynthesis_apply (a : ℝ) (ha : -1<a) (N : ℕ) (t : ℝ) (y : FeatureIndex N→ℝ) :
    finiteFeatureSynthesis a ha N t y=∑ i : FeatureIndex N,y i • finiteFeatureVector a ha t i := by
  simp only [finiteFeatureSynthesis,sum_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply,ContinuousLinearMap.toSpanSingleton_apply]

/-- The original finite GL compression is exactly identity plus the synthesis/analysis product of its true original weighted physical features.
Use: finiteFeatureSystem_isUnit applies the genuine Sylvester inverse identity to the original finite system and the independently proved actual finite GL inverse.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: expand the original finite spectral corrections and commute the genuine physical projection through each original rank-one term. The two Bool features give exactly its original positive target and negative reference term. The finite coefficient and original Hilbert sums are identical. -/
theorem finiteFeatureFactorization (a : ℝ) (ha : -1<a) (N : ℕ) (t : ℝ) :
    ContinuousLinearMap.id ℝ halfSubspace+finiteFeatureSynthesis a ha N t ∘L finiteFeatureAnalysis a ha N t=
      finiteCompressedPositive a ha N t := by
  -- The equality is evaluated on arbitrary actual source inputs, preserving every original finite spectral term.
  apply ContinuousLinearMap.ext
  intro v
  change v+finiteFeatureSynthesis a ha N t (finiteFeatureAnalysis a ha N t v)=
    v+cutoffProjection t (finiteKernelOperator a ha N (cutoffProjection t v))
  congr 1
  rw [finiteFeatureSynthesis_apply]
  simp only [FeatureIndex,Fintype.sum_prod_type,Fintype.sum_bool,finiteFeatureAnalysis,
    ContinuousLinearMap.pi_apply,smul_apply,innerSL_apply_apply,smul_eq_mul]
  change _=cutoffProjection t ((∑ k∈Finset.range N,rankCorrection a ha k) (cutoffProjection t v))
  rw [sum_apply,map_sum,← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  rw [rankCorrection]
  simp only [sub_apply,smul_apply,InnerProductSpace.rankOne_apply,map_sub,map_smul]
  have hinner (E : ℝ) : inner ℝ (coefficientVector a ha E) (cutoffProjection t v)=
      inner ℝ (cutoffProjection t (coefficientVector a ha E)) v :=
    (cutoffProjection_symmetric t _ _).symm
  simp only [finiteFeatureWeight,finiteFeatureVector,finiteFeatureEnergy,Bool.false_eq_true,
    ite_true,ite_false,hinner,smul_smul]
  module

/-- The genuine original finite feature system is invertible at every physical endpoint for every sufficiently long original spectral prefix.
Use: its actual inverse gives the finite kernel's original smooth coefficient functions in the differential-equation proof, including coincident target/reference energies without an added feature-independence assumption.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: the actual finite GL compressed operators are eventually proved units uniformly in t. Their exact original feature factorization and the proved Sylvester inverse identity give the genuine swapped finite coefficient-system inverse. -/
theorem finiteFeatureSystem_isUnit (a : ℝ) (ha : -1<a) :
    ∀ᶠ N : ℕ in atTop,∀ t : ℝ,IsUnit (finiteFeatureSystem a ha N t) := by
  obtain ⟨B,_hB,hFinite⟩ := finiteCompressedPositive_isUnit a ha
  filter_upwards [hFinite] with N hN t
  apply isUnit_id_add_swap_comp (finiteFeatureSynthesis a ha N t) (finiteFeatureAnalysis a ha N t)
  rw [finiteFeatureFactorization]
  exact (hN t).1

end
end jacobi.GelfandLevitan
