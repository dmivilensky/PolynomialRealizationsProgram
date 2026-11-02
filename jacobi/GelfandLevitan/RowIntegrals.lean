import jacobi.GelfandLevitan.TransformationOperator

/-!
Article: jacobi, Proposition C.2.
Continuous Hilbert rows can be integrated against arbitrary original
L2 inputs. These are Bochner integrals in the original Hilbert space,
and the actual Volterra adjoint is precisely such a row integral.
Use: justifies the adjoint formula and all subsequent row-integral pairings in the factorization.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set MeasureTheory Filter jacobi.Reference
open scoped Topology InnerProductSpace
attribute [local instance] Measure.Subtype.measureSpace

/-- A continuous Hilbert row times any original L2 input is Bochner integrable.
Use: justifies the adjoint formula and all subsequent row-integral pairings in the factorization.
Article: jacobi, Proposition C.2.
Source: Bochner integration of an L1 scalar times a bounded continuous vector function.
Proof: the physical interval has finite measure, so L2 is contained in L1; bound the actual row by its continuous-function supremum norm. -/
theorem rowIntegral_integrable (R : C(Interval,halfSubspace)) (v : halfSubspace) :
    Integrable (fun t:Interval => (v:Space) t • R t) :=
  (space_integrable (v:Space)).smul_bdd ‖R‖ R.continuous.aestronglyMeasurable
    (Eventually.of_forall R.norm_coe_le_norm)

/-- The genuine Hilbert-valued integral of a continuous row against an original input.
Use: represents the actual transformation adjoint and permits the GL factorization to use vector-valued Fubini.
Article: jacobi, Proposition C.2.
-/
def rowIntegral (R : C(Interval,halfSubspace)) (v : halfSubspace) : halfSubspace :=
  ∫ t:Interval,(v:Space) t • R t

/-- Pairing a genuine row integral is the original scalar integral of row pairings.
Use: verifies the Volterra adjoint formula and the double-integral covariance calculation.
Article: jacobi, Proposition C.2.
Source: bounded linear functionals commute with Bochner integrals.
Proof: use real symmetry and the community integral-inner theorem for the proved integrable Hilbert-valued function. -/
theorem rowIntegral_inner (R : C(Interval,halfSubspace)) (v w : halfSubspace) :
    inner ℝ (rowIntegral R v) w=∫ t:Interval,(v:Space) t*inner ℝ (R t) w := by
  rw [real_inner_comm, rowIntegral,← integral_inner (rowIntegral_integrable R v)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun t => by
    dsimp only
    rw [real_inner_smul_right w (R t) ((v:Space) t),real_inner_comm])

/-- The true zero-extended row family on the common compact spatial domain.
Use: its original Bochner integral is transformationOperator_adjoint.
Article: jacobi, Proposition C.2.
-/
def volterraRows (a : ℝ) (ha : -1<a) : C(Interval,halfSubspace) :=
  (solutionRowMap a ha).comp halfClamp

/-- Pairing the true Volterra operator is the integral of its actual continuous row pairings.
Use: identifies its adjoint with the original Hilbert-valued row integral, without any pointwise adjoint assumption.
Article: jacobi, Proposition C.2.
Proof: the half-domain projection preserves pairing with the actual supported input. Substitute the genuine continuous L2 representative in the original integral inner product. -/
theorem transformationOperator_inner (a : ℝ) (ha : -1<a) (v w : halfSubspace) :
    inner ℝ (transformationOperator a ha v) w=
      ∫ t:Interval,(w:Space) t*inner ℝ (solutionRow a ha (halfClamp t)) v := by
  change inner ℝ (halfSubspace.orthogonalProjectionOnto
    (ContinuousMap.toLp (𝕜 := ℝ) (p := 2) volume (transformationActionMap a ha v))) w=_
  rw [halfSubspace.inner_orthogonalProjectionOnto_eq_of_mem_right,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 2) volume (transformationActionMap a ha v)] with t ht
  rw [ht]
  rfl

/-- The actual adjoint of the original Volterra transformation is its true Hilbert-valued row integral.
Use: makes the covariance terms in the GL operator factorization literal integrals of the actual constructed solution rows.
Article: jacobi, Proposition C.2.
Proof: test against every genuine Hilbert vector. The community adjoint identity and the proved original Volterra integral pairing agree with the actual Bochner row integral. -/
theorem transformationOperator_adjoint (a : ℝ) (ha : -1<a) (v : halfSubspace) :
    (transformationOperator a ha).adjoint v=rowIntegral (volterraRows a ha) v := by
  apply ext_inner_right ℝ
  intro w
  rw [ContinuousLinearMap.adjoint_inner_left,← real_inner_comm v (transformationOperator a ha w),
    transformationOperator_inner,rowIntegral_inner]
  rfl

/-- A genuine continuous covariance kernel formed from two continuous Hilbert rows.
Use: bounds the double-integral covariance in rowIntegral_inner_twice and the GL factorization.
Article: jacobi, Proposition C.2.
-/
def rowCovariance (R S : C(Interval,halfSubspace))
    (T : halfSubspace →L[ℝ] halfSubspace) : C(Interval×Interval,ℝ) :=
  ⟨fun p => inner ℝ (T (R p.1)) (S p.2),
    (T.continuous.comp (R.continuous.comp continuous_fst)).inner
      (S.continuous.comp continuous_snd)⟩

/-- The original double covariance integrand is integrable for arbitrary genuine L2 inputs.
Use: all changes of order in the GL factorization are justified by this actual domination bound.
Article: jacobi, Proposition C.2.
Proof: the independent-variable product of the two original L1 inputs is integrable and the genuine continuous covariance kernel is uniformly bounded. -/
theorem rowCovariance_integrable (R S : C(Interval,halfSubspace))
    (T : halfSubspace →L[ℝ] halfSubspace) (v w : halfSubspace) :
    Integrable (fun p:Interval×Interval =>
      ((v:Space) p.1*(w:Space) p.2)*inner ℝ (T (R p.1)) (S p.2))
      (volume.prod volume) :=
  ((space_integrable (v:Space)).mul_prod (space_integrable (w:Space))).mul_bdd
    (rowCovariance R S T).continuous.aestronglyMeasurable
    (Eventually.of_forall (rowCovariance R S T).norm_coe_le_norm)

/-- Pairing two original row integrals through a bounded operator is the genuine double covariance integral.
Use: evaluates the K*(v) covariance terms in the original GL factorization, using the actual solution rows.
Article: jacobi, Proposition C.2.
Source: vector-valued Fubini and bounded linear maps commuting with Bochner integrals.
Proof: commute the bounded operator with the first actual row integral, move each inner product through the corresponding integrable vector function, and use Fubini for the independently dominated product integrand. -/
theorem rowIntegral_inner_twice (R S : C(Interval,halfSubspace))
    (T : halfSubspace →L[ℝ] halfSubspace) (v w : halfSubspace) :
    inner ℝ (T (rowIntegral R v)) (rowIntegral S w)=
      ∫ p:Interval×Interval,((v:Space) p.1*(w:Space) p.2)*
        inner ℝ (T (R p.1)) (S p.2) ∂(volume.prod volume) := by
  -- Every interchange is in the original Hilbert space and the original spatial product measure.
  rw [rowIntegral,← T.integral_comp_comm (rowIntegral_integrable R v),
    real_inner_comm,← integral_inner (T.integrable_comp (rowIntegral_integrable R v)),
    integral_prod _ (rowCovariance_integrable R S T v w)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun t => by
    dsimp only
    rw [map_smul,real_inner_smul_right (rowIntegral S w) (T (R t)) ((v:Space) t),
      rowIntegral_inner,
      ← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall (fun s => by dsimp only; rw [real_inner_comm]; ring))

end
end jacobi.GelfandLevitan
