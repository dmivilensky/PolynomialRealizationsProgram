import chebyshev2.Packing.IntervalCost
import chebyshev2.Continuum.Transport
import chebyshev2.Continuum.AtomicOperator

/-!
Article: chebyshev2, Theorem 2.3.
Lemma 4(v) applied to the explicit interval-to-atom coupling.
Use: `chebyshev2.Packing.Blocks.density_atomic_transport` feeds
`chebyshev2.Packing.Jacobi.density_atomic_traceBound` (The actual density feature operator is
within 2/sqrt(N) of its atomic one).
Proof chain: `chebyshev2.Packing.packed_spectral_distance` — chebyshev2, Theorem 2.3; Block
packing, exact masses/energy and spectral distance.
-/
namespace chebyshev2.Packing
noncomputable section
open MeasureTheory Real Set
open scoped BigOperators NNReal
set_option backward.isDefEq.respectTransparency false

namespace Blocks
variable {ι : Type*} [Fintype ι] (B : Blocks ι)

/--
One cell of the article's mass-moving coupling.

Use: `chebyshev2.Packing.Blocks.coupling` uses this definition in the displayed
construction of `coupling`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.
-/
def couplingCell (y : ι → ℝ) (i : ι) : Measure (ℝ × ℝ) :=
  (Real.toNNReal (B.height i^2) •
    ((volume.restrict (Ioc (B.left i) (B.right i))).map (fun x : ℝ => (x,y i))) : Measure (ℝ × ℝ))

/--
Supplies the typeclass structure specified by `IsFiniteMeasure (B.couplingCell y i)`. This lets
subsequent generic library results apply to this concrete type.

Use: `chebyshev2.Packing.Blocks.coupling_finite` uses this typeclass instance in the
displayed construction of `coupling_finite`. Its inputs and component formulas are fixed by
that definition.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
instance couplingCell_finite (y : ι → ℝ) (i : ι) : IsFiniteMeasure (B.couplingCell y i) := by
  let : IsFiniteMeasure (volume.restrict (Ioc (B.left i) (B.right i))) :=
    isFiniteMeasure_restrict.mpr (by rw [volume_Ioc]; exact ENNReal.ofReal_ne_top)
  unfold couplingCell
  infer_instance

/--
Defines `coupling` of type `Measure (ℝ × ℝ)` by `∑ i, B.couplingCell y i`.

Use: `chebyshev2.Packing.Blocks.coupling_finite` uses this definition in the displayed
construction of `coupling_finite`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.
-/
def coupling (y : ι → ℝ) : Measure (ℝ × ℝ) := ∑ i, B.couplingCell y i

/--
Supplies the typeclass structure specified by `IsFiniteMeasure (B.coupling y)`. This lets
subsequent generic library results apply to this concrete type.

Use: `chebyshev2.Packing.Blocks.density_atomic_transport` uses this typeclass instance to
establish the stated quantitative bound `TraceBound (densityOperator B.closedDensity -
atomicOperator (fun i => B.height i^2 * (B.right i-B.left i)) y) (2 * sqrt (2 * (∫ x,
B.closedDensity x) * ∫ z, |z.1-z.2| ∂B.coupling y))`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
instance coupling_finite (y : ι → ℝ) : IsFiniteMeasure (B.coupling y) := by unfold coupling; infer_instance

omit [Fintype ι] in
/--
Integrating against a cell is exactly the weighted interval integral.

Exact identity `(∫ z, f z ∂B.couplingCell y i) = B.height i^2 • ∫ x in Ioc (B.left i) (B.right
i), f (x,y i)`.

Use: `chebyshev2.Packing.Blocks.coupling_integral` uses this identity to establish exact
identity `(∫ z, f z ∂B.coupling y) = ∑ i, B.height i^2 • ∫ x in Ioc (B.left i) (B.right i), f
(x,y i)`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem couplingCell_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (y : ι → ℝ) (i : ι) (f : ℝ × ℝ → E) (hf : Continuous f) :
    (∫ z, f z ∂B.couplingCell y i) = B.height i^2 • ∫ x in Ioc (B.left i) (B.right i), f (x,y i) := by
  rw [couplingCell,integral_smul_nnreal_measure]
  have hmap : Measurable (fun x : ℝ => (x,y i)) := measurable_id.prodMk measurable_const
  rw [integral_map hmap.aemeasurable hf.aestronglyMeasurable]
  simp only [NNReal.smul_def, Real.coe_toNNReal _ (sq_nonneg _)]

omit [Fintype ι] in
/--
Integrability of the displayed function: `Integrable f (B.couplingCell y i)`.

Use: `chebyshev2.Packing.Blocks.coupling_integrable` uses this integrability result to
establish integrability of the displayed function: `Integrable f (B.coupling y)`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
theorem couplingCell_integrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (y : ι → ℝ) (i : ι) (f : ℝ × ℝ → E) (hf : Continuous f) :
    Integrable f (B.couplingCell y i) := by
  have hmap : Measurable (fun x : ℝ => (x,y i)) := measurable_id.prodMk measurable_const
  have hi : IntegrableOn (fun x : ℝ => f (x,y i)) (Ioc (B.left i) (B.right i)) volume :=
    (hf.comp (continuous_id.prodMk continuous_const)).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  exact ((integrable_map_measure hf.aestronglyMeasurable hmap.aemeasurable).mpr hi).smul_measure_nnreal

/--
Integrability of the displayed function: `Integrable f (B.coupling y)`.

Use: `chebyshev2.Packing.Blocks.density_atomic_transport` uses this integrability result to
establish the stated quantitative bound `TraceBound (densityOperator B.closedDensity -
atomicOperator (fun i => B.height i^2 * (B.right i-B.left i)) y) (2 * sqrt (2 * (∫ x,
B.closedDensity x) * ∫ z, |z.1-z.2| ∂B.coupling y))`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Proof: Use the identities/estimates `chebyshev2.Packing.Blocks.couplingCell_integrable`
with the arguments shown in the proof.
-/
theorem coupling_integrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (y : ι → ℝ) (f : ℝ × ℝ → E) (hf : Continuous f) : Integrable f (B.coupling y) := by
  unfold coupling
  exact integrable_finsetSum_measure.mpr (fun i _ => B.couplingCell_integrable y i f hf)

/--
Exact identity `(∫ z, f z ∂B.coupling y) = ∑ i, B.height i^2 • ∫ x in Ioc (B.left i) (B.right
i), f (x,y i)`.

Use: `chebyshev2.Packing.Blocks.coupling_cost` rewrites with this identity to establish the
stated quantitative bound `(∫ z, |z.1-z.2| ∂B.coupling y) ≤ ∑ i, B.height i^2 * (B.right
i-B.left i)^2/2`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem coupling_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (y : ι → ℝ) (f : ℝ × ℝ → E) (hf : Continuous f) :
    (∫ z, f z ∂B.coupling y) = ∑ i, B.height i^2 • ∫ x in Ioc (B.left i) (B.right i), f (x,y i) := by
  rw [coupling,integral_finsetSum_measure (fun i _ => B.couplingCell_integrable y i f hf)]
  exact Finset.sum_congr rfl (fun i _ => B.couplingCell_integral y i f hf)

/--
The finite sum also records its exact total mass.

Exact identity `(B.coupling y).real univ = ∑ i, B.height i^2 * (B.right i-B.left i)`.

Use: `chebyshev2.Packing.Blocks.density_atomic_transport` uses this identity to establish
the stated quantitative bound `TraceBound (densityOperator B.closedDensity - atomicOperator
(fun i => B.height i^2 * (B.right i-B.left i)) y) (2 * sqrt (2 * (∫ x, B.closedDensity x) * ∫
z, |z.1-z.2| ∂B.coupling y))`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem coupling_mass (y : ι → ℝ) : (B.coupling y).real univ =
    ∑ i, B.height i^2 * (B.right i-B.left i) := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  have h : (∫ _z, (1 : ℝ) ∂B.coupling y) =
      ∑ i, B.height i^2 * (B.right i-B.left i) := by
    rw [coupling,integral_finsetSum_measure (fun i _ => integrable_const 1)]
    apply Finset.sum_congr rfl
    intro i _
    rw [B.couplingCell_integral y i (fun _ => (1 : ℝ)) continuous_const,integral_const]
    simp [measureReal_def,volume_Ioc,ENNReal.toReal_ofReal (sub_nonneg.mpr (B.left_le_right i))]
  simpa only [integral_const,smul_eq_mul,mul_one] using h

/--
The actual transport cost, bounded uniformly over the location inside each cell.

The stated quantitative bound `(∫ z, |z.1-z.2| ∂B.coupling y) ≤ ∑ i, B.height i^2 * (B.right
i-B.left i)^2/2`.

Use: `chebyshev2.Packing.Jacobi.coupling_cost_bound` uses this bound to establish the
stated quantitative bound `(∫ z, |z.1-z.2| ∂(blocks J hN ht hir).coupling
(J.representationPoint hN)) ≤ 1/(2*(N : ℝ))`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Proof: Use the identities/estimates `chebyshev2.Packing.Blocks.coupling_integral`,
`chebyshev2.Packing.interval_transport_cost_bound` with the arguments shown in the proof.
-/
theorem coupling_cost (y : ι → ℝ) (hy : ∀ i, y i ∈ Icc (B.left i) (B.right i)) :
    (∫ z, |z.1-z.2| ∂B.coupling y) ≤ ∑ i, B.height i^2 * (B.right i-B.left i)^2/2 := by
  rw [B.coupling_integral y (fun z => |z.1-z.2|) ((continuous_fst.sub continuous_snd).abs)]
  apply Finset.sum_le_sum
  intro i _
  simpa only [smul_eq_mul,mul_div_assoc] using
    mul_le_mul_of_nonneg_left (interval_transport_cost_bound (hy i)) (sq_nonneg (B.height i))

open chebyshev2.Continuum

/--
Exact identity `measureOperator ((B.coupling y).map Prod.snd) = atomicOperator (fun i =>
B.height i^2 * (B.right i-B.left i)) y`.

Use: `chebyshev2.Packing.Blocks.density_atomic_transport` uses this identity to establish
the stated quantitative bound `TraceBound (densityOperator B.closedDensity - atomicOperator
(fun i => B.height i^2 * (B.right i-B.left i)) y) (2 * sqrt (2 * (∫ x, B.closedDensity x) * ∫
z, |z.1-z.2| ∂B.coupling y))`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem coupling_second_operator (y : ι → ℝ) :
    measureOperator ((B.coupling y).map Prod.snd) =
      atomicOperator (fun i => B.height i^2 * (B.right i-B.left i)) y := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  rw [measureOperator,integral_map measurable_snd.aemeasurable featureProjection_continuous.aestronglyMeasurable]
  rw [B.coupling_integral y (fun z => featureProjection z.2) (featureProjection_continuous.comp continuous_snd)]
  unfold atomicOperator
  apply Finset.sum_congr rfl
  intro i _
  change B.height i^2 • (∫ _x : ℝ in Ioc (B.left i) (B.right i), featureProjection (y i)) = _
  rw [integral_const]
  simp only [measureReal_def,Measure.restrict_apply_univ,volume_Ioc,ENNReal.toReal_ofReal (sub_nonneg.mpr (B.left_le_right i)),smul_smul]

/--
Exact identity `measureOperator ((B.coupling y).map Prod.fst) = densityOperator
B.closedDensity`.

Use: `chebyshev2.Packing.Blocks.density_atomic_transport` uses this identity to establish
the stated quantitative bound `TraceBound (densityOperator B.closedDensity - atomicOperator
(fun i => B.height i^2 * (B.right i-B.left i)) y) (2 * sqrt (2 * (∫ x, B.closedDensity x) * ∫
z, |z.1-z.2| ∂B.coupling y))`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Proof: Separate `x ∈ Ioc (B.left i) (B.right i)` from its negation; prove the goal under each
of these mutually exclusive hypotheses. Intersect the eventual or almost-everywhere hypotheses,
then prove the asserted relation at an arbitrary point in that intersection. Identify the
summands/integrands on their required domain before replacing the sum or integral.
-/
theorem coupling_first_operator (y : ι → ℝ) :
    measureOperator ((B.coupling y).map Prod.fst) = densityOperator B.closedDensity := by
  -- Separate `x ∈ Ioc (B.left i) (B.right i)` from its negation; prove the goal under each of
  -- these mutually exclusive hypotheses.
  rw [measureOperator,integral_map measurable_fst.aemeasurable featureProjection_continuous.aestronglyMeasurable]
  rw [B.coupling_integral y (fun z => featureProjection z.1) (featureProjection_continuous.comp continuous_fst)]
  have ha : densityOperator B.closedDensity = densityOperator B.density := by
    apply integral_congr_ae
    filter_upwards [B.closedDensity_ae] with x hx
    rw [hx]
  rw [ha]
  change _ = ∫ x, (∑ i, (Ioc (B.left i) (B.right i)).indicator (fun _ => B.height i^2) x) • featureProjection x
  have he : (fun x => (∑ i, (Ioc (B.left i) (B.right i)).indicator (fun _ => B.height i^2) x) • featureProjection x) =
      (fun x => ∑ i, (Ioc (B.left i) (B.right i)).indicator (fun _ => B.height i^2) x • featureProjection x) :=
    funext (fun x => Finset.sum_smul (s := Finset.univ)
      (f := fun i => (Ioc (B.left i) (B.right i)).indicator (fun _ => B.height i^2) x) (x := featureProjection x))
  rw [he,integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    have he (x : ℝ) : (Ioc (B.left i) (B.right i)).indicator (fun _ => B.height i^2) x • featureProjection x =
        (Ioc (B.left i) (B.right i)).indicator (fun x => B.height i^2 • featureProjection x) x := by
      by_cases hx : x ∈ Ioc (B.left i) (B.right i)
      · rw [indicator_of_mem hx,indicator_of_mem hx]
      · rw [indicator_of_notMem hx,indicator_of_notMem hx]
        exact zero_smul ℝ (featureProjection x)
    simp_rw [he]
    rw [integral_indicator measurableSet_Ioc,integral_smul]
  · intro i _
    exact densityOperator_integrable ((integrableOn_const (hs := by rw [volume_Ioc]; exact ENNReal.ofReal_ne_top) :
      IntegrableOn (fun _ : ℝ => B.height i^2) (Ioc (B.left i) (B.right i)) volume).integrable_indicator measurableSet_Ioc)

/--
Lemma 4(v) applied to the explicit interval-to-atom coupling.

The stated quantitative bound `TraceBound (densityOperator B.closedDensity - atomicOperator
(fun i => B.height i^2 * (B.right i-B.left i)) y) (2 * sqrt (2 * (∫ x, B.closedDensity x) * ∫
z, |z.1-z.2| ∂B.coupling y))`.

Use: `chebyshev2.Packing.Jacobi.density_atomic_traceBound` uses this identity to establish
the precise assertion is `TraceBound (densityOperator (density J hN ht hir) - atomicOperator
(atomicWeight J) (J.representationPoint hN)) (2 / sqrt (N : ℝ))`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Proof: Use the identities/estimates `chebyshev2.Continuum.measureOperator_transport`,
`chebyshev2.Packing.Blocks.coupling_integrable`,
`chebyshev2.Packing.Blocks.closed_mass` with the arguments shown in the proof.
-/
theorem density_atomic_transport (y : ι → ℝ) :
    TraceBound (densityOperator B.closedDensity - atomicOperator
      (fun i => B.height i^2 * (B.right i-B.left i)) y)
      (2 * sqrt (2 * (∫ x, B.closedDensity x) * ∫ z, |z.1-z.2| ∂B.coupling y)) := by
  have h := measureOperator_transport (B.coupling y)
    (B.coupling_integrable y _ ((continuous_fst.sub continuous_snd).abs))
  rwa [B.coupling_first_operator,B.coupling_second_operator,B.coupling_mass,← B.closed_mass] at h

end Blocks
end
end chebyshev2.Packing
