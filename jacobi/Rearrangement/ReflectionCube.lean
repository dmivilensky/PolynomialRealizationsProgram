import jacobi.Rearrangement.Polarization
import jacobi.Rearrangement.SpinPartition
import Mathlib.MeasureTheory.Integral.Pi

/-!
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Independent reflections in a finite product of real lines form a finite
group action. Each action map preserves the actual product Lebesgue measure.
An orbit sum therefore integrates to its cardinality times the original
integral. These facts supply the analytic side of the finite graph comparison.
Source: product measures, Haar invariance and finite-group averaging.
Use: encodes the two choices in a density or exponential-kernel factor.
-/
namespace jacobi.Rearrangement
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false

/-- One coordinate of the finite reflection group action.
Use: encodes the two choices in a density or exponential-kernel factor.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
-/
def spinCoordinate (a : ℝ) (σ : ZMod 2) (x : ℝ) : ℝ := if σ=0 then x else reflect a x

/-- Every spin has one of the two possible values.
Use: elementary verification of the reflection action and kernel identities.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: enumerate the two elements of ZMod 2 with kernel-checked finite elimination. -/
theorem spin_cases (σ : ZMod 2) : σ=0 ∨ σ=1 := by
  fin_cases σ <;> simp_all

/-- Spin zero leaves the coordinate fixed.
Use: identifies the two density values in each graph vertex factor.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: select the zero branch of the definition. -/
@[simp] theorem spinCoordinate_zero (a x : ℝ) : spinCoordinate a 0 x=x :=
  ite_eq_left rfl

/-- Spin one reflects the coordinate.
Use: identifies the other density value in each graph vertex factor.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: zero and one are distinct in ZMod 2. -/
@[simp] theorem spinCoordinate_one (a x : ℝ) : spinCoordinate a 1 x=reflect a x :=
  ite_eq_right (by decide)

/-- The two coordinate actions compose by spin addition.
Use: reflection-orbit sums do not depend on which point of the orbit is chosen.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: check the four spin pairs and cancel the double reflection. -/
theorem spinCoordinate_add (a : ℝ) (σ τ : ZMod 2) (x : ℝ) :
    spinCoordinate a σ (spinCoordinate a τ x)=spinCoordinate a (σ+τ) x := by
  have h11 : (1 : ZMod 2)+1=0 := by decide
  rcases spin_cases σ with rfl | rfl <;> rcases spin_cases τ with rfl | rfl <;>
    simp only [h11,zero_add,add_zero,spinCoordinate_zero,spinCoordinate_one,reflect_reflect]

/-- The coordinatewise reflection action as an actual measurable equivalence.
Use: the finite-dimensional change of variables for every cyclic moment.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
-/
def cubeReflection {V : Type*} (a : ℝ) (σ : V → ZMod 2) : (V → ℝ) ≃ᵐ (V → ℝ) where
  toFun z v := spinCoordinate a (σ v) (z v)
  invFun z v := spinCoordinate a (σ v) (z v)
  left_inv z := by
    funext v
    rcases spin_cases (σ v) with h | h <;> simp [h]
  right_inv z := by
    funext v
    rcases spin_cases (σ v) with h | h <;> simp [h]
  measurable_toFun := Measurable.of_eval (fun v => by
    change Measurable (fun z : V → ℝ => spinCoordinate a (σ v) (z v))
    by_cases h : σ v=0
    · simpa only [spinCoordinate,ite_eq_left h] using
        (measurable_pi_apply v : Measurable (fun z : V → ℝ => z v))
    · have hr : Measurable (fun z : V → ℝ => 2*a-z v) := by fun_prop
      simpa only [spinCoordinate,ite_eq_right h,reflect] using hr)
  measurable_invFun := Measurable.of_eval (fun v => by
    change Measurable (fun z : V → ℝ => spinCoordinate a (σ v) (z v))
    by_cases h : σ v=0
    · simpa only [spinCoordinate,ite_eq_left h] using
        (measurable_pi_apply v : Measurable (fun z : V → ℝ => z v))
    · have hr : Measurable (fun z : V → ℝ => 2*a-z v) := by fun_prop
      simpa only [spinCoordinate,ite_eq_right h,reflect] using hr)

/-- Every finite-coordinate reflection preserves the product Lebesgue measure.
Use: transports absolute integrability and exact integrals on R^p.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: each coordinate map preserves volume, so the pushforward of the product
measure is the product of the unchanged coordinate measures. -/
theorem cubeReflection_preserve {V : Type*} [Fintype V] (a : ℝ) (σ : V → ZMod 2) :
    MeasurePreserving (cubeReflection a σ) volume volume := by
  -- Finiteness of each mapped coordinate measure on compact sets follows from its exact map identity.
  have hm (v : V) : Measure.map (spinCoordinate a (σ v)) volume=volume := by
    rcases spin_cases (σ v) with h | h
    · have he : spinCoordinate a 0=(id : ℝ → ℝ) := funext (spinCoordinate_zero a)
      rw [h,he]
      exact (MeasurePreserving.id (volume : Measure ℝ)).map_eq
    · have he : spinCoordinate a 1=(fun x => 2*a-x) := funext (spinCoordinate_one a)
      rw [h,he]
      exact (volume.measurePreserving_sub_left (2*a)).map_eq
  have hσ (v : V) : SigmaFinite (Measure.map (spinCoordinate a (σ v)) volume) := by
    rw [hm v]
    infer_instance
  refine ⟨(cubeReflection a σ).measurable,?_⟩
  change Measure.map (fun z v => spinCoordinate a (σ v) (z v)) (Measure.pi fun _ : V => volume)=_
  have hmeas (v : V) : Measurable (spinCoordinate a (σ v)) := by
    change Measurable (fun x : ℝ => if σ v=0 then x else 2*a-x)
    by_cases h : σ v=0 <;> simp only [h,ite_true,ite_false] <;> fun_prop
  rw [Measure.pi_map_pi (fun v => (hmeas v).aemeasurable)]
  simp_rw [hm]
  rfl

/-- The reflection orbit sum of a function on a finite real product space.
Use: combines the graph partition comparison with ordinary product integration.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
-/
def cubeOrbit {V : Type*} [Fintype V] (F : (V → ℝ) → ℝ) (a : ℝ) (z : V → ℝ) : ℝ :=
  ∑ σ : V → ZMod 2, F (cubeReflection a σ z)

/-- Independent physical reflections compose by addition of their spin vectors.
Use: reindexing reflection-orbit sums when moving a tuple into the preferred half-space.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: apply the proved one-coordinate action law at every coordinate. -/
theorem cubeReflection_add {V : Type*} (a : ℝ) (σ τ : V → ZMod 2) (z : V → ℝ) :
    cubeReflection a σ (cubeReflection a τ z)=cubeReflection a (σ+τ) z := by
  funext v
  exact spinCoordinate_add a (σ v) (τ v) (z v)

/-- A complete reflection-orbit sum is unchanged by choosing a different orbit representative.
Use: applies the preferred-half-space partition comparison at arbitrary physical tuples.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: composition adds the fixed spin vector, a permutation of the finite spin group. -/
theorem cubeOrbit_reflect {V : Type*} [Fintype V] (F : (V → ℝ) → ℝ)
    (a : ℝ) (τ : V → ZMod 2) (z : V → ℝ) :
    cubeOrbit F a (cubeReflection a τ z)=cubeOrbit F a z := by
  unfold cubeOrbit
  simp_rw [cubeReflection_add]
  exact Equiv.sum_comp (Equiv.addRight τ) (fun σ => F (cubeReflection a σ z))

/-- Every reflection orbit sum is integrable whenever its original integrand is integrable.
Use: all finite spin sums may be integrated and compared as actual Lebesgue integrals.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: transport integrability by each measure-preserving reflection and take the finite sum. -/
theorem cubeOrbit_integrable {V : Type*} [Fintype V] {F : (V → ℝ) → ℝ}
    (hF : Integrable F) (a : ℝ) : Integrable (cubeOrbit F a) := by
  apply integrable_finsetSum
  intro σ _
  exact ((cubeReflection_preserve a σ).integrable_comp hF.aestronglyMeasurable).mpr hF

/-- Integrating the complete reflection orbit multiplies the integral by 2^|V|.
Use: cancels the common positive orbit multiplicity in every cyclic polarization inequality.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: use the proved measure-preserving substitutions and linearity for an
absolutely integrable finite sum, then count the two choices per coordinate. -/
theorem integral_cubeOrbit {V : Type*} [Fintype V] {F : (V → ℝ) → ℝ}
    (hF : Integrable F) (a : ℝ) :
    (∫ z, cubeOrbit F a z)=(2 : ℝ)^Fintype.card V*(∫ z, F z) := by
  -- All terms are the same integral after independent real reflection substitutions.
  have hi (σ : V → ZMod 2) : Integrable (fun z => F (cubeReflection a σ z)) :=
    ((cubeReflection_preserve a σ).integrable_comp hF.aestronglyMeasurable).mpr hF
  unfold cubeOrbit
  rw [integral_finsetSum _ (fun σ _ => hi σ)]
  simp_rw [(cubeReflection_preserve a _).integral_comp' F]
  simp [Fintype.card_pi,ZMod.card]

end
end jacobi.Rearrangement
