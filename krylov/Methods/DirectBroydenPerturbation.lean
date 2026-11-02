import krylov.Methods.DirectBroydenNativeBounds
import krylov.Methods.DirectBroydenStep
set_option autoImplicit false
/-!
Article: main_krylov, prop:classical(c), primitive native Broyden perturbations.
Use: derive actual chronological model bounds, true denominator domains and
observed cross-pair rates from precisely the primitive source assumptions.
Source: positive reference curvature, real operator continuity, finite
compact Broyden parameter bounds and the norm big-O product calculus.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference krylov.Stability
open Set Filter Topology Asymptotics
open scoped InnerProductSpace
variable {E α : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Primitive observed-pair perturbations for the original direct Broyden
comparison. The actual step limits need no first-order convergence rate
and the actual convex interpolation schedule need not be continuous.
Use: every model, secant error and quadratic comparison is derived from
these primitive data; no model bound or model correctness field is supplied.
Article: main_krylov, prop:classical(c), apE:broyden. -/
structure DirectBroydenPerturbation (l : Filter α) (t : α → ℝ) (p : ℕ) where
  reference : E →L[ℝ] E
  reference_symmetric : reference.toLinearMap.IsSymmetric
  reference_positive : ∀ w : E,w≠0 → 0 < inner ℝ w (reference w)
  initial : E →L[ℝ] E
  initial_symmetric : initial.toLinearMap.IsSymmetric
  initial_positive : ∀ w : E,w≠0 → 0 < inner ℝ w (initial w)
  step : α → ℕ → E
  image : α → ℕ → E
  referenceStep : ℕ → E
  referenceStep_ne : ∀ i<p,referenceStep i≠0
  step_limit : ∀ i<p,Tendsto (fun z => step z i) l (𝓝 (referenceStep i))
  image_error : ∀ i<p,(fun z => image z i-reference (step z i)) =O[l] t
  cross_error : ∀ i<p,∀ j<p,i≠j → (fun z => inner ℝ (step z i) (reference (step z j))) =O[l] t
  parameter : α → ℕ → ℝ
  parameter_cube : ∀ᶠ z in l,∀ i<p,0≤parameter z i ∧ parameter z i≤1
  scale_limit : Tendsto t l (𝓝 0)

/-- The genuine observed pair array of the primitive perturbation.
Use: retain the original actually executed chronological pair recursion.
Article: main_krylov, prop:classical(c), apE:broyden. -/
def directBroydenPerturbedPairs {l : Filter α} {t : α → ℝ} {p : ℕ}
    (D : DirectBroydenPerturbation (E := E) l t p) (z : α) (i : ℕ) : E × E := (D.step z i,D.image z i)

/-- The literal native direct model of the original primitive perturbation.
Use: the second-order comparison concerns this actual executed model.
Article: main_krylov, prop:classical(c), apE:broyden. -/
def directBroydenPerturbedModel {l : Filter α} {t : α → ℝ} {p : ℕ}
    (D : DirectBroydenPerturbation (E := E) l t p) (z : α) (k : ℕ) : E →L[ℝ] E :=
  directBroydenNative D.initial (D.parameter z) (directBroydenPerturbedPairs D z) k

/-- The actual observed images and step/image curvatures converge to the
genuine positive reference values under the original primitive hypotheses.
Use: all native observed inverse curvatures and positive pair domains are
derived, with no first-order step convergence assumption.
Article: main_krylov, prop:classical(c), apE:broyden.
Proof: the genuine image error tends to zero and the actual reference
operator is continuous on the actual convergent step. Real inner-product
continuity then gives the true positive reference secant curvature. -/
theorem directBroydenPerturbation_limits {l : Filter α} {t : α → ℝ} {p : ℕ}
    (D : DirectBroydenPerturbation (E := E) l t p) (i : ℕ) (hi : i<p) :
    Tendsto (fun z => D.image z i) l (𝓝 (D.reference (D.referenceStep i))) ∧
    Tendsto (fun z => inner ℝ (D.step z i) (D.image z i)) l
      (𝓝 (inner ℝ (D.referenceStep i) (D.reference (D.referenceStep i)))) := by
  have he := (D.image_error i hi).trans_tendsto D.scale_limit
  have href := D.reference.continuous.continuousAt.tendsto.comp (D.step_limit i hi)
  have hy : Tendsto (fun z => D.image z i) l (𝓝 (D.reference (D.referenceStep i))) := by
    simpa only [Function.comp_def,sub_add_cancel,zero_add] using he.add href
  exact ⟨hy,(D.step_limit i hi).inner hy⟩

/-- Every actual pair and actual interpolation coordinate has its native
boundedness and genuine positive observed-curvature neighborhood.
Use: supply actual primitive factors of the true direct-update estimates.
Article: main_krylov, prop:classical(c), apE:broyden.
Proof: actual pair limits bound both vectors and the actual reciprocal
positive curvature; the original cube directly bounds its parameter. -/
theorem directBroydenPerturbation_pair_bounds {l : Filter α} {t : α → ℝ} {p : ℕ}
    (D : DirectBroydenPerturbation (E := E) l t p) (i : ℕ) (hi : i<p) :
    (fun z => D.step z i) =O[l] (fun _ => (1 : ℝ)) ∧
    (fun z => D.image z i) =O[l] (fun _ => (1 : ℝ)) ∧
    (fun z => (inner ℝ (D.step z i) (D.image z i))⁻¹) =O[l] (fun _ => (1 : ℝ)) ∧
    (fun z => D.parameter z i) =O[l] (fun _ => (1 : ℝ)) ∧
    ∀ᶠ z in l,0 < inner ℝ (D.step z i) (D.image z i) := by
  have hh := directBroydenPerturbation_limits D i hi
  have hp := D.reference_positive _ (D.referenceStep_ne i hi)
  refine ⟨(D.step_limit i hi).isBigO_one ℝ,hh.1.isBigO_one ℝ,
    (hh.2.inv₀ hp.ne').isBigO_one ℝ,?_,?_⟩
  · apply IsBigO.of_bound 1
    filter_upwards [D.parameter_cube] with z hz
    simpa only [norm_one,mul_one,Real.norm_eq_abs,abs_of_nonneg (hz i hi).1] using (hz i hi).2
  · exact hh.2.eventually (lt_mem_nhds hp)

/-- Actual cross pairings of distinct observed steps and images are
first order under the original primitive reference conjugacy errors.
Use: derive both native new/old pair cross rates in the model induction.
Article: main_krylov, prop:classical(c), apE:broyden.
Proof: split the actual image into its reference action and actual image
error; the true other step is bounded by its genuine limit. -/
theorem directBroydenPerturbation_cross {l : Filter α} {t : α → ℝ} {p : ℕ}
    (D : DirectBroydenPerturbation (E := E) l t p) (i j : ℕ)
    (hi : i<p) (hj : j<p) (hne : i≠j) :
    (fun z => inner ℝ (D.step z i) (D.image z j)) =O[l] t := by
  have h := real_inner_bigO (fun z => D.step z i)
    (fun z => D.image z j-D.reference (D.step z j)) _ _
    ((D.step_limit i hi).isBigO_one ℝ) (D.image_error j hj)
  have h' : (fun z => inner ℝ (D.step z i) (D.image z j-D.reference (D.step z j))) =O[l] t := by
    simpa only [one_mul] using h
  exact (h'.add (D.cross_error i hi j hj hne)).congr_left (fun z => by
    rw [inner_sub_right]
    ring)

/-- Genuine native models and their next inverse old curvatures are
bounded, and all native symmetries and both denominator domains hold
eventually, under just the original primitive perturbation assumptions.
Use: close the actual chronological induction without any supplied
updated-model, inverse-curvature or second-order comparison hypothesis.
Article: main_krylov, prop:classical(c), apE:broyden.
Proof: actual pair limits are positive reference pairs. The proved compact
native cube theorem gives actual bounds. Finitely many genuine observed
positive-curvature neighborhoods and true nonnegative parameters give
native model positivity, hence its actual next old curvature domain. -/
theorem directBroydenPerturbation_model_bounds {l : Filter α} {t : α → ℝ} {p : ℕ}
    (D : DirectBroydenPerturbation (E := E) l t p) (k : ℕ) (hk : k<p) :
    (fun z => directBroydenPerturbedModel D z k) =O[l] (fun _ => (1 : ℝ)) ∧
    (fun z => (inner ℝ (D.step z k) (directBroydenPerturbedModel D z k (D.step z k)))⁻¹)
      =O[l] (fun _ => (1 : ℝ)) ∧
    ∀ᶠ z in l,(directBroydenPerturbedModel D z k).toLinearMap.IsSymmetric ∧
      inner ℝ (D.step z k) (directBroydenPerturbedModel D z k (D.step z k))≠0 ∧
      inner ℝ (D.step z k) (D.image z k)≠0 := by
  have hb := directBroydenNative_bounds D.initial D.initial_symmetric D.initial_positive k
    (fun i => (D.referenceStep i,D.reference (D.referenceStep i)))
    (fun i hi => D.reference_positive _ (D.referenceStep_ne i (by omega)))
    (D.referenceStep k) (D.referenceStep_ne k hk) l D.parameter (directBroydenPerturbedPairs D)
    (fun z => D.step z k) (D.parameter_cube.mono (fun _ hz i hi => hz i (by omega)))
    (fun i hi => (D.step_limit i (by omega)).prodMk_nhds (directBroydenPerturbation_limits D i (by omega)).1)
    (D.step_limit k hk)
  refine ⟨hb.1,hb.2,?_⟩
  have hp : ∀ᶠ z in l,∀ i : Fin (k+1),0 < inner ℝ (D.step z i.val) (D.image z i.val) :=
    eventually_all.mpr (fun i => (directBroydenPerturbation_pair_bounds D i.val (by omega)).2.2.2.2)
  filter_upwards [D.parameter_cube,hp] with z htheta hpair
  have hmodel := directBroydenNative_positive D.initial D.initial_symmetric D.initial_positive
    (D.parameter z) (directBroydenPerturbedPairs D z) k
    (fun i hi => (htheta i (by omega)).1) (fun i hi => hpair ⟨i,by omega⟩)
  have hs : D.step z k≠0 := by
    intro hz
    have h := hpair ⟨k,by omega⟩
    rw [hz,inner_zero_left] at h
    exact lt_irrefl _ h
  exact ⟨hmodel.1,(hmodel.2 _ hs).ne',(hpair ⟨k,by omega⟩).ne'⟩

end
end krylov.Methods
