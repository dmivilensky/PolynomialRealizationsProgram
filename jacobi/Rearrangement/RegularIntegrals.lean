import jacobi.Rearrangement.RegularShape
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Every continuous function of a regular density that vanishes at zero has the
same integral throughout the finite orbit and its uniform closure. In
particular the limiting radial density has exactly the original mass, energy
and root mass. Integrability and continuity are proved from the actual common
compact support, rather than included as assumptions on a replacement density.
Source: equimeasurability of polarizations and Lebesgue dominated convergence.
Use: global integrals of the density and its continuous transforms reduce to a finite interval.
-/
namespace jacobi.Rearrangement
noncomputable section
open Set Real MeasureTheory Filter
open jacobi.Variational
open scoped NNReal Topology BoundedContinuousFunction ENNReal
set_option backward.isDefEq.respectTransparency false

/-- A regular function vanishes off its common closed support interval.
Use: global integrals of the density and its continuous transforms reduce to a finite interval.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: a point outside [-R,R] has absolute value larger than R. -/
theorem regular_zero_compl {f : ℝ →ᵇ ℝ} {R C : ℝ} {K : ℝ≥0}
    (hf : f ∈ regularFamily R C K) {x : ℝ} (hx : x ∉ Icc (-R) R) : f x=0 := by
  apply hf.2.2
  have : x < -R ∨ R < x := by simpa only [mem_Icc,not_and_or,not_le] using hx
  rcases this with h | h
  · exact (by linarith : R < -x).le.trans (neg_le_abs x)
  · exact h.le.trans (le_abs_self x)

/-- Regular functions have actual compact support.
Use: constructs genuine finite-energy densities from the compact polarization family.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: their support lies in the compact interval [-R,R]. -/
theorem regular_compactSupport {f : ℝ →ᵇ ℝ} {R C : ℝ} {K : ℝ≥0}
    (hf : f ∈ regularFamily R C K) : HasCompactSupport (f : ℝ → ℝ) :=
  HasCompactSupport.intro isCompact_Icc (fun _ hx => regular_zero_compl hf hx)

/-- Continuous transforms vanishing at zero are integrable on every actual regular density.
Use: mass, energy, root mass and continuous distribution tests all have legitimate real integrals.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: the transform is continuous and its support stays in the same compact interval. -/
theorem regular_integrable_comp {f : ℝ →ᵇ ℝ} {R C : ℝ} {K : ℝ≥0}
    (hf : f ∈ regularFamily R C K) {F : ℝ → ℝ} (hF : Continuous F) (h0 : F 0=0) :
    Integrable (fun x => F (f x)) :=
  (hF.comp f.continuous).integrable_of_hasCompactSupport ((regular_compactSupport hf).comp_left h0)

/-- Whole-line and interval integrals coincide for the supported density transforms.
Use: dominated convergence on a finite interval proves continuity of the actual whole-line functional.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: the transform is exactly zero outside the interval. -/
theorem regular_integral_interval {f : ℝ →ᵇ ℝ} {R C : ℝ} {K : ℝ≥0}
    (hf : f ∈ regularFamily R C K) {F : ℝ → ℝ} (h0 : F 0=0) :
    (∫ x, F (f x))=∫ x in Icc (-R) R, F (f x) :=
  (setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => by rw [regular_zero_compl hf hx,h0])).symm

/-- Continuous density transforms have a continuous integral on the regular family.
Use: their exact invariance under finite polarizations survives in the orbit closure.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: restrict to the common finite interval and bound the transform uniformly
on the compact range [0,C]; then apply dominated convergence to continuous evaluation. -/
theorem regular_integral_continuous {R C : ℝ} {K : ℝ≥0} {F : ℝ → ℝ}
    (hF : Continuous F) (h0 : F 0=0) :
    ContinuousOn (fun f : ℝ →ᵇ ℝ => ∫ x, F (f x)) (regularFamily R C K) := by
  -- The dominating constant is obtained from a compact range, independently of the varying density.
  obtain ⟨B,hB⟩ := isCompact_Icc.bddAbove_image (K := Icc 0 C) hF.norm.continuousOn
  have hc : ContinuousOn (fun f : ℝ →ᵇ ℝ => ∫ x in Icc (-R) R, F (f x))
      (regularFamily R C K) := by
    apply continuousOn_of_dominated (bound := fun _ => B)
    · intro f _
      exact (hF.comp f.continuous).aestronglyMeasurable
    · intro f hf
      exact Eventually.of_forall fun x => hB (mem_image_of_mem _ (hf.2.1 x))
    · exact integrableOn_const isCompact_Icc.measure_ne_top
    · exact Eventually.of_forall fun x =>
        (hF.comp (BoundedContinuousFunction.lipschitz_eval_const x).continuous).continuousOn
  exact hc.congr (fun f hf => regular_integral_interval hf h0)

/-- A regular bounded continuous function defines an actual admissible density.
Use: the rearranged limit participates in the same operator and variational constructions as the original density.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
-/
def regularDensity (f : ℝ →ᵇ ℝ) {R C : ℝ} {K : ℝ≥0} (hf : f ∈ regularFamily R C K) : Density where
  value := f
  measurable := f.continuous.measurable
  nonneg x := (hf.2.1 x).1
  integrable := regular_integrable_comp hf continuous_id rfl
  energy_integrable := regular_integrable_comp hf (F := fun y : ℝ => y^(3/2 : ℝ)) (Real.continuous_rpow_const (by norm_num))
    (Real.zero_rpow (by norm_num : (3/2 : ℝ) ≠ 0))

/-- Every finite orbit element preserves each integrable continuous density transform.
Use: establishes exact normalization identities before taking the radial orbit limit.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: induction uses the proved elementary Borel integral invariance and
reflection invariance of Lebesgue measure. -/
theorem RegularOrbit.integral_comp {f g : ℝ →ᵇ ℝ} {R C : ℝ} {K : ℝ≥0}
    (hg : RegularOrbit f g) (hf : f ∈ regularFamily R C K)
    {F : ℝ → ℝ} (hF : Continuous F) (h0 : F 0=0) :
    (∫ x, F (g x))=∫ x, F (f x) := by
  -- Integrability is re-established from the common regular bounds at each polarization step.
  induction hg with
  | base => rfl
  | @polarize q hg a _ ih =>
    exact (integral_polarize_comp q.continuous.measurable hF.measurable
      (regular_integrable_comp (hg.regular hf) hF h0) a).trans ih
  | @mirror q _ ih =>
    exact (integral_neg_eq_self (fun x => F (q x)) volume).trans ih

/-- Every member of the closed regular orbit preserves the whole continuous distribution functional.
Use: exact mass, energy and root-mass identities for the constructed radial limit.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: the regular-family integral is continuous, so its level set is closed;
the finite orbit lies in that level set by the proved induction. -/
theorem regularOrbit_integral_comp {f g : ℝ →ᵇ ℝ} {R C : ℝ} {K : ℝ≥0}
    (hf : f ∈ regularFamily R C K) (hg : g ∈ closure {q | RegularOrbit f q})
    {F : ℝ → ℝ} (hF : Continuous F) (h0 : F 0=0) :
    (∫ x, F (g x))=∫ x, F (f x) := by
  -- Intersecting with the closed regular family makes relative continuity sufficient for closure preservation.
  have hc := (regular_integral_continuous (R := R) (C := C) (K := K) hF h0).preimage_isClosed_of_isClosed
    (regularFamily_closed R C K) (isClosed_singleton (x := ∫ x, F (f x)))
  have hi : {q | RegularOrbit f q} ⊆ regularFamily R C K ∩
      (fun q : ℝ →ᵇ ℝ => ∫ x, F (q x)) ⁻¹' {∫ x, F (f x)} :=
    fun _ hq => ⟨hq.regular hf,hq.integral_comp hf hF h0⟩
  exact (closure_minimal hi hc hg).2

/-- Mass, energy and extended root mass are exactly preserved throughout the regular orbit closure.
Use: the radial replacement respects every normalization in the article's root and root-free relaxations.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: specialize continuous integral preservation to identity, the 3/2 power
and square root; finite integrability identifies the latter's ENNReal integral. -/
theorem regularOrbit_integrals {f g : ℝ →ᵇ ℝ} {R C : ℝ} {K : ℝ≥0}
    (hf : f ∈ regularFamily R C K) (hg : g ∈ closure {q | RegularOrbit f q})
    (hgr : g ∈ regularFamily R C K) :
    (regularDensity g hgr).mass=(regularDensity f hf).mass ∧
    (regularDensity g hgr).energy=(regularDensity f hf).energy ∧
    (regularDensity g hgr).rootMass=(regularDensity f hf).rootMass := by
  -- Square-root integrability follows from the common compact support, rather than from an extra bound.
  refine ⟨regularOrbit_integral_comp hf hg continuous_id rfl,
    regularOrbit_integral_comp hf hg (F := fun y : ℝ => y^(3/2 : ℝ))
      (Real.continuous_rpow_const (by norm_num)) (Real.zero_rpow (by norm_num)),?_⟩
  have h := regularOrbit_integral_comp hf hg Real.continuous_sqrt Real.sqrt_zero
  change (∫⁻ x, ENNReal.ofReal (sqrt (g x)))=∫⁻ x, ENNReal.ofReal (sqrt (f x))
  rw [← ofReal_integral_eq_lintegral_ofReal (regular_integrable_comp hgr Real.continuous_sqrt Real.sqrt_zero)
      (Eventually.of_forall (fun _ => sqrt_nonneg _)),
    ← ofReal_integral_eq_lintegral_ofReal (regular_integrable_comp hf Real.continuous_sqrt Real.sqrt_zero)
      (Eventually.of_forall (fun _ => sqrt_nonneg _)),h]

end
end jacobi.Rearrangement
