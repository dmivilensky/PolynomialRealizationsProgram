import krylov.Envelope.FirstJets
import krylov.Stability.ContDiffSolve
import krylov.Methods.WindowCoordinates

/-!
Article: main_krylov, apB:lem:filtration, genuine zero-query moving-span derivative.
Use: prove that the derivative of an actual zero reference correction remains
in the true reference correction span, even when its primitive representation
uses redundant observed vectors. Its actual moving-span restriction is enough.
Source: the proved genuine inverse-Gram coordinate synthesis, actual C-one
model-coefficient regularity and the real observed-combination derivative rule.
-/

namespace krylov.Envelope
noncomputable section
open Matrix Filter Topology krylov.Methods krylov.Stability
open scoped Matrix.Norms.Elementwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p : ℕ}

/-- The derivative of a genuinely zero reference query constrained to a real regular moving observed span belongs to its true reference span.
Use: The derivative of a genuinely zero reference query constrained to a real regular moving observed span belongs to its true reference span.
Article: main_krylov, apB:lem:filtration, genuine zero-query moving-span derivative.
Proof: The actual inverse Gram reconstructs the query on a genuine open domain. Its real coordinate vector is C-one and zero at the reference, so the true derivative contains only reference span vectors; no coefficient-derivative outside the span survives. -/
theorem zero_moving_span_derivative (s : ℝ → Fin p → E) (u : ℝ → E)
    (hs : ∀ i, ContDiffAt ℝ 1 (fun t => s t i) 0) (hu : ContDiffAt ℝ 1 u 0)
    (hzero : u 0=0) (hGram : (crossGram (s 0) (s 0)).det≠0)
    (hspan : ∀ᶠ t in 𝓝 (0 : ℝ), u t∈Submodule.span ℝ (Set.range (s t))) :
    deriv u 0∈Submodule.span ℝ (Set.range (s 0)) := by
  -- Use actual inverse-Gram coordinates, so redundant original observed coefficients require no unjustified zero-coefficient assumption.
  let G := fun t => crossGram (s t) (s t)
  let w := fun t i => -modelCoefficients (s t) (G t) (u t) i
  have hG (i j : Fin p) : ContDiffAt ℝ 1 (fun t => G t i j) 0 := (hs i).inner ℝ (hs j)
  have hw (i : Fin p) : ContDiffAt ℝ 1 (fun t => w t i) 0 :=
    (contDiff_modelCoefficients s G u 0 hs hG hu hGram i).neg
  have hw0 (i : Fin p) : w 0 i=0 := by
    have hz : coordinates (s 0) (0 : E)=0 := by funext j;exact inner_zero_right _
    simp only [w,hzero,modelCoefficients,hz,Matrix.mulVec_zero,Pi.neg_apply,Pi.zero_apply,neg_zero]
  have hGM : ContDiffAt ℝ 1 G 0 := contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr (hG i)
  have hdet : ContinuousAt (fun t => (G t).det) 0 := continuous_id.matrix_det.continuousAt.comp hGM.continuousAt
  have hunit : ∀ᶠ t in 𝓝 (0 : ℝ), IsUnit (G t).det :=
    (hdet.eventually_ne hGram).mono fun _ ht => isUnit_iff_ne_zero.mpr ht
  -- Synthesize the genuine constrained query on its actual nonsingular neighborhood before differentiating it.
  have heq : (fun t => combine (s t) (w t))=ᶠ[𝓝 (0 : ℝ)] u := by
    filter_upwards [hunit,hspan] with t ht hst
    have hc := combine_gram_coordinates (s t) (u t) ht hst
    simpa only [w,modelCoefficients,conjugacyCoefficients,G,Pi.neg_apply,neg_neg] using hc
  have hd := hasDerivAt_observedCombination (fun i t => w t i) (fun i t => s t i)
    (fun i => deriv (fun t => w t i) 0) (fun i => deriv (fun t => s t i) 0) 0
    (fun i => ((hw i).differentiableAt (by simp)).hasDerivAt)
    (fun i => ((hs i).differentiableAt (by simp)).hasDerivAt)
  have hactual : HasDerivAt u (∑ i, deriv (fun t => w t i) 0 • s 0 i) 0 := by
    simpa only [hw0,zero_smul,zero_add] using hd.congr_of_eventuallyEq heq.symm
  rw [hactual.deriv]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩)
end
end krylov.Envelope
