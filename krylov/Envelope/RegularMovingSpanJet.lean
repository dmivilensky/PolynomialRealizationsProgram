import krylov.Envelope.MovingSpanJet
import krylov.Envelope.JetSubspace
set_option autoImplicit false
/-!
Article: main_krylov, thm:E1, true regular moving-span jet closure.
Use: propagate actual virtual-correction first jets from genuine moving stored-step spans without assuming a trajectory expansion or supplied coefficient jets.
Source: the proved true inverse-Gram coordinate synthesis, actual C-one coefficient calculus and finite observed first-jet closure.
-/

namespace krylov.Envelope
noncomputable section
open Matrix Filter Topology krylov.Methods krylov.Stability
open scoped BigOperators Matrix.Norms.Elementwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p : ℕ}

/-- Every genuinely smooth vector constrained to a regular actual moving observed span inherits the true first-jet coherence of its original spanning observations.
Use: Every genuinely smooth vector constrained to a regular actual moving observed span inherits the true first-jet coherence of its original spanning observations.
Article: main_krylov, thm:E1, true regular moving-span jet closure.
Proof: Recover actual smooth inverse-Gram coordinates on a genuine open domain and apply the proved finite observed-combination first-jet rule. -/
theorem regular_moving_span_jet (K : Submodule ℝ E) (L : E →ₗ[ℝ] E)
    (s : ℝ → Fin p → E) (u : ℝ → E)
    (hs : ∀ i, ContDiffAt ℝ 1 (fun t => s t i) 0) (hu : ContDiffAt ℝ 1 u 0)
    (hGram : (crossGram (s 0) (s 0)).det≠0)
    (hspan : ∀ᶠ t in 𝓝 (0 : ℝ),u t∈Submodule.span ℝ (Set.range (s t)))
    (hj : ∀ i,(s 0 i,deriv (fun t => s t i) 0)∈jetSubspace K L) :
    (u 0,deriv u 0)∈jetSubspace K L := by
  -- Reconstruct the actual constrained vector on its genuine nonsingular neighborhood before differentiating its true coordinates.
  let G := fun t => crossGram (s t) (s t)
  let w := fun t i => -modelCoefficients (s t) (G t) (u t) i
  have hG (i j : Fin p) : ContDiffAt ℝ 1 (fun t => G t i j) 0 := (hs i).inner ℝ (hs j)
  have hw (i : Fin p) : ContDiffAt ℝ 1 (fun t => w t i) 0 :=
    (contDiff_modelCoefficients s G u 0 hs hG hu hGram i).neg
  have hGM : ContDiffAt ℝ 1 G 0 := contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr (hG i)
  have hdet : ContinuousAt (fun t => (G t).det) 0 := continuous_id.matrix_det.continuousAt.comp hGM.continuousAt
  have heq : (fun t => combine (s t) (w t))=ᶠ[𝓝 (0 : ℝ)]u := by
    filter_upwards [hdet.eventually_ne hGram,hspan] with t ht hst
    have hc := combine_gram_coordinates (s t) (u t) (isUnit_iff_ne_zero.mpr ht) hst
    simpa only [w,modelCoefficients,conjugacyCoefficients,G,Pi.neg_apply,neg_neg] using hc
  have hh := observed_combination_jet K L (fun i t => w t i) (fun i t => s t i)
    (fun i => deriv (fun t => w t i) 0) (fun i => deriv (fun t => s t i) 0) 0
    (fun i => ((hw i).differentiableAt (by norm_num)).hasDerivAt)
    (fun i => ((hs i).differentiableAt (by norm_num)).hasDerivAt) hj
  change (combine (s 0) (w 0),deriv (fun t => combine (s t) (w t)) 0)∈_ at hh
  have h0 : combine (s 0) (w 0)=u 0 := heq.self_of_nhds
  rwa [h0,heq.deriv_eq] at hh
end
end krylov.Envelope
