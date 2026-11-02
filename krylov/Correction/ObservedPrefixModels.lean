import krylov.Correction.ObservedSearchDomains
import krylov.Correction.ObservedAugmentedGram
import krylov.Stability.ObservedCanonical
import krylov.Correction.GatedCutoffAlgebra

/-!
Article: main_krylov, thm:UCq and thm:UCg(iii), original observed model conditioning.
Use: Derive the actual ordinary defect and measured spectral decisions plus
the original canonical step-normalized model bound from genuine prefix data.
Source: real observed conjugacy inverses, actual metric pairing invariance,
normalized augmented Gram geometry and the proved measured gate margins.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Stability
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- Genuine old recorded angles and observed pair errors derive every actual inverse and gate decision and the original step-normalized model distance at a nonzero computed direction.
Use: Complete the uniform ordinary-RFC model and acceptance part under condition (N).
Article: main_krylov, thm:UCq and thm:UCg(iii).
Proof: The true normalized old cross Gram supplies the actual conjugacy inverse, hence original image conjugacy. Its real augmented unit Gram and pair errors give the model distance and measured spectral margin. Exact primal/dual model equality transfers the real decision to the original policy window. The genuine relative pair-defect bound proves the actual ordinary defect test as well.
-/
theorem observed_prefix_model_conditioning (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (W : List (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
    (g : EuclideanSpace ℝ (Fin n))
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    {N : ℕ} {a η ε γ : ℝ} (hN : 1≤N) (hsize : W.length+1≤N)
    (ha : 0≤a) (hη : 0≤η) (hεη : ε≤η) (hηa : η≤a/2)
    (hγ : 0≤γ) (hγ1 : γ<1) (hangle : (N : ℝ)*a≤(1-γ)/8)
    (hs : ∀ i, primalWindow base (windowSteps W) i≠0)
    (hangles : ∀ i j, i≠j → |inner ℝ (unitWindow (primalWindow base (windowSteps W)) i)
      (unitWindow (primalWindow base (windowSteps W)) j)|≤a)
    (hy : ∀ i, ‖dualWindow base (windowImages W) i-primalWindow base (windowSteps W) i‖≤
      η*‖primalWindow base (windowSteps W) i‖)
    (hd : windowDirection W g≠0)
    (hA : ‖canonicalOperator base A-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤ε) :
    let d := windowDirection W g
    let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
    let S := primalWindow base (windowSteps W)
    let Y := dualWindow base (windowImages W)
    let U : Fin (W.length+1) → EuclideanSpace ℝ (Fin n) := Fin.cons (R d) S
    let Z : Fin (W.length+1) → EuclideanSpace ℝ (Fin n) := Fin.cons (canonicalOperator base A (R d)) Y
    IsUnit (crossGram (windowImages W) (windowSteps W)).det ∧
      spectralGate γ ((d,A d)::W) ∧ ‖windowDefect W‖<1 ∧
      ‖rescaleModel (pairModel U Z) (fun i => ‖U i‖⁻¹)-1‖≤((W.length+1 : ℕ) : ℝ)*(a+η) := by
  let d := windowDirection W g
  let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
  let S := primalWindow base (windowSteps W)
  let Y := dualWindow base (windowImages W)
  let U : Fin (W.length+1) → EuclideanSpace ℝ (Fin n) := Fin.cons (R d) S
  let Z : Fin (W.length+1) → EuclideanSpace ℝ (Fin n) := Fin.cons (canonicalOperator base A (R d)) Y
  have hm := uniform_gate_margins hN hsize hγ hγ1 ha hη hηa hangle
  have hp : (W.length : ℝ)≤((W.length+1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ W.length
  have hG := unitGram_deviation (unitWindow S) (unitWindow_norm S hs) ha hangles
  have hsolveSmall : (W.length : ℝ)*a+(W.length : ℝ)*η≤1/2 := by
    have ha' := mul_le_mul_of_nonneg_right hp ha
    have hη' := mul_le_mul_of_nonneg_right hp hη
    linarith [hm.2.1]
  have hC := normalized_observed_solve_unit S Y hs hη hy hG hsolveSmall
  change IsUnit (crossGram (dualWindow base (windowImages W)) (primalWindow base (windowSteps W))).det at hC
  rw [canonical_crossGram base hb] at hC
  have hRd : R d≠0 := by
    intro hz
    have ht := congrArg (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹) hz
    rw [canonical_primal_dual_cancel base hb,map_zero] at ht
    exact hd ht
  have ho (i : Fin W.length) : inner ℝ (Y i) (R d)=0 :=
    canonical_window_image_conjugacy base hb W g hC i
  have haugG := unit_augmented_observed_gram S Y (R d) hs hRd ha (by linarith : η≤a) hy ho hangles
  have hU (i : Fin (W.length+1)) : U i≠0 := Fin.cases hRd hs i
  have hZ (i : Fin (W.length+1)) : ‖Z i-U i‖≤η*‖U i‖ := by
    refine Fin.cases ?_ (fun j => hy j) i
    have ht := (canonicalOperator base A-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))).le_opNorm (R d)
    change ‖canonicalOperator base A (R d)-R d‖≤η*‖R d‖
    exact ht.trans (mul_le_mul_of_nonneg_right (hA.trans hεη) (norm_nonneg _))
  have hgate := pair_spectralGate_of_gram U Z hU hγ hη (by linarith : η<1) hZ haugG hm.2.2.1
  have hmodel := normalized_pairModel_identity_distance U Z hU hη hZ haugG
  have hUm : primalWindow base (windowSteps ((d,A d)::W))=U := by
    rw [windowSteps_cons]
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  have hZm : dualWindow base (windowImages ((d,A d)::W))=Z := by
    rw [windowImages_cons]
    funext i
    refine Fin.cases ?_ (fun _ => rfl) i
    exact (canonicalOperator_primal base hb A d).symm
  have hpair : pairModel U Z=windowModel ((d,A d)::W) := by
    rw [← hUm,← hZm,canonical_pairModel base hb,pairModel_window]
  have hdefect : (W.length : ℝ)*(4*η)<1 :=
    (mul_le_mul_of_nonneg_right hp (by positivity)).trans_lt hm.2.2.2
  dsimp only
  refine ⟨hC,?_,?_,hmodel.trans_eq (by ring)⟩
  · rw [hpair] at hgate
    exact (matrixSpectralGate_window γ _).mp hgate
  · change ‖pairDefect (windowSteps W) (windowImages W)‖<1
    rw [← canonical_pairDefect base hb]
    exact (relative_pairDefect_norm_bound S Y hs hη hm.1 hy).trans_lt hdefect

end
end krylov.Correction
