import krylov.XR.QuadraticReference
import krylov.XR.MemoryGeometry
import krylov.XR.QuadraticExecution

/-!
Article: main_krylov, thm:XR, actual observed Krylov extension.
Use: derive retention and the exact virtual CG state from faithful observed
data, then prove that each genuine nonzero stored trial adds one direction.
The same proof covers rejected probes at the unchanged anchor and accepted
steps; no acceptance decision enters the algebra. Source: Galerkin
uniqueness, positive quadratic secants and nonzero-trial flag extension.
-/

namespace krylov.XR
noncomputable section
open Matrix Set krylov.Methods krylov.Reference krylov.Secant
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A capacity that already contains an independent faithful quadratic
window incurs neither rank cleanup nor an actual Hermitian-test deletion. -/
theorem quadratic_model_retains {n : ℕ} (P : Parameters)
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v, v ≠ 0 → 0 < inner ℝ v (Q v)) (g₀ : EuclideanSpace ℝ (Fin n))
    (constant : ℝ) (S : State (EuclideanSpace ℝ (Fin n)))
    (hfaithful : ∀ a ∈ S.pairs,
      PairFaithful (quadraticObjective Q g₀ constant) (quadraticGradient Q g₀) S.point a)
    (hs : LinearIndependent ℝ (storedSteps S.pairs))
    (hcap : S.pairs.length ≤ min S.capacity n) :
    (algorithmModel P S).pairs = S.pairs ∧
      (algorithmModel P S).pairsBeforeTest = S.pairs.length ∧
      (algorithmModel P S).deletedByTest = 0 := by
  have hretain : retainNewest (min S.capacity n) S.pairs = S.pairs := by
    simp only [retainNewest, Nat.sub_eq_zero_of_le hcap, List.drop_zero]
  have hrank : rankWindow n S = S.pairs := by
    simp only [rankWindow, hretain, rankDeletion_eq_zero S.pairs hs, List.drop_zero]
  have hdelete := quadratic_modelDeletion_zero P Q hQ hpos g₀ constant S.point S.pairs hfaithful hs
  simp only [algorithmModel, hrank, hdelete, List.drop_zero, and_self]

/-- Faithful actual quadratic observations give the exact virtual CG
point, extrapolated gradient and new direction on their real observed flag. -/
theorem quadratic_observed_reference (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v, v ≠ 0 → 0 < inner ℝ v (Q v))
    (g₀ : E) (constant : ℝ) (S : State E) (k : ℕ)
    (hg : ∀ i < k, CG.gradient Q g₀ i ≠ 0)
    (hcache : S.gradient = quadraticGradient Q g₀ S.point)
    (hfaithful : ∀ a ∈ S.pairs,
      PairFaithful (quadraticObjective Q g₀ constant) (quadraticGradient Q g₀) S.point a)
    (hs : LinearIndependent ℝ (storedSteps S.pairs))
    (hspan : Submodule.span ℝ (range (storedSteps S.pairs)) = directionFlag Q g₀ k)
    (hx : S.point ∈ Submodule.span ℝ (range (storedSteps S.pairs))) :
    S.point + modelVirtualCorrection (storedSteps S.pairs) (storedModel S.pairs) S.gradient =
        CG.displacement Q g₀ k ∧
      modelVirtualGradient (storedSteps S.pairs) (storedImages S.pairs)
        (storedModel S.pairs) S.gradient = CG.gradient Q g₀ k ∧
      modelDirection (storedSteps S.pairs) (storedImages S.pairs)
        (storedModel S.pairs) S.gradient = CG.direction Q g₀ k := by
  have hy : storedImages S.pairs = fun i => Q (storedSteps S.pairs i) := by
    ext i
    exact faithful_quadratic_image Q g₀ constant S.point _ (hfaithful _ (List.get_mem _ i))
  have hv := quadratic_virtual_reference Q hQ hpos g₀ k hg (storedSteps S.pairs) hs hspan S.point hx
  simpa only [storedModel, storedPairing, hy, hcache, quadraticGradient] using hv

/-- A nonzero outer trial in the genuine new CG direction cannot lie in
the old observed flag, even if its model step contains a virtual correction. -/
theorem quadratic_observed_step_new (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v, v ≠ 0 → 0 < inner ℝ v (Q v))
    (g₀ : E) (k : ℕ) (hg : ∀ i < k, CG.gradient Q g₀ i ≠ 0)
    (hgk : CG.gradient Q g₀ k ≠ 0) (x : E) (hx : x ∈ directionFlag Q g₀ k)
    (trial length : ℝ) (htrial : trial ≠ 0) (hlength : length ≠ 0) :
    length • ((CG.displacement Q g₀ k - x) + trial • CG.direction Q g₀ k) ∉
      directionFlag Q g₀ k := by
  intro hs
  have hu := (directionFlag Q g₀ k).sub_mem (displacement_mem_directionFlag Q g₀ k) hx
  have hin := (directionFlag Q g₀ k).smul_mem length⁻¹ hs
  rw [smul_smul, inv_mul_cancel₀ hlength, one_smul] at hin
  have hd := (directionFlag Q g₀ k).smul_mem trial⁻¹
    ((directionFlag Q g₀ k).sub_mem hin hu)
  rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ htrial, one_smul] at hd
  exact quadratic_new_direction_not_mem Q hQ hpos g₀ k hg hgk hd

/-- The exact physical span after a genuine observed trial is the next
CG flag. Outer shortening and the virtual correction do not alter it. -/
theorem quadratic_observed_step_flag (Q : E →L[ℝ] E) (g₀ : E) (k : ℕ)
    (x : E) (hx : x ∈ directionFlag Q g₀ k) (trial length : ℝ)
    (htrial : trial ≠ 0) (hlength : length ≠ 0) :
    (ℝ ∙ (length • ((CG.displacement Q g₀ k - x) + trial • CG.direction Q g₀ k))) ⊔
      directionFlag Q g₀ k = directionFlag Q g₀ (k + 1) := by
  have hu := (directionFlag Q g₀ k).sub_mem (displacement_mem_directionFlag Q g₀ k) hx
  have hz : (0 : E) ∈ directionFlag Q g₀ k := Submodule.zero_mem _
  rw [← zero_add (length • _), trial_span_extension _ 0 _ hz length hlength,
    trial_span_extension _ _ _ hu trial htrial, ← directionFlag_succ]

/-- Every genuine nonzero quadratic trial is actually stored: positive
curvature is derived from the true SPD operator and actual secant. -/
theorem appendPositive_quadratic (Q : E →L[ℝ] E)
    (hpos : ∀ v, v ≠ 0 → 0 < inner ℝ v (Q v)) (g₀ : E)
    (f : E → ℝ) (S : State E) (hcache : S.gradient = quadraticGradient Q g₀ S.point)
    (W : List (PairObservation E)) (s : E) (hs : s ≠ 0) :
    appendPositive W (observedTrialPair f (quadraticGradient Q g₀) S s) =
      W ++ [observedTrialPair f (quadraticGradient Q g₀) S s] := by
  classical
  have hi : (observedTrialPair f (quadraticGradient Q g₀) S s).image = Q s := by
    simp [observedTrialPair, hcache, quadraticGradient, map_add]
  unfold appendPositive
  rw [ite_eq_left (show positivePair (observedTrialPair f (quadraticGradient Q g₀) S s) from by
    change 0 < inner ℝ s (observedTrialPair f (quadraticGradient Q g₀) S s).image
    rw [hi]
    exact hpos s hs)]

end
end krylov.XR
