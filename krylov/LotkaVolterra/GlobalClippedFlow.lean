import krylov.LotkaVolterra.GlobalBoundedODE
import krylov.LotkaVolterra.Saddle
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.Compact

/-!
Bounded continuation for the concrete Lotka--Volterra field on a compact
positive rectangle. Coordinate projection agrees with the polynomial field
on that rectangle and gives a bounded globally Lipschitz extension. The
auxiliary flow is used only to construct actual stopped finite-time orbits.

Source: compactness of the derivative, the convex mean-value theorem, and
Picard--Lindelöf. Neither completeness of the original quadratic field nor
an assumed maximal trajectory is used.
-/
namespace krylov.LotkaVolterra
noncomputable section
open Set
open scoped NNReal

def stateClip (R : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (max 0 (min z.1 R), max 0 (min z.2 R))

theorem stateClip_mem {R : ℝ} (hR : 0 ≤ R) (z : ℝ × ℝ) :
    stateClip R z ∈ Icc (0 : ℝ) R ×ˢ Icc (0 : ℝ) R := by
  exact ⟨⟨le_max_left _ _, max_le hR (min_le_right _ _)⟩,
    ⟨le_max_left _ _, max_le hR (min_le_right _ _)⟩⟩

theorem stateClip_eq {R : ℝ} {z : ℝ × ℝ}
    (hz : z ∈ Icc (0 : ℝ) R ×ˢ Icc (0 : ℝ) R) : stateClip R z = z := by
  apply Prod.ext <;> simp [stateClip, min_eq_left hz.1.2, max_eq_right hz.1.1,
    min_eq_left hz.2.2, max_eq_right hz.2.1]

theorem stateClip_lipschitz (R : ℝ) : LipschitzWith 1 (stateClip R) := by
  have hf : LipschitzWith 1 (fun z : ℝ × ℝ ↦ z.1) :=
    LipschitzWith.prod_fst
  have hg : LipschitzWith 1 (fun z : ℝ × ℝ ↦ z.2) :=
    LipschitzWith.prod_snd
  convert ((hf.min_const R).const_max 0).prodMk ((hg.min_const R).const_max 0) using 1
  · simp
  · rfl

def clippedVectorField (γ R : ℝ) (z : ℝ × ℝ) : ℝ × ℝ := vectorField γ (stateClip R z)

theorem clippedVectorField_eq {γ R : ℝ} {z : ℝ × ℝ}
    (hz : z ∈ Icc (0 : ℝ) R ×ˢ Icc (0 : ℝ) R) :
    clippedVectorField γ R z = vectorField γ z := by
  rw [clippedVectorField, stateClip_eq hz]

theorem clippedVectorField_bounds (γ : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ L K : ℝ≥0, (∀ z, ‖clippedVectorField γ R z‖ ≤ L) ∧
      LipschitzWith K (clippedVectorField γ R) := by
  let C : Set (ℝ × ℝ) := Icc 0 R ×ˢ Icc 0 R
  have hC : IsCompact C := isCompact_Icc.prod isCompact_Icc
  have hJ : Continuous (jacobian γ) := by
    convert (contDiff_vectorField γ 1).continuous_fderiv (by norm_num) using 1
    funext z
    exact (hasFDerivAt_vectorField γ z).fderiv.symm
  obtain ⟨L, hL⟩ := hC.bddAbove_image ((contDiff_vectorField γ 1).continuous.norm.continuousOn)
  obtain ⟨K, hK⟩ := hC.bddAbove_image hJ.norm.continuousOn
  have hLip : LipschitzOnWith (Real.toNNReal K) (vectorField γ) C := by
    apply Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
      (fun z _ ↦ (hasFDerivAt_vectorField γ z).hasFDerivWithinAt) ?_
      ((convex_Icc (0 : ℝ) R).prod (convex_Icc (0 : ℝ) R))
    intro z hz
    have hh : ‖jacobian γ z‖ ≤ (Real.toNNReal K : ℝ) :=
      (hK ⟨z, hz, rfl⟩).trans (Real.le_coe_toNNReal _)
    exact_mod_cast hh
  refine ⟨Real.toNNReal L, Real.toNNReal K, fun z ↦ ?_, ?_⟩
  · exact (hL ⟨stateClip R z, stateClip_mem hR z, rfl⟩).trans (Real.le_coe_toNNReal _)
  · apply LipschitzWith.of_dist_le_mul
    intro z w
    calc
      dist (clippedVectorField γ R z) (clippedVectorField γ R w) ≤
          (Real.toNNReal K : ℝ) * dist (stateClip R z) (stateClip R w) :=
        hLip.dist_le_mul _ (stateClip_mem hR z) _ (stateClip_mem hR w)
      _ ≤ (Real.toNNReal K : ℝ) * dist z w := by
        gcongr
        simpa using (stateClip_lipschitz R).dist_le_mul z w

theorem exists_global_clipped_solution (γ : ℝ) {R : ℝ} (hR : 0 ≤ R)
    (z₀ : ℝ × ℝ) :
    ∃ α : ℝ → ℝ × ℝ, α 0 = z₀ ∧
      ∀ t, HasDerivAt α (clippedVectorField γ R (α t)) t := by
  obtain ⟨L, K, hL, hK⟩ := clippedVectorField_bounds γ hR
  exact exists_global_solution_of_bounded_lipschitz (L := L) (K := K)
    (fun _ ↦ hK) (fun _ ↦ continuous_const) (fun _ z ↦ hL z) z₀

/-- Each clipped coordinate still vanishes on its own axis. Its speed is
therefore bounded by the global Lipschitz constant times that coordinate. -/
theorem clippedVectorField_coordinate_bound {γ R : ℝ} (hR : 0 ≤ R) {K : ℝ≥0}
    (hK : LipschitzWith K (clippedVectorField γ R)) (z : ℝ × ℝ) :
    ‖(clippedVectorField γ R z).1‖ ≤ K * ‖z.1‖ ∧
      ‖(clippedVectorField γ R z).2‖ ≤ K * ‖z.2‖ := by
  have hf : (clippedVectorField γ R (0, z.2)).1 = 0 := by
    simp [clippedVectorField, stateClip, min_eq_left hR, vectorField, sRate]
  have hg : (clippedVectorField γ R (z.1, 0)).2 = 0 := by
    simp [clippedVectorField, stateClip, min_eq_left hR, vectorField, uRate]
  constructor
  · have hp := LipschitzWith.prod_fst.dist_le_mul (clippedVectorField γ R z)
      (clippedVectorField γ R (0, z.2))
    simp only [NNReal.coe_one, one_mul] at hp
    have h := hp.trans (hK.dist_le_mul z (0, z.2))
    simpa [hf, Prod.dist_eq, Real.dist_eq] using h
  · have hp := LipschitzWith.prod_snd.dist_le_mul (clippedVectorField γ R z)
      (clippedVectorField γ R (z.1, 0))
    simp only [NNReal.coe_one, one_mul] at hp
    have h := hp.trans (hK.dist_le_mul z (z.1, 0))
    simpa [hg, Prod.dist_eq, Real.dist_eq] using h

/-- A multiplicative derivative bound prevents a positive scalar coordinate
from reaching its invariant axis at finite time. -/
theorem positive_of_derivative_norm_le {x x' : ℝ → ℝ} {K : ℝ}
    (hd : ∀ t, HasDerivAt x (x' t) t) (hb : ∀ t, ‖x' t‖ ≤ K * ‖x t‖)
    (hx₀ : 0 < x 0) : ∀ t ≥ 0, 0 < x t := by
  have hC : Continuous x := continuous_iff_continuousAt.mpr fun t ↦ (hd t).continuousAt
  have hn (t : ℝ) (ht : 0 ≤ t) : x t ≠ 0 := by
    intro he
    have hdz (u : ℝ) : HasDerivAt (fun u ↦ x (t - u)) (-(x' (t - u))) u := by
      convert (hd (t - u)).comp u ((hasDerivAt_id u).const_sub t) using 1
      · rfl
      · ring
    have hz := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
      (f := fun u ↦ x (t - u)) (f' := fun u ↦ -(x' (t - u))) (a := 0) (b := t)
      (hC.comp (continuous_const.sub continuous_id)).continuousOn
      (fun u _ ↦ (hdz u).hasDerivWithinAt) (by simpa using he)
      (fun u _ ↦ by simpa only [norm_neg] using hb (t - u)) t ⟨ht, le_rfl⟩
    have hz₀ : x 0 = 0 := by simpa using hz
    linarith
  intro t ht
  by_contra! hnpos
  obtain ⟨u, hu, hu₀⟩ := intermediate_value_Icc' ht hC.continuousOn
    (show (0 : ℝ) ∈ Icc (x t) (x 0) from ⟨hnpos, hx₀.le⟩)
  exact hn u hu.1 hu₀

/-- Positive initial data stay positive under the auxiliary complete flow. -/
theorem clipped_solution_positive {γ R : ℝ} (hR : 0 ≤ R) {α : ℝ → ℝ × ℝ}
    (hα : ∀ t, HasDerivAt α (clippedVectorField γ R (α t)) t)
    (hpos : α 0 ∈ positiveQuadrant) : ∀ t ≥ 0, α t ∈ positiveQuadrant := by
  obtain ⟨_, K, _, hK⟩ := clippedVectorField_bounds γ hR
  have hs := positive_of_derivative_norm_le
    (fun t ↦ (hasFDerivAt_fst (𝕜 := ℝ) (p := α t)).comp_hasDerivAt t (hα t))
    (fun t ↦ (clippedVectorField_coordinate_bound hR hK (α t)).1) hpos.1
  have hU := positive_of_derivative_norm_le
    (fun t ↦ (hasFDerivAt_snd (𝕜 := ℝ) (p := α t)).comp_hasDerivAt t (hα t))
    (fun t ↦ (clippedVectorField_coordinate_bound hR hK (α t)).2) hpos.2
  exact fun t ht ↦ ⟨hs t ht, hU t ht⟩

end
end krylov.LotkaVolterra
