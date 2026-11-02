import krylov.Functions.SelfConcordantPotential
import Mathlib.Topology.Order.IntermediateValue

/-!
Article: main_krylov, apG:sc(ii), genuine sublevel radius.
Use: construct the unique nonnegative inverse-potential radius and enclose
the actual function sublevel; the uniform bound rho(t) <= 2t is proved from
the exact derivative comparison on [0,1/2].
Source: Nesterov18, inequalities (5.1.14), (5.1.16), and the scalar comparison
given in Appendix G of main_krylov.
-/

namespace krylov.Functions
noncomputable section
open Set

/-- The lower potential is continuous on the entire nonnegative half-line.
Article: main_krylov, apG:sc(ii). Proof: its genuine derivative exists there. -/
theorem continuousOn_scOmega : ContinuousOn scOmega (Ici 0) :=
  fun t ht => (scOmega_hasDerivAt (by have ht' : 0 ≤ t := ht; linarith : -1 < t)).continuousAt.continuousWithinAt

/-- The lower potential is strictly increasing on nonnegative radii.
Article: main_krylov, apG:sc(ii). Proof: its derivative is positive away from zero. -/
theorem strictMonoOn_scOmega : StrictMonoOn scOmega (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0) continuousOn_scOmega
  intro t ht
  have ht' : 0 < t := by simpa only [interior_Ici, mem_Ioi] using ht
  rw [(scOmega_hasDerivAt (by linarith : -1 < t)).deriv]
  positivity

/-- The lower potential has an explicit unbounded affine minorant.
Article: main_krylov, apG:sc(ii), existence of the sublevel radius.
Proof: apply log z <= z-1 at z=(1+t)/2 and use log 2 <= 1. -/
theorem scOmega_affine_lower {t : ℝ} (ht : 0 ≤ t) : (t - 1) / 2 ≤ scOmega t := by
  have hp : 0 < (1 + t) / 2 := by positivity
  have h := Real.log_le_sub_one_of_pos hp
  have h₂ := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  rw [Real.log_div (by positivity : (1 : ℝ) + t ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)] at h
  dsimp [scOmega]
  linarith

/-- Each nonnegative value has exactly one nonnegative lower-potential radius.
Article: main_krylov, apG:sc(ii).
Proof: use the explicit affine minorant to bound an interval for the actual
intermediate value theorem; strict monotonicity supplies uniqueness. -/
theorem existsUnique_scOmega_radius (v : ℝ) (hv : 0 ≤ v) :
    ∃! r : ℝ, 0 ≤ r ∧ scOmega r = v := by
  have hR : 0 ≤ 2 * v + 1 := by positivity
  have hbound : v ≤ scOmega (2 * v + 1) := by
    have h := scOmega_affine_lower hR
    linarith
  have hv' : v ∈ Icc (scOmega 0) (scOmega (2 * v + 1)) := by
    simpa [scOmega] using And.intro hv hbound
  obtain ⟨r, hr, he⟩ := intermediate_value_Icc hR
    (continuousOn_scOmega.mono (fun t ht => ht.1)) hv'
  refine ⟨r, ⟨hr.1, he⟩, ?_⟩
  intro s hs
  exact strictMonoOn_scOmega.injOn hs.1 hr.1 (hs.2.trans he.symm)

/-- The upper potential is nonnegative on its admitted radii.
Article: main_krylov, apG:sc(ii). Proof: log(1-t) <= -t. -/
theorem scOmegaStar_nonneg {t : ℝ} (ht : t < 1) : 0 ≤ scOmegaStar t := by
  have h := Real.log_le_sub_one_of_pos (sub_pos.mpr ht)
  dsimp [scOmegaStar]
  linarith

/-- The actual sublevel radius is the unique inverse-potential radius.
Article: main_krylov, apG:sc(ii). -/
def scSublevelRadius (t : ℝ) (ht : t < 1) : ℝ :=
  (existsUnique_scOmega_radius (scOmegaStar t) (scOmegaStar_nonneg ht)).choose

/-- The constructed radius is nonnegative and satisfies the exact defining equation.
Article: main_krylov, apG:sc(ii). Proof: specification of the proved unique inverse. -/
theorem scSublevelRadius_spec (t : ℝ) (ht : t < 1) :
    0 ≤ scSublevelRadius t ht ∧ scOmega (scSublevelRadius t ht) = scOmegaStar t :=
  (existsUnique_scOmega_radius (scOmegaStar t) (scOmegaStar_nonneg ht)).choose_spec.1

/-- The printed two-times-radius potential comparison is exact on [0,1/2].
Article: main_krylov, apG:sc(ii).
Proof: differentiate the actual potential difference; its derivative is
3t(1-2t)/((1+2t)(1-t)), which is nonnegative on that interval. -/
theorem scOmegaStar_le_double {t : ℝ} (ht : 0 ≤ t) (ht₂ : t ≤ 1 / 2) :
    scOmegaStar t ≤ scOmega (2 * t) := by
  let q := fun t : ℝ => scOmega (2 * t) - scOmegaStar t
  let q' := fun t : ℝ => 3 * t * (1 - 2 * t) / ((1 + 2 * t) * (1 - t))
  have hd s (hs : s ∈ Icc (0 : ℝ) (1 / 2)) : HasDerivAt q (q' s) s := by
    have hp : -1 < 2 * s := by linarith [hs.1]
    have hm : s < 1 := by linarith [hs.2]
    convert! ((scOmega_hasDerivAt hp).comp s ((hasDerivAt_id s).const_mul 2)).sub
      (scOmegaStar_hasDerivAt hm) using 1
    all_goals dsimp [q']
    all_goals field_simp [show (1 : ℝ) + 2 * s ≠ 0 by linarith,
      show (1 : ℝ) + s * 2 ≠ 0 by linarith [hs.1], show (1 : ℝ) - s ≠ 0 by linarith]
    all_goals ring
  have hb s (hs : s ∈ Icc (0 : ℝ) (1 / 2)) : 0 ≤ q' s := by
    dsimp [q']
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hs.1) (by linarith [hs.2]))
      (mul_nonneg (by linarith [hs.1]) (by linarith [hs.2]))
  have hm : MonotoneOn q (Icc 0 (1 / 2)) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 (1 / 2))
      (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hd s (interior_subset hs)).hasDerivWithinAt)
      (fun s hs => hb s (interior_subset hs))
  have h := hm (by norm_num : (0 : ℝ) ∈ Icc 0 (1 / 2)) ⟨ht, ht₂⟩ ht
  have hq₀ : q 0 = 0 := by simp [q, scOmega, scOmegaStar]
  dsimp [q] at h
  rw [show scOmega (2 * 0) - scOmegaStar 0 = 0 from hq₀] at h
  linarith

/-- The exact inverse-potential radius satisfies the printed uniform bound.
Article: main_krylov, apG:sc(ii). Proof: apply strict monotonicity to the exact
inverse equation and the proved double-radius potential comparison. -/
theorem scSublevelRadius_le_double {t : ℝ} (ht : 0 ≤ t) (ht₂ : t ≤ 1 / 2) :
    scSublevelRadius t (by linarith) ≤ 2 * t := by
  obtain ⟨hρ, he⟩ := scSublevelRadius_spec t (by linarith : t < 1)
  by_contra! hlt
  have h := strictMonoOn_scOmega (show 2 * t ∈ Ici 0 from mul_nonneg (by norm_num) ht) hρ hlt
  rw [he] at h
  exact (not_lt_of_ge (scOmegaStar_le_double ht ht₂)) h

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The genuine function sublevel lies in the exact inverse-potential ball.
Article: main_krylov, apG:sc(ii), actual-function sublevel enclosure.
Proof: compare the actual potential at both points and invert the strictly
increasing lower potential. Every derivative and comparison was proved from
the original self-concordance data. -/
theorem standardSelfConcordant_sublevel (f : E → ℝ) (U : Set E)
    (D : krylov.Nonlinear.StandardSelfConcordantData f U)
    (h₀ : (0 : E) ∈ U) (hg₀ : gradient f (0 : E) = 0)
    (hH₀ : D.hessian 0 = ContinuousLinearMap.id ℝ E)
    (x : E) (hx : x ∈ U) (hx1 : ‖x‖ < 1) (y : E) (hy : y ∈ U) (hvalue : f y ≤ f x) :
    ‖y‖ ≤ scSublevelRadius ‖x‖ hx1 := by
  have hlo := (standardSelfConcordant_potential f U D h₀ hg₀ hH₀ y hy).1
  have hhi := (standardSelfConcordant_potential f U D h₀ hg₀ hH₀ x hx).2 hx1
  obtain ⟨hρ, he⟩ := scSublevelRadius_spec ‖x‖ hx1
  by_contra! hlt
  have h := strictMonoOn_scOmega hρ (norm_nonneg y) hlt
  rw [he] at h
  linarith

end
end krylov.Functions
