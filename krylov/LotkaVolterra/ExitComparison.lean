import krylov.LotkaVolterra.ExitCoordinates
import krylov.LotkaVolterra.ExitExpansion
import krylov.LotkaVolterra.GlobalFullSaddleGraphs

/-!
Article: main_krylov, apC:prop:LV, nonexit classification.
Use: compare the actual physical-time chord with a stable graph, using uniform
expansion of their squared difference. This avoids a general omega-limit theory.
Source: the scalar expansion theorem and the exact chord equations.
-/

namespace krylov.LotkaVolterra
noncomputable section
open Set

theorem physical_chord_rate_eq {γ s U : ℝ} (hU : U ≠ 0)
    (hz : saddleU γ - U ≠ 0) (hv : 1 - chordSlope γ s U ≠ 0) :
    2 * s * (chordSlope γ s U - γ) +
      chordSlope γ s U * U * (1 - chordSlope γ s U) =
        -U * (1 - chordSlope γ s U) *
          saddleSlopeRate γ (saddleU γ - U) (chordSlope γ s U) := by
  have hrep : saddleS γ - chordSlope γ s U * (saddleU γ - U) = s := by
    unfold chordSlope
    rw [div_mul_cancel₀ _ hz]
    ring
  unfold saddleSlopeRate
  rw [hrep, show saddleU γ - (saddleU γ - U) = U by ring]
  field_simp
  ring

/-- A true graph solution has the required chord derivative in U. -/
theorem hasDerivAt_graph_chord {γ U : ℝ} {σ : ℝ → ℝ} (hγ : γ < 1)
    (hU : U ≠ 0) (hz : saddleU γ - U ≠ 0)
    (hv : 1 - chordSlope γ (σ U) U ≠ 0)
    (hσ : HasDerivAt σ (2 * σ U * (σ U - 1 - γ * U) /
      (U * (σ U + 1 - U))) U) :
    HasDerivAt (fun U ↦ chordSlope γ (σ U) U)
      (-saddleSlopeRate γ (saddleU γ - U) (chordSlope γ (σ U) U) /
        (saddleU γ - U)) U := by
  let v := chordSlope γ (σ U) U
  have hrep : saddleS γ - v * (saddleU γ - U) = σ U := by
    dsimp [v, chordSlope]
    rw [div_mul_cancel₀ _ hz]
    ring
  have hrate := graphRate_from_chord (ne_of_lt hγ) hU hz hv
  rw [hrep] at hrate
  rw [← hrate] at hσ
  have hd := (hσ.const_sub (saddleS γ)).div
    ((hasDerivAt_id U).const_sub (saddleU γ)) hz
  convert hd using 1
  · rfl
  · change -saddleSlopeRate γ (saddleU γ - U) v / (saddleU γ - U) =
      (-(v + saddleSlopeRate γ (saddleU γ - U) v) * (saddleU γ - U) -
        (saddleS γ - σ U) * (-1)) / (saddleU γ - U) ^ 2
    have hvrep : saddleS γ - σ U = v * (saddleU γ - U) := by linarith [hrep]
    rw [hvrep]
    field_simp
    ring

/-- Two bounded physical-time chord curves sharing the actual U and distance
coordinate coincide. The lower bound on U and gamma<1 force uniform expansion. -/
theorem bounded_physical_chords_unique {γ u₀ : ℝ} {U z v w : ℝ → ℝ}
    (hγ : γ < 1) (hu₀ : 0 < u₀)
    (hU : ∀ t ≥ 0, u₀ ≤ U t)
    (hz : ∀ t ≥ 0, z t ∈ Icc (0 : ℝ) (saddleS γ))
    (hv : ∀ t ≥ 0, v t ∈ Icc 0 γ ∧ HasDerivAt v
      (-U t * (1 - v t) * saddleSlopeRate γ (z t) (v t)) t)
    (hw : ∀ t ≥ 0, w t ∈ Icc 0 γ ∧ HasDerivAt w
      (-U t * (1 - v t) * saddleSlopeRate γ (z t) (w t)) t) :
    EqOn v w (Ici 0) := by
  let F : ℝ → ℝ → ℝ := fun t x ↦ -U t * (1 - v t) * saddleSlopeRate γ (z t) x
  apply bounded_expanding_solution_unique (F := F)
    (mul_pos hu₀ (sub_pos.mpr hγ)) _ hv hw
  intro t ht x hx y hy
  have hcoef : u₀ * (1 - γ) ≤ U t * (1 - v t) :=
    mul_le_mul (hU t ht) (sub_le_sub_left (hv t ht).1.2 1)
      (sub_nonneg.mpr hγ.le) (hu₀.le.trans (hU t ht))
  have hcoef₀ : 0 ≤ U t * (1 - v t) :=
    mul_nonneg (hu₀.le.trans (hU t ht)) (by linarith [(hv t ht).1.2])
  have he := saddleSlopeRate_lower_expansion hγ (hz t ht) hx hy
  have hh := mul_le_mul_of_nonneg_left he hcoef₀
  have hc := mul_le_mul_of_nonneg_right hcoef (sq_nonneg (x - y))
  dsimp [F]
  nlinarith

end
end krylov.LotkaVolterra
