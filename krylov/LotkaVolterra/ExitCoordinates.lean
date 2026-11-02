import krylov.LotkaVolterra.GlobalExpandingLimit
import krylov.LotkaVolterra.OrbitEstimates

/-!
Article: main_krylov, apC:prop:LV, classification of nonexiting trajectories.
Use: express a true subcritical LV trajectory in the chord slope v. The
physical-time equation has no singular denominator at v=1, which permits
strict escape estimates before changing the independent coordinate.
Source: quotient differentiation and the two saddle equilibrium identities.
-/

namespace krylov.LotkaVolterra
noncomputable section
open Set Filter
open scoped Topology

def chordSlope (γ s U : ℝ) : ℝ := (saddleS γ - s) / (saddleU γ - U)

/-- The open lower phase region corresponds precisely to slopes in (0,1). -/
theorem chordSlope_mem {γ s U : ℝ} (hγ : γ < 1)
    (hs : s < saddleS γ) (hU : U < s + 1) :
    chordSlope γ s U ∈ Ioo (0 : ℝ) 1 := by
  have hB := saddleU_eq_saddleS_add_one (ne_of_lt hγ)
  have hden : 0 < saddleU γ - U := by linarith
  refine ⟨div_pos (sub_pos.mpr hs) hden, ?_⟩
  apply (div_lt_one hden).mpr
  linarith

/-- In physical orbit time the normalized chord slope satisfies a polynomial
equation, even at the exit wall v=1. -/
theorem hasDerivAt_chordSlope {γ t : ℝ} {s U : ℝ → ℝ} (hγ : γ < 1)
    (hden : saddleU γ - U t ≠ 0)
    (hs : HasDerivAt s (2 * s t * (s t - 1 - γ * U t)) t)
    (hU : HasDerivAt U (U t * (s t + 1 - U t)) t) :
    HasDerivAt (fun t ↦ chordSlope γ (s t) (U t))
      (2 * s t * (chordSlope γ (s t) (U t) - γ) +
        chordSlope γ (s t) (U t) * U t * (1 - chordSlope γ (s t) (U t))) t := by
  have hd := (hs.const_sub (saddleS γ)).div (hU.const_sub (saddleU γ)) hden
  convert hd using 1
  · rfl
  · have hA := saddleS_eq_one_add_mul_saddleU (ne_of_lt hγ)
    have hB := saddleU_eq_saddleS_add_one (ne_of_lt hγ)
    unfold chordSlope
    field_simp
    rw [hA] at hB ⊢
    linear_combination (U t * (1 + γ * saddleU γ - s t)) * hB

/-- A globally bounded trajectory in the lower region cannot have slope
strictly above gamma once its U-coordinate is bounded away from one. This
uses a true finite-time growth contradiction, without an omega-limit theorem. -/
theorem nonescaping_chord_le_gamma {γ T δ : ℝ} {s U v : ℝ → ℝ}
    (hδ : 0 < δ)
    (hb : ∀ t ≥ T, 0 < v t ∧ v t < 1 ∧ δ ≤ s t ∧ 0 ≤ U t)
    (hd : ∀ t ≥ T, HasDerivAt v
      (2 * s t * (v t - γ) + v t * U t * (1 - v t)) t) :
    ∀ t ≥ T, v t ≤ γ := by
  intro t ht
  by_contra! hvγ
  let a := (γ + v t) / 2
  have ha : γ < a := by dsimp [a]; linarith
  have hv : a < v t := by dsimp [a]; linarith
  have hrate : 0 < 2 * δ * (a - γ) := by positivity
  have hbound := bounded_solution_le_of_positive_rate hrate hd
    (B := (1 : ℝ)) (fun u hu ↦ (hb u hu).2.1.le)
    (a := a) (fun u hu hva ↦ by
      have hb' := hb u hu
      have hmass : 0 ≤ v u * U u * (1 - v u) :=
        mul_nonneg (mul_nonneg hb'.1.le hb'.2.2.2) (sub_nonneg.mpr hb'.2.1.le)
      have hprod := mul_le_mul hb'.2.2.1 (sub_le_sub_right hva γ)
        (sub_nonneg.mpr ha.le) (by linarith : 0 ≤ s u)
      nlinarith)
  linarith [hbound t ht]

end
end krylov.LotkaVolterra
