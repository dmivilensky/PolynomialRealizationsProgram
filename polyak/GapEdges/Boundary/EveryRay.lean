import polyak.GapEdges.Boundary.RationalRay
import Mathlib.Data.Rat.Floor

/-! Density is used only to choose one primitive rational frequency
strictly between the two roots.  Negativity then holds for all amplitudes
above one explicit finite bound, rather than for a finite set of rays. -/
noncomputable section
namespace polyak.GapEdges
open General Levels Set

theorem rational_cosine_between {r₁ r₂ : ℝ}
    (hl : -1 < r₁) (hr : r₁ < r₂) (hu : r₂ < 1) :
    ∃ j k : ℕ, 1 ≤ j ∧ 2 * j < k ∧ j.Coprime k ∧
      r₁ < Chart.rationalCosine j k ∧ Chart.rationalCosine j k < r₂ := by
  have hl1 := hr.trans hu
  have hl2 := hl.trans hr
  have harc := Real.strictAntiOn_arccos ⟨hl.le, hl1.le⟩ ⟨hl2.le, hu.le⟩ hr
  obtain ⟨r, hrlo, hrhi⟩ := exists_rat_btwn
    ((div_lt_div_iff_of_pos_right (by positivity : 0 < 2 * Real.pi)).mpr harc)
  have hlo : 0 < (r : ℝ) :=
    (div_pos (Real.arccos_pos.mpr hu) (by positivity)).trans hrlo
  have hhi : (r : ℝ) < 1 / 2 := by
    have hπ := Real.arccos_lt_pi.mpr hl
    have hh := (div_lt_div_iff_of_pos_right (by positivity : 0 < 2 * Real.pi)).mpr hπ
    have he : Real.pi / (2 * Real.pi) = (1 : ℝ) / 2 := by field_simp
    exact hrhi.trans (he ▸ hh)
  have hnum : 0 < r.num := Rat.num_pos.mpr (by exact_mod_cast hlo)
  have hcast : ((r.num.natAbs : ℕ) : ℝ) = (r.num : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg (by exact_mod_cast hnum.le)]
  have hk : 0 < (r.den : ℝ) := by exact_mod_cast r.pos
  have he : (r : ℝ) = (r.num.natAbs : ℝ) / r.den := by
    rw [Rat.cast_def, hcast]
  have hj : 1 ≤ r.num.natAbs := by
    have hh := Int.natAbs_pos.mpr hnum.ne'
    omega
  have hjk : 2 * r.num.natAbs < r.den := by
    rw [he] at hhi
    have hh := (div_lt_iff₀ hk).mp hhi
    exact_mod_cast (show (2 : ℝ) * r.num.natAbs < r.den by linarith)
  let ω := Regions.rationalAngle r.num.natAbs r.den
  have hω : ω ∈ Ioo (0 : ℝ) Real.pi := Regions.rationalAngle_mem hj hjk
  have hωlo : Real.arccos r₂ < ω := by
    have hh := (div_lt_iff₀ (by positivity : 0 < 2 * Real.pi)).mp hrlo
    rw [he] at hh
    dsimp [ω, Regions.rationalAngle]
    convert hh using 1
    ring
  have hωhi : ω < Real.arccos r₁ := by
    have hh := (lt_div_iff₀ (by positivity : 0 < 2 * Real.pi)).mp hrhi
    rw [he] at hh
    dsimp [ω, Regions.rationalAngle]
    convert hh using 1
    ring
  refine ⟨r.num.natAbs, r.den, hj, hjk, r.reduced, ?_, ?_⟩
  · change r₁ < Real.cos ω
    have hh := Real.strictAntiOn_cos ⟨hω.1.le, hω.2.le⟩
      ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩ hωhi
    simpa only [Real.cos_arccos hl.le hl1.le] using hh
  · change Real.cos ω < r₂
    have hh := Real.strictAntiOn_cos ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
      ⟨hω.1.le, hω.2.le⟩ hωlo
    simpa only [Real.cos_arccos hl2.le hu.le] using hh

theorem every_ray_eventually_negative {K : ℕ} (hK : 2 ≤ K)
    {r₁ r₂ : ℝ} (hl : Chart.boundaryCosine K < r₁) (hr : r₁ < r₂)
    (hu : r₂ < Chart.boundaryCosine (K + 1)) :
    ∃ A : ℝ, Chart.amplitudeFloor r₁ r₂ ≤ A ∧
      ∀ a > A, ∀ q : Tuning,
        Chart.coefficients q = Chart.gapPolynomial a r₁ r₂ → q ∈ negativeGap K := by
  obtain ⟨j, k, hj, hjk, hcop, hcl, hcu⟩ := rational_cosine_between
    ((Chart.boundaryCosine_ge_neg_one K).trans_lt hl) hr
    (hu.trans (Chart.boundaryCosine_succ_lt_one hK))
  refine ⟨max (Chart.amplitudeFloor r₁ r₂) (Chart.tongueAmplitude j k r₁ r₂),
    le_max_left _ _, ?_⟩
  intro a ha q he
  exact negative_on_rational_ray hK hj hjk hcop hl hr hu hcl hcu ha q he

theorem negativeGap_nonempty {K : ℕ} (hK : 2 ≤ K) : (negativeGap K).Nonempty := by
  obtain ⟨p, hp⟩ := Chart.rayParameterSet_nonempty hK
  obtain ⟨A, hA, hneg⟩ := every_ray_eventually_negative hK hp.2.1 hp.2.2.1 hp.2.2.2
  let a := A + 1
  have ha : Chart.amplitudeFloor p.2.1 p.2.2 < a := by dsimp [a]; linarith
  let q := Chart.gapInverse hK ⟨(a, p.2.1, p.2.2), hp.2.1, hp.2.2.1, hp.2.2.2, ha⟩
  exact ⟨q.val, hneg a (by dsimp [a]; linarith) q.val (Chart.coefficients_inverseTuning _)⟩

end polyak.GapEdges
