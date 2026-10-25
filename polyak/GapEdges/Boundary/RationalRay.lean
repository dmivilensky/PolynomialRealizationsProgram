import polyak.GapEdges.Boundary.Topology
import polyak.Levels.Chart.TongueNonempty
import polyak.Levels.Geometry.Arccotangent

/-! A strict tongue inequality gives a strictly negative full threshold.
The explicit root chart then proves negativity on every sufficiently
large amplitude of a ray containing the chosen rational frequency. -/
noncomputable section
namespace polyak.GapEdges
open General Levels Set

theorem sigma_le_rational_shift (q : Tuning) {j k : ℕ}
    (hj : 1 ≤ j) (hjk : 2 * j < k) (hcop : j.Coprime k) :
    Threshold.sigma q ≤ Real.cos (Real.pi / k) / Real.sin (Real.pi / k) -
      Geometry.cotangent q (Regions.rationalAngle j k) := by
  let s := Real.cos (Real.pi / k) / Real.sin (Real.pi / k) -
    Geometry.cotangent q (Regions.rationalAngle j k)
  let ω := Chart.rationalFrequency hj hjk
  have hω := Regions.rationalAngle_mem hj hjk
  have hφ : Real.pi / k ∈ Ioo (0 : ℝ) Real.pi := by
    exact ⟨div_pos Real.pi_pos (by exact_mod_cast (show 0 < k by omega)),
      div_lt_self Real.pi_pos (by exact_mod_cast (show 1 < k by omega))⟩
  have he : Geometry.shiftedCurve q s ω = Real.pi / k := by
    apply Geometry.angle_eq_of_cot_eq (Geometry.shiftedAngle_mem q s hω) hφ
    rw [Geometry.cot_shiftedAngle q s hω]
    dsimp [s, Geometry.cotangent]
    ring
  exact (Threshold.shifted_fp_iff q s).mp
    (Lattice.rational_atom_feasible (Geometry.shiftedCurve q s) hcop
      (show 2 ≤ k by omega) ω rfl he.le)

theorem sigma_neg_of_strict_rational_Xi (q : Tuning) {j k : ℕ}
    (hj : 1 ≤ j) (hjk : 2 * j < k) (hcop : j.Coprime k)
    (h : Chart.rationalHeight j k < q.Xi (Chart.rationalCosine j k)) :
    Threshold.sigma q < 0 := by
  have hs := Real.sin_pos_of_pos_of_lt_pi
    (Regions.rationalAngle_mem hj hjk).1 (Regions.rationalAngle_mem hj hjk).2
  have ht : Real.cos (Real.pi / k) / Real.sin (Real.pi / k) <
      Geometry.cotangent q (Regions.rationalAngle j k) := by
    rw [Geometry.cotangent, lt_div_iff₀ hs]
    exact h
  exact (sigma_le_rational_shift q hj hjk hcop).trans_lt (sub_neg.mpr ht)

theorem negative_on_rational_ray {K j k : ℕ} (hK : 2 ≤ K)
    (hj : 1 ≤ j) (hjk : 2 * j < k) (hcop : j.Coprime k)
    {r₁ r₂ a : ℝ} (hr₁ : Chart.boundaryCosine K < r₁)
    (hr : r₁ < r₂) (hr₂ : r₂ < Chart.boundaryCosine (K + 1))
    (hcl : r₁ < Chart.rationalCosine j k) (hcu : Chart.rationalCosine j k < r₂)
    (ha : max (Chart.amplitudeFloor r₁ r₂) (Chart.tongueAmplitude j k r₁ r₂) < a)
    (q : Tuning) (he : Chart.coefficients q = Chart.gapPolynomial a r₁ r₂) :
    q ∈ negativeGap K := by
  have hfloor := (le_max_left _ _).trans_lt ha
  have htongue := (le_max_right _ _).trans_lt ha
  refine ⟨Chart.gap_of_root_coordinates q hK hr₁ hr hr₂ hfloor he, ?_⟩
  apply sigma_neg_of_strict_rational_Xi q (show 1 ≤ j by omega) hjk hcop
  rw [← Chart.eval_coefficients, he, Chart.gapPolynomial_eval]
  have hd : 0 < (Chart.rationalCosine j k - r₁) * (r₂ - Chart.rationalCosine j k) :=
    mul_pos (sub_pos.mpr hcl) (sub_pos.mpr hcu)
  change (Chart.rationalHeight j k - 1 - Chart.rationalCosine j k) /
    ((Chart.rationalCosine j k - r₁) * (r₂ - Chart.rationalCosine j k)) < a at htongue
  have hm := (div_lt_iff₀ hd).mp htongue
  nlinarith [hm]

end polyak.GapEdges
