import jacobi.Jacobi.InterpolationDistance

/-!
Article: jacobi, Proposition B.1.
The positive shifted endpoint margins and the independent opposite-factor
bound are applied to every point of every original first-half node
segment. The genuine source frequency is then compared with degree.
Use: the exact source reflection in Jacobi.Interpolation supplies the opposite half and completes Proposition B.1 (d).
-/
namespace jacobi.Jacobi
noncomputable section
open Real Set Filter jacobi.Oscillation
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The full source sine comparison holds throughout every actual first-half interpolation segment, including all fixed small indices.
Use: the exact source reflection in Jacobi.Interpolation supplies the opposite half and completes Proposition B.1 (d).
Article: jacobi, Proposition B.1.
Proof: both true and model corrected squared endpoint distances have
proved positive quadratic bounds. Exact affine interpolation preserves
them. The independent opposite-endpoint margin converts their product
to sine squared. Positivity on the physical interval [0,pi] selects the
positive square root. Finally N and n differ by a fixed parameter offset.
The physical interval is implicit in the article's angular coordinate. -/
theorem firstHalf_interpolation {a b : ℝ} (ha : -1<a) (hb : -1<b) :
    ∃ c C : ℝ,0<c ∧ 0<C ∧ ∀ᶠ n : ℕ in atTop,0<n ∧ ∀ k,2*k<n →
      ∀ theta : ℝ,theta ∈ Icc 0 Real.pi →
      modelScale a b n*cos theta+modelShift a b n ∈
        uIcc (modelNode a b n k) (cos (finiteAngleAt a b ha hb n k)) →
      c*(k+1:ℝ)/(n:ℝ)≤sin theta ∧ sin theta≤C*(k+1:ℝ)/(n:ℝ) := by
  -- Small-index positivity is supplied by the actual Bessel limit, and the entire growing range uses the same constants.
  obtain ⟨d,D,hd,hD,hmargins⟩ := firstHalf_endpoint_margins ha hb
  let c := Real.sqrt d/8
  let C := 2*Real.sqrt (2*D)
  have hc : 0<c := by dsimp [c]; positivity
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨c,C,hc,hC,?_⟩
  filter_upwards [hmargins,firstHalf_interpolation_opposite ha hb,
    frequency_degree_comparison a b,eventually_gt_atTop (0:ℕ)] with n hm ho hn hnpos
  refine ⟨hnpos,?_⟩
  intro k hk theta htheta hinterp
  have ht : 0<(k+1:ℝ) := by positivity
  have hnR : (0:ℝ)<n := by exact_mod_cast hnpos
  obtain ⟨hal,hau,hml,hmu⟩ := hm.2 k hk
  have hdistance := interpolationDistance_bounds ha hb hm.1 ho.1.ne' ⟨hal,hau⟩ ⟨hml,hmu⟩ hinterp
  have hcos := ho.2 k hk _ hinterp
  have hcoord : (modelScale a b n*cos theta+modelShift a b n-modelShift a b n)/modelScale a b n=cos theta := by
    field_simp [ho.1.ne']
    ring
  rw [hcoord] at hcos
  change (frequency a b n)^2*(1-(modelScale a b n*cos theta+modelShift a b n-modelShift a b n)/modelScale a b n) ∈ _ at hdistance
  rw [hcoord] at hdistance
  have hsin := sine_of_endpoint_margins hd hD hm.1 ht htheta hcos hdistance.1 hdistance.2
  constructor
  · apply le_trans _ hsin.1
    apply (div_le_div_iff₀ hnR hm.1).mpr
    dsimp [c]
    have hh := mul_le_mul_of_nonneg_left hn.2.2 (show 0≤Real.sqrt d*(k+1:ℝ) by positivity)
    nlinarith
  · apply hsin.2.trans
    apply (div_le_div_iff₀ hm.1 hnR).mpr
    dsimp [C]
    have hh := mul_le_mul_of_nonneg_left hn.2.1 (show 0≤Real.sqrt (2*D)*(k+1:ℝ) by positivity)
    nlinarith

end
end jacobi.Jacobi
