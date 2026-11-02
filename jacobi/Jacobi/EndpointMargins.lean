import jacobi.Jacobi.SquaredDistanceBounds
import jacobi.Oscillation.UniformPositivePrefix

/-!
Article: jacobi, Proposition B.1.
Both the true shifted finite endpoint distance and the literal corrected
model have uniform positive quadratic index bounds. The growing tail
uses the actual bounded node-error comparison. Every small index uses
the genuine Mehler--Heine limit and the proved original Bessel inequality B5.
Use: the actual affine interpolation preserves these positive margins, proving the full sine-coordinate comparison in Proposition B.1 (d).
-/
namespace jacobi.Jacobi
noncomputable section
open Real Set Filter jacobi.Bessel jacobi.Oscillation
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The genuine shifted finite endpoint distance and its literal model have one uniform positive quadratic margin on the entire original growing first-half range, including every small index.
Use: the actual affine interpolation preserves these positive margins, proving the full sine-coordinate comparison in Proposition B.1 (d).
Article: jacobi, Proposition B.1.
Proof: the model has a proved quadratic lower bound and the true shifted
distance differs by a proved bounded error. The actual fixed-index limits
are (sigma_k-c_0alpha)/2 and are uniformly positive by true B5 and genuine
Bessel zero monotonicity. The finite-prefix positivity lemma upgrades the
coercive estimate to a uniform positive quadratic lower bound. Upper
bounds follow from the same literal model and bounded comparison. -/
theorem firstHalf_endpoint_margins {a b : ℝ} (ha : -1<a) (hb : -1<b) :
    ∃ d D : ℝ,0<d ∧ 0<D ∧ ∀ᶠ n : ℕ in atTop,0<frequency a b n ∧ ∀ k,2*k<n →
      d*(k+1:ℝ)^2≤correctedSquaredDistance a b ha hb n k ∧
      correctedSquaredDistance a b ha hb n k≤D*(k+1:ℝ)^2 ∧
      d*(k+1:ℝ)^2≤modelSquaredDistance a b n k ∧
      modelSquaredDistance a b n k≤D*(k+1:ℝ)^2 := by
  -- Positivity of the actual shifted distance is derived from the original Bessel limit, rather than inferred from a possibly nonpositive additive-error comparison.
  obtain ⟨B,hB,hdiff⟩ := firstHalf_distance_difference ha hb
  let delta := (sigma a ha 0-endpointCorrection a)/2
  have hdelta : 0<delta := by
    have hh := sigma_above_correction ha 0
    change endpointCorrection a<sigma a ha 0 at hh
    dsimp [delta]
    linarith
  have hv : ∀ k,delta≤(sigma a ha k-endpointCorrection a)/2 := by
    intro k
    have hh := (sigma_strictMono ha).monotone (Nat.zero_le k)
    dsimp [delta]
    linarith
  have hcoerce : ∀ᶠ n : ℕ in atTop,∀ k,2*k<n →
      (1/8:ℝ)*(k+1:ℝ)^2-B≤correctedSquaredDistance a b ha hb n k := by
    filter_upwards [hdiff] with n hn
    intro k hk
    have he := hn.2 k hk
    have hm := (modelSquaredDistance_bounds ha hb (show k<n by omega)).1
    linarith [(abs_le.mp he).1]
  obtain ⟨c,hc,hpositive⟩ := uniform_positive_quadratic (P := fun n k => 2*k<n)
    (show (0:ℝ)<1/8 by norm_num) hdelta (correctedSquaredDistance_tendsto ha hb) hv hcoerce
  let d := min c (1/8:ℝ)
  let L := (Real.pi*(|a|+2))^2/2
  let D := L+B
  have hd : 0<d := lt_min hc (by norm_num)
  have hL : 0≤L := by dsimp [L]; positivity
  have hD : 0<D := by dsimp [D]; linarith
  refine ⟨d,D,hd,hD,?_⟩
  filter_upwards [hdiff,hpositive] with n hn hp
  refine ⟨hn.1,?_⟩
  intro k hk
  have ht : 1≤(k+1:ℝ)^2 := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have he := hn.2 k hk
  have hm := modelSquaredDistance_bounds ha hb (show k<n by omega)
  have hcD : L≤D := by dsimp [D]; linarith
  refine ⟨(mul_le_mul_of_nonneg_right (min_le_left c (1/8:ℝ)) (sq_nonneg _)).trans (hp k hk),?_,
    (mul_le_mul_of_nonneg_right (min_le_right c (1/8:ℝ)) (sq_nonneg _)).trans hm.1,
      hm.2.trans (mul_le_mul_of_nonneg_right hcD (sq_nonneg _))⟩
  have hh := (abs_le.mp he).2
  have hmul := mul_le_mul_of_nonneg_left ht hB.le
  change correctedSquaredDistance a b ha hb n k≤(L+B)*(k+1:ℝ)^2
  have hmodelUpper : modelSquaredDistance a b n k≤L*(k+1:ℝ)^2 := hm.2
  nlinarith

end
end jacobi.Jacobi
