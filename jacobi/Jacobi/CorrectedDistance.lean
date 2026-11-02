import jacobi.Jacobi.NodeError
import jacobi.Bessel.EdgeData

/-!
Article: jacobi, Proposition B.1.
The actual affine-inverse distance has the exact positive fixed-index
limit (sigma_k-c_0alpha)/2. Its explicit model has uniform quadratic
index growth. These are the true source quantities used to prove a
positive interpolation margin, including every small original index.
Use: proves the uniformly positive shifted endpoint margin required by Proposition B.1 (d).
-/
namespace jacobi.Jacobi
noncomputable section
open Real Set Filter jacobi.Bessel
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The true scaled distance of an original finite node from the corrected affine right endpoint.
Use: proves the uniformly positive shifted endpoint margin required by Proposition B.1 (d).
Article: jacobi, Proposition B.1.
-/
def correctedSquaredDistance (a b : ℝ) (ha : -1<a) (hb : -1<b) (n k : ℕ) : ℝ :=
  ((frequency a b n)^2*(1-cos (finiteAngleAt a b ha hb n k))-endpointCorrection a/2)/modelScale a b n

/-- The true squared-distance model at the original finite frequency.
Use: supplies the uniform quadratic comparison for the actual shifted distance.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
-/
def modelSquaredDistance (a b : ℝ) (n k : ℕ) : ℝ :=
  (frequency a b n)^2*(1-cos (modelAngle a b n k))

/-- The literal affine cosine scale tends to one at the actual original Jacobi frequency.
Use: evaluates the true shifted endpoint limits and provides the physical interpolation scale.
Article: jacobi, Proposition B.1.
Proof: the actual frequency tends to infinity, so its inverse square tends to zero; substitute the literal source scale. -/
theorem modelScale_tendsto (a b : ℝ) : Tendsto (modelScale a b) atTop (𝓝 1) := by
  have hi := tendsto_inv_atTop_zero.comp (frequency_tendsto a b)
  have h := (tendsto_const_nhds (x := (1:ℝ))).sub ((hi.pow 2).const_mul ((endpointCorrection a+endpointCorrection b)/4))
  simp only [zero_pow (by norm_num : 2≠0),mul_zero,sub_zero] at h
  convert h using 1
  ext n
  simp only [modelScale,Function.comp_def,div_eq_mul_inv,mul_inv_rev,inv_pow]
  ring

/-- The literal affine cosine shift tends to zero at the original finite frequency.
Use: bounds the transformed actual nodes away from the opposite endpoint during interpolation.
Article: jacobi, Appendix C.3 (top-node polynomials).
Proof: the true inverse frequency tends to zero; multiply its square by the fixed original shift coefficient. -/
theorem modelShift_tendsto (a b : ℝ) : Tendsto (modelShift a b) atTop (𝓝 0) := by
  have hi := tendsto_inv_atTop_zero.comp (frequency_tendsto a b)
  have h := (hi.pow 2).const_mul ((endpointCorrection b-endpointCorrection a)/4)
  simp only [zero_pow (by norm_num : 2≠0),mul_zero] at h
  convert h using 1
  ext n
  simp only [modelShift,Function.comp_def,div_eq_mul_inv,mul_inv_rev,inv_pow]
  ring

/-- The true finite frequency divided by its degree tends to one.
Use: transfers the original Mehler--Heine squared-zero limit from n^2 to the exact source scale N^2.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: away from the single degree zero, the actual ratio is one plus the fixed parameter offset times 1/n. -/
theorem frequency_ratio_tendsto (a b : ℝ) :
    Tendsto (fun n : ℕ => frequency a b n/(n:ℝ)) atTop (𝓝 1) := by
  have h := (tendsto_one_div_atTop_nhds_zero_nat.const_mul ((a+b+1)/2)).const_add 1
  simp only [mul_zero,add_zero] at h
  apply (tendsto_congr' ?_).mpr h
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  dsimp [frequency]
  field_simp [hn0]

/-- Every actual scaled finite cosine distance has the genuine Bessel squared-zero limit at the exact source frequency.
Use: computes the true corrected endpoint margin for each original small index.
Article: jacobi, Proposition B.1.
Proof: the original finite squared zero is exactly 2*n^2*(1-zeta).
Multiply its proved genuine indexed limit by the squared actual ratio N/n. -/
theorem cosine_distance_tendsto {a b : ℝ} (ha : -1<a) (hb : -1<b) (k : ℕ) :
    Tendsto (fun n : ℕ => (frequency a b n)^2*(1-cos (finiteAngleAt a b ha hb n k)))
      atTop (𝓝 (sigma a ha k/2)) := by
  -- The true indexed original zero limit is used before any shifted endpoint positivity is claimed.
  have h := (((frequency_ratio_tendsto a b).pow 2).mul (finiteSigmaAt_tendsto ha hb k)).div_const 2
  simp only [one_pow,one_mul] at h
  apply (tendsto_congr' ?_).mpr h
  filter_upwards [eventually_gt_atTop k] with n hn
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast (show n≠0 by omega)
  rw [finiteAngleAt_eq ha hb hn,(angle_properties ha hb ⟨k,hn⟩).2,
    finiteSigmaAt_eq ha hb hn,finiteSigma_node ha hb ⟨k,hn⟩]
  field_simp [hn0]

/-- The original shifted actual endpoint distance has its genuine strictly positive Bessel-correction limit at every fixed original index.
Use: discharges the finitely many small-index positivity cases in the full uniform interpolation theorem.
Article: jacobi, Proposition B.1.
Proof: subtract the literal source correction from the actual scaled
Mehler--Heine cosine distance and divide by the actual scale tending to
one. Positivity of its limit is proved separately by original B5. -/
theorem correctedSquaredDistance_tendsto {a b : ℝ} (ha : -1<a) (hb : -1<b) (k : ℕ) :
    Tendsto (fun n => correctedSquaredDistance a b ha hb n k) atTop
      (𝓝 ((sigma a ha k-endpointCorrection a)/2)) := by
  have h := ((cosine_distance_tendsto ha hb k).sub_const (endpointCorrection a/2)).div
    (modelScale_tendsto a b) (by norm_num : (1:ℝ)≠0)
  rw [show (sigma a ha k-endpointCorrection a)/2=(sigma a ha k/2-endpointCorrection a/2)/(1:ℝ) by ring]
  exact h

end
end jacobi.Jacobi
