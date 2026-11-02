import jacobi.Jacobi.CorrectedDistance
import jacobi.Jacobi.ModelGap

/-!
Article: jacobi, Proposition B.1.
The literal model squared distance grows quadratically in the original
one-based index. The genuine corrected finite distance differs from it
by a uniformly bounded amount, as a consequence of the proved full
corrected-node error. Positive fixed-index limits then remove every
possible small-index loss of positivity.
Use: supplies the coercive and upper comparisons for the true corrected endpoint distance in Proposition B.1 (d).
-/
namespace jacobi.Jacobi
noncomputable section
open Real Set Filter jacobi.Bessel
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Every actual explicit model squared endpoint distance has uniform positive quadratic index bounds at the exact original frequency.
Use: supplies the coercive and upper comparisons for the true corrected endpoint distance in Proposition B.1 (d).
Article: jacobi, Proposition B.1.
Proof: the true model angle lies in (0,pi). Apply the community global
quadratic cosine bounds and the proved exact leading phase lower and
upper bounds, cancelling the actual nonzero frequency scale. -/
theorem modelSquaredDistance_bounds {a b : ℝ} (ha : -1<a) (hb : -1<b) {n k : ℕ} (hk : k<n) :
    (1/8:ℝ)*(k+1:ℝ)^2≤modelSquaredDistance a b n k ∧
      modelSquaredDistance a b n k≤((Real.pi*(|a|+2))^2/2)*(k+1:ℝ)^2 := by
  -- These are true model endpoint bounds for every original finite index, not asymptotic hypotheses about a chosen comparison grid.
  let N := frequency a b n
  let x := modelAngle a b n k
  let v := phaseGrid a k
  have hN : 0<N := frequency_pos ha hb (by omega)
  have hx := (modelAngle_endpoint_bounds ha hb hk).1
  have hv : 0<v := phaseGrid_pos ha k
  have hscale : N^2*x^2=v^2 := by
    dsimp [x,modelAngle,N,v]
    have hfreqne : frequency a b n≠0 := hN.ne'
    field_simp [hfreqne]
  have hl := Real.cos_le_one_sub_mul_cos_sq (x := x) (by rw [abs_of_pos hx.1]; exact hx.2.le)
  have hu := Real.one_sub_sq_div_two_le_cos (x := x)
  have hvlo := phaseGrid_lower ha k
  have hvhi := phaseGrid_upper a k
  have hvlo2 := (sq_le_sq₀ (by positivity : 0≤(Real.pi/4)*(k+1:ℝ)) hv.le).mpr hvlo
  have hvhi2 := (sq_le_sq₀ hv.le (by positivity : 0≤(Real.pi*(|a|+2))*(k+1:ℝ))).mpr hvhi
  constructor
  · calc
      _ = (2/Real.pi^2)*(((Real.pi/4)*(k+1:ℝ))^2) := by field_simp; ring
      _ ≤ (2/Real.pi^2)*v^2 := mul_le_mul_of_nonneg_left hvlo2 (by positivity)
      _ = (2/Real.pi^2)*(N^2*x^2) := by rw [hscale]
      _ ≤ N^2*(1-cos x) := by nlinarith [mul_le_mul_of_nonneg_left (show (2/Real.pi^2)*x^2≤1-cos x by linarith) (sq_nonneg N)]
  · calc
      _ ≤ N^2*(x^2/2) := mul_le_mul_of_nonneg_left (show 1-cos x≤x^2/2 by linarith) (sq_nonneg N)
      _ = v^2/2 := by rw [show N^2*(x^2/2)=(N^2*x^2)/2 by ring,hscale]
      _ ≤ ((Real.pi*(|a|+2))*(k+1:ℝ))^2/2 := div_le_div_of_nonneg_right hvhi2 (by norm_num)
      _ = _ := by ring

/-- The true corrected endpoint distance and its literal model differ by exactly the original node error times the true affine inverse scale.
Use: transfers the fully proved corrected-node error into a bounded additive squared-distance error.
Article: jacobi, Proposition B.1.
Proof: the original affine scale and shift satisfy N^2*(c_n+d_n-1)=-c_0alpha/2. Substitute this exact coefficient identity and clear the actual nonzero affine scale. -/
theorem correctedSquaredDistance_difference {a b : ℝ} (ha : -1<a) (hb : -1<b) {n : ℕ}
    (hN : 0<frequency a b n) (hscale : modelScale a b n≠0) (k : ℕ) :
    correctedSquaredDistance a b ha hb n k-modelSquaredDistance a b n k=
      -(frequency a b n)^2*(cos (finiteAngleAt a b ha hb n k)-modelNode a b n k)/modelScale a b n := by
  -- The identity retains the original affine endpoint shift, whose positive small-index limit is essential to the interpolation theorem.
  have he : (frequency a b n)^2*(modelScale a b n+modelShift a b n-1)= -endpointCorrection a/2 := by
    dsimp [modelScale,modelShift]
    field_simp [hN.ne']
    ring
  unfold correctedSquaredDistance modelSquaredDistance modelNode
  field_simp [hscale]
  nlinarith [he]

/-- The true corrected endpoint distance differs from the explicit original quadratic model by one uniform bounded amount on the complete growing first-half range.
Use: the positive fixed-index limit upgrades this bounded error into the full positive interpolation margin in Proposition B.1 (d).
Article: jacobi, Proposition B.1.
Proof: the true affine scale is at least one half. Multiply the proved
original node error by N^2; its two terms become k^(-2) and k/N^2,
whose sum is at most three on the original first-half range at large
degree. The exact affine distance identity gives the stated bound. -/
theorem firstHalf_distance_difference {a b : ℝ} (ha : -1<a) (hb : -1<b) :
    ∃ B : ℝ,0<B ∧ ∀ᶠ n : ℕ in atTop,0<frequency a b n ∧ ∀ k,2*k<n →
      |correctedSquaredDistance a b ha hb n k-modelSquaredDistance a b n k|≤B := by
  -- The genuine source node error, rather than a separate numerical margin, supplies the only growing-index comparison input.
  obtain ⟨C,hC,herror⟩ := firstHalf_node_error ha hb
  refine ⟨6*C,by positivity,?_⟩
  filter_upwards [herror,modelScale_half a b,frequency_degree_comparison a b,
    (frequency_tendsto a b).eventually (eventually_ge_atTop 1)] with n hn hscale hdegree hlarge
  have hN := hn.1
  have hsc : 0<modelScale a b n := by linarith
  refine ⟨hN,?_⟩
  intro k hk
  let N := frequency a b n
  let t : ℝ := k+1
  have ht : 1≤t := by dsimp [t]; linarith [Nat.cast_nonneg (α := ℝ) k]
  have htp : 0<t := by linarith
  have htN : t≤2*N := by
    have hh : (k+1:ℝ)≤n := by exact_mod_cast (show k+1≤n by omega)
    exact hh.trans hdegree.2.1
  have hi1 : 1/t^2≤1 := div_le_self (by norm_num) (by nlinarith)
  have hi2 : t/N^2≤2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hN)).mpr
    have hN1 : 1≤N := hlarge
    nlinarith
  have he := mul_le_mul_of_nonneg_left (hn.2 k hk) (sq_nonneg N)
  have hN0 : N≠0 := hN.ne'
  have hid : N^2*(C*(1/(N^2*t^2)+t/N^4))=C*(1/t^2+t/N^2) := by field_simp [hN0,htp.ne']
  change N^2*|cos (finiteAngleAt a b ha hb n k)-modelNode a b n k|≤N^2*(C*(1/(N^2*t^2)+t/N^4)) at he
  rw [hid] at he
  have hbounded : N^2*|cos (finiteAngleAt a b ha hb n k)-modelNode a b n k|≤3*C := by nlinarith
  rw [correctedSquaredDistance_difference ha hb hN hsc.ne' k,abs_div,abs_mul,abs_neg,
    abs_of_pos (sq_pos_of_pos hN),abs_of_pos hsc]
  apply (div_le_iff₀ hsc).mpr
  nlinarith

end
end jacobi.Jacobi
