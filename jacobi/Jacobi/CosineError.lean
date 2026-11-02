import jacobi.Jacobi.AngularExpansion
import jacobi.Oscillation.CosineTaylor

/-!
Article: jacobi, Proposition B.1.
The true angular expansion and global cosine Taylor estimate give both
printed error terms on the full growing first half. The affine source
model cancels the entire first-order angular term exactly.
Use: applies the actual original angular theorem to the literal corrected trigonometric model in Proposition B.1 (b).
-/
namespace jacobi.Jacobi
noncomputable section
open Real Set Filter jacobi.Bessel jacobi.Oscillation
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- A genuine sharp angular error and exact first-order model cancellation imply the source's two-term corrected cosine error.
Use: applies the actual original angular theorem to the literal corrected trigonometric model in Proposition B.1 (b).
Article: jacobi, Proposition B.1.
Proof: expand the true cosine with its proved global quadratic remainder.
The exact affine-model identity cancels the first-order correction;
bound the remaining angular error times the original model sine. -/
theorem cosine_error_conversion {theta x D eta N t A C L : ℝ}
    (hN : 0<N) (ht : 0<t) (hA : 0≤A) (hC : 0≤C)
    (hdelta : |theta-x|≤A/(N*t))
    (he : |theta-x-D|≤C*(1/(N*t^3)+1/N^3)) (hsin : |sin x|≤L*t/N)
    (hmodel : D*sin x=cos x-eta) :
    |cos theta-eta|≤(A^2/2+C*L)*(1/(N^2*t^2)+t/N^4) := by
  -- The two original error powers arise separately from the true quadratic Taylor term and the sharp angular remainder times sin(x).
  have hTaylor := cosine_linear_remainder x (theta-x)
  rw [show x+(theta-x)=theta by ring] at hTaylor
  have hid : cos theta-eta=(cos theta-cos x+(theta-x)*sin x)-(theta-x-D)*sin x := by
    nlinarith only [hmodel]
  have hsq : (theta-x)^2≤(A/(N*t))^2 := by
    have hh := (sq_le_sq₀ (abs_nonneg (theta-x)) (by positivity : 0≤A/(N*t))).mpr hdelta
    simpa only [sq_abs] using hh
  have h1 : (theta-x)^2/2≤(A^2/2)*(1/(N^2*t^2)+t/N^4) := by
    have hh := div_le_div_of_nonneg_right hsq (show (0:ℝ)≤2 by norm_num)
    have heq : (A/(N*t))^2/2=(A^2/2)/(N^2*t^2) := by field_simp [hN.ne',ht.ne']
    rw [heq] at hh
    have hp : 0≤(A^2/2)*(t/N^4) := by positivity
    have heq2 : (A^2/2)*(1/(N^2*t^2)+t/N^4)=(A^2/2)/(N^2*t^2)+(A^2/2)*(t/N^4) := by ring
    rw [heq2]
    linarith
  have h2 : |(theta-x-D)*sin x|≤(C*L)*(1/(N^2*t^2)+t/N^4) := by
    rw [abs_mul]
    have hh := mul_le_mul he hsin (abs_nonneg _) (by positivity : 0≤C*(1/(N*t^3)+1/N^3))
    convert hh using 1
    field_simp [hN.ne',ht.ne']
  rw [hid]
  calc
    _ ≤ |cos theta-cos x+(theta-x)*sin x|+|(theta-x-D)*sin x| := abs_sub _ _
    _ ≤ (A^2/2)*(1/(N^2*t^2)+t/N^4)+(C*L)*(1/(N^2*t^2)+t/N^4) :=
      add_le_add (hTaylor.trans h1) h2
    _ = _ := by ring

/-- Every original first-half Jacobi node has precisely the source corrected trigonometric-model error, uniformly over its growing index range.
Use: exact reflection gives the full two-edge Proposition B.1 (b).
Article: jacobi, Proposition B.1.
Proof: use the unconditional true angular theorem and coarse angular
error. The exact phase-grid upper bound controls the actual model sine
by L*k/N. Apply the genuine cosine Taylor conversion and the proved
literal affine-model cancellation identity. -/
theorem firstHalf_node_error {a b : ℝ} (ha : -1<a) (hb : -1<b) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ n : ℕ in atTop,0<frequency a b n ∧ ∀ k,2*k<n →
      |cos (finiteAngleAt a b ha hb n k)-modelNode a b n k|≤
        C*(1/((frequency a b n)^2*(k+1:ℝ)^2)+(k+1:ℝ)/(frequency a b n)^4) := by
  -- The sharp original angular error and literal model correction have already been proved; no cosine approximation is supplied as a premise.
  obtain ⟨C,hC,hsharp⟩ := firstHalf_angle_expansion ha hb
  obtain ⟨A,hA,hcoarse⟩ := firstHalf_angle_coarse ha hb
  let L := Real.pi*(|a|+2)
  have hL : 0<L := by dsimp [L]; positivity
  refine ⟨A^2/2+C*L,by positivity,?_⟩
  filter_upwards [hsharp,hcoarse] with n hn hc
  refine ⟨hn.1,?_⟩
  intro k hk
  have hx := (modelAngle_endpoint_bounds ha hb (show k<n by omega)).1
  have hsin : |sin (modelAngle a b n k)|≤L*(k+1:ℝ)/frequency a b n := by
    rw [abs_of_pos (Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2)]
    exact (Real.sin_le hx.1.le).trans
      (div_le_div_of_nonneg_right (phaseGrid_upper a k) hn.1.le)
  exact cosine_error_conversion hn.1 (by positivity) hA.le hC.le
    (hc.2 k hk) (hn.2 k hk) hsin (modelCorrection_sin ha hb (show k<n by omega))

end
end jacobi.Jacobi
