import krylov.Convergence.SlidingRFCRate
import krylov.Convergence.SlidingRFCAnchor
import krylov.Functions.SearchTrajectory
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

/-!
Article: main_krylov, thm:Ip, RFC correction-angle refinement.
Use: identify the actual searched correction with the perpendicular
quadratic error and its ordinary sine angle. Source: genuine chord
stationarity, observed full-model anchoring and true local secant estimates.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Filter Topology Asymptotics krylov.Methods krylov.Functions InnerProductGeometry
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
set_option maxHeartbeats 800000

/-- The real quadratic searched point is the actual perpendicular
projection, including its exact norm-square identity. -/
theorem quadraticSearchPoint_norm_sq (x d : E) (hd : d≠0) :
    ‖quadraticSearchPoint x d‖^2=‖x‖^2-(inner ℝ x d)^2/‖d‖^2 := by
  rw [quadraticSearchPoint,norm_sub_sq_real,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,
    real_inner_smul_right]
  field_simp [norm_ne_zero_iff.mpr hd]
  ring

/-- The actual perpendicular projection has the literal sine-angle norm,
not merely an independently named angular response. -/
theorem quadraticSearchPoint_norm_div_eq_sin (x d : E) (hx : x≠0) (hd : d≠0) :
    ‖quadraticSearchPoint x d‖/‖x‖=Real.sin (angle x d) := by
  apply (sq_eq_sq₀ (div_nonneg (norm_nonneg _) (norm_nonneg _)) (sin_angle_nonneg _ _)).mp
  rw [div_pow,quadraticSearchPoint_norm_sq x d hd,Real.sin_sq,cos_angle]
  field_simp [norm_ne_zero_iff.mpr hx,norm_ne_zero_iff.mpr hd]

/-- The true searched quadratic point is contractive, independently of
the direction length and of any descent assumption. -/
theorem quadraticSearchPoint_norm_le (x d : E) : ‖quadraticSearchPoint x d‖≤‖x‖ := by
  by_cases hd : d=0
  · simp only [hd,quadraticSearchPoint,inner_zero_right,zero_div,zero_smul,sub_zero]
    exact le_rfl
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [quadraticSearchPoint_norm_sq x d hd]
  exact sub_le_self _ (div_nonneg (sq_nonneg _) (sq_nonneg _))

/-- The actual correction after a genuine search has the perpendicular
leading vector whenever the actual corrected endpoint and search error
have their already derived source bounds. This is a finite algebra lemma. -/
theorem correction_perpendicular_error (x d y z : E) {A B e : ℝ}
    (hz : ‖z‖≤A*e*‖x‖) (hy : ‖y-quadraticSearchPoint x d‖≤B*e*‖x‖) :
    ‖(z-y)+quadraticSearchPoint x d‖≤(A+B)*e*‖x‖ := by
  have he : (z-y)+quadraticSearchPoint x d=z-(y-quadraticSearchPoint x d) := by abel_nf
  rw [he]
  exact (norm_sub_le _ _).trans ((add_le_add hz hy).trans_eq (by ring))

/-- A finite quotient comparison keeps the angular gain when the real
step length and correction norm both have source-relative errors. -/
theorem correction_ratio_error {r a b X C K e : ℝ}
    (hX : 0<X) (ha : 0≤a) (haX : a≤X) (hC : 0≤C) (hK : 0≤K) (he : 0≤e)
    (hb : X/2≤b) (hr : |r-a|≤C*e*X) (hs : |b-X|≤K*e*X) :
    |r/b-a/X|≤2*(C+K)*e := by
  have hbpos : 0<b := (half_pos hX).trans_le hb
  have hcross : |r*X-a*b|≤(C+K)*e*X^2 := by
    have hh : r*X-a*b=(r-a)*X+a*(X-b) := by ring
    rw [hh]
    have ht : |(r-a)*X+a*(X-b)|≤C*e*X*X+a*(K*e*X) := by
      apply (abs_add_le _ _).trans
      simp only [abs_mul,abs_of_pos hX,abs_of_nonneg ha]
      exact add_le_add (mul_le_mul_of_nonneg_right hr hX.le)
        (mul_le_mul_of_nonneg_left (by simpa only [abs_sub_comm] using hs) ha)
    have ha' := mul_le_mul_of_nonneg_right haX (show 0≤K*e*X by positivity)
    nlinarith only [ht,ha']
  have hid : r/b-a/X=(r*X-a*b)/(b*X) := by field_simp
  rw [hid,abs_div,abs_of_pos (mul_pos hbpos hX)]
  apply (div_le_iff₀ (mul_pos hbpos hX)).mpr
  apply hcross.trans
  have hh := mul_le_mul_of_nonneg_right hb (show 0≤2*(C+K)*e*X by positivity)
  nlinarith only [hh]

end
end krylov.Convergence
