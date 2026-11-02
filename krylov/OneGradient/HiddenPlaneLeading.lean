import krylov.OneGradient.HiddenPlaneFibre
import krylov.OneGradient.TwoDimensionalAttainment
import krylov.Information.PlanarAdmissibility
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(c), exact actual four-adversary coefficient.
Use: retain the true length of an arbitrary last query in the hidden-entry
and independent output-defect game, before reference normalization.
Source: exact planar actions, the genuine closed-disc Schur half-width
and the actual Euclidean norm of orthogonal physical coordinates.
-/

namespace krylov.OneGradient
noncomputable section
open krylov.Reference krylov.LinearAlgebra krylov.Information
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The actual hidden half-width belongs to [0,1] at every genuine
attaining cross coordinate, with a derived strict denominator domain.
Use: real hidden rank-one adversaries satisfy their exact operator budget.
Article: main_krylov, thm:local(c), true adversarial hidden radius.
Proof: the nonzero cross coordinate and closed disc force 1-g²>0.
Its genuine Schur ratio is nonnegative and at most one. -/
theorem hiddenPlane_halfWidth_bounds (a g : ℝ) (ha : 0< a) (hd : a^2+g^2≤1) :
    0≤ hiddenPlaneHalfWidth a g ∧ hiddenPlaneHalfWidth a g≤1 := by
  have hden : 0<1-g^2 := by nlinarith
  unfold hiddenPlaneHalfWidth
  constructor
  · exact sub_nonneg.mpr ((div_le_one hden).mpr (by linarith))
  · exact sub_le_self _ (div_nonneg (sq_nonneg a) hden.le)

/-- The original hidden-entry/output-defect coefficient is exactly the
seminorm of the actual opposite observed-column increment, with the real
query length retained. No approximation of query directions is made.
Use: combine the attained V2 point with the finite four-model game for
arbitrary competing policies, including a zero second query.
Article: main_krylov, thm:local(c), exact four-adversary leading term.
Proof: the true observed planar column is a e+g h. Its actual hidden
diagonal action is a times the Schur half-width in the e direction.
Orthogonal coordinate norms give the exact remaining output-ball term. -/
theorem hiddenPlane_leading_coefficient
    (e h : EuclideanSpace ℝ (Fin n)) (he : ‖e‖=1) (hh : ‖h‖=1) (heh : inner ℝ e h=0)
    (a g W w omega q : ℝ) (ha : 0< a) (hd : a^2+g^2≤1)
    (hW : 0≤ W) (homega : 0≤ omega) (hq : 0≤ q) :
    let S := planarMatrix e h (hiddenPlaneCentre a g) a g
    let D := Matrix.toEuclideanCLM (𝕜 := ℝ) ((W*omega) • planarMatrix e h (hiddenPlaneHalfWidth a g) 0 0)
    let z := (W*omega*q) • Matrix.toEuclideanCLM (𝕜 := ℝ) S h
    ‖D z‖+(w*omega)*‖z‖=q*omega^2*twoDimensionalHiddenValue W w a g := by
  let H := hiddenPlaneHalfWidth a g
  have hH : 0≤ H := (hiddenPlane_halfWidth_bounds a g ha hd).1
  have hee : inner ℝ e e=1 := by rw [real_inner_self_eq_norm_sq,he,one_pow]
  have hcol := hiddenPlane_observed_column e h hh heh a g (hiddenPlaneCentre a g)
  have hcolnorm : ‖a • e+g • h‖=Real.sqrt (a^2+g^2) := by
    rw [← Real.sqrt_sq (norm_nonneg _),planar_coordinates_norm_sq e h he hh heh]
  have hdiag : Matrix.toEuclideanCLM (𝕜 := ℝ) (planarMatrix e h H 0 0) (a • e+g • h)=(H*a) • e := by
    rw [planarMatrix_action]
    simp only [inner_add_right,real_inner_smul_right,hee,heh,mul_one,mul_zero,add_zero,
      zero_mul,zero_smul]
  dsimp only
  rw [hcol,map_smul,map_smul,_root_.smul_apply,hdiag,smul_smul,smul_smul,
    norm_smul,norm_smul,he,mul_one,hcolnorm,
    Real.norm_of_nonneg (by positivity : 0≤ W*omega*q),
    Real.norm_of_nonneg (by positivity : 0≤ W*omega*q*(W*omega)*(H*a))]
  unfold twoDimensionalHiddenValue
  change _=q*omega^2*(W^2*a*H+w*W*Real.sqrt (a^2+g^2))
  ring

end
end krylov.OneGradient
