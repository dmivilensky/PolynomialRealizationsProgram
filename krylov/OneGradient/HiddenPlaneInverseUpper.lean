import krylov.OneGradient.HiddenPlaneCentre
import krylov.OneGradient.CentredInverseRisk
import krylov.OneGradient.TwoDimensionalAttainment
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(c), finite actual centred inverse upper bound.
Use: the observed-column centre inverse attains V2 up to one explicit
uniform cubic loss on the entire original hidden spectral disc.
Source: actual hidden-entry interval, real centre contraction and inverse
domain, exact hidden rank-one action and the attained scalar maximum.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Reference krylov.LinearAlgebra
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The actual observed-column centring inverse has the original V2
upper coefficient with an explicit uniform cubic loss, on every true
contractive symmetric operator on a complete physical orthonormal plane.
Every inverse domain and actual hidden-entry bound is derived, including
singular disc corners. No smoothness of the centre or output is assumed.
Use: the genuine known-base two-query algorithm's exact observed column
therefore gives a finite all-scenario upper bound before taking a limit.
Article: main_krylov, thm:local(c), real centring upper construction.
Proof: the true observed centre is contractive, so its actual inverse is
controlled. The exact hidden rank-one action gives the sharp leading
hidden/output coefficient; the full closed-disc scalar maximum is V2.
The genuine inverse correction loss is bounded by 2W²(W+w) omega³. -/
theorem hiddenPlane_centred_inverse_upper
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) (hMn : ‖M‖≤1)
    (e h : EuclideanSpace ℝ (Fin n)) (he : ‖e‖=1) (hh : ‖h‖=1) (heh : inner ℝ e h=0)
    (hfull : ∀ v : EuclideanSpace ℝ (Fin n),(inner ℝ e v) • e+(inner ℝ h v) • h=v)
    (W w omega sigma : ℝ) (hW : 0< W) (hw : 0≤ w) (homega : 0≤ omega) (hsigma : 0≤ sigma)
    (hsmall : W*omega≤(1/2 : ℝ))
    (F : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hF : ‖F‖≤ w*omega) :
    let T := cgOperator M
    let a := inner ℝ e (T h)
    let g := inner ℝ h (T h)
    let S := planarMatrix e h (hiddenPlaneCentre a g) a g
    let rho := (W*omega*sigma) • T h
    let u : EuclideanSpace ℝ (Fin n) := -(cgOperator ((1+(W*omega) • S)⁻¹) rho)
    show Prop from ‖rho+cgOperator (1+(W*omega) • M) u+F u‖≤
      sigma*(twoDimensionalValue W w*omega^2+2*W^2*(W+w)*omega^3) := by
  let T := cgOperator M
  let a := inner ℝ e (T h)
  let g := inner ℝ h (T h)
  let y := inner ℝ e (T e)
  let S := planarMatrix e h (hiddenPlaneCentre a g) a g
  let eta := W*omega
  let C := 1+eta • S
  let Delta := cgOperator (eta • (M-S))
  let rho := (eta*sigma) • T h
  let u : EuclideanSpace ℝ (Fin n) := -(cgOperator (C⁻¹) rho)
  have heta : 0≤ eta := mul_nonneg hW.le homega
  have hTs : T.toLinearMap.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr (Matrix.isHermitian_iff_isSymm.mpr hM)
  have hTn : ‖T‖≤1 := by
    rw [show ‖T‖=‖M‖ from (Matrix.l2_opNorm_toEuclideanCLM M).symm]
    exact hMn
  have hobs := hiddenPlane_observed_centre T hTs hTn e h he hh heh
  have hdisc : a^2+g^2≤1 := (hiddenPlane_observed_interval T hTs hTn e h he hh heh).1
  have hSn : ‖S‖≤1 := hobs.2.2.2
  have hwidth : 0≤ hiddenPlaneHalfWidth a g := hobs.1
  have hwidth1 : hiddenPlaneHalfWidth a g≤1 := hobs.2.1
  have hdelta : |y-hiddenPlaneCentre a g|≤ hiddenPlaneHalfWidth a g := hobs.2.2.1
  have hCnorm : ‖C-1‖≤ eta := by
    have heq : C-1=eta • S := by dsimp only [C];abel
    rw [heq,norm_smul,Real.norm_of_nonneg heta]
    exact (mul_le_mul_of_nonneg_left hSn heta).trans_eq (mul_one _)
  have hCsmall : ‖C-1‖≤(1/2 : ℝ) := hCnorm.trans hsmall
  have hDelta (v : EuclideanSpace ℝ (Fin n)) :
      Delta v=(eta*(y-hiddenPlaneCentre a g)*inner ℝ e v) • e := by
    simp only [Delta,cgOperator,map_smul,map_sub,_root_.smul_apply,_root_.sub_apply]
    have hdif : T v-cgOperator S v=((y-hiddenPlaneCentre a g)*inner ℝ e v) • e :=
      hiddenPlane_centre_difference T hTs e h hfull v
    change eta • (T v-cgOperator S v)=_
    rw [hdif]
    module
  have hDn : ‖Delta‖≤ eta := by
    apply ContinuousLinearMap.opNorm_le_bound _ heta
    intro v
    rw [hDelta,norm_smul,he,mul_one,Real.norm_eq_abs,abs_mul,abs_mul,abs_of_nonneg heta]
    have hi : |inner ℝ e v|≤‖v‖ := by simpa only [he,one_mul] using abs_real_inner_le_norm e v
    have hd : |y-hiddenPlaneCentre a g|≤1 := hdelta.trans hwidth1
    nlinarith [mul_le_mul_of_nonneg_left hi (mul_nonneg heta (abs_nonneg (y-hiddenPlaneCentre a g))),
      mul_le_mul_of_nonneg_left hd (mul_nonneg heta (norm_nonneg v))]
  have hTh : T h=a • e+g • h := (hfull (T h)).symm
  have hThNorm : ‖T h‖=Real.sqrt (a^2+g^2) := by
    rw [hTh,← Real.sqrt_sq (norm_nonneg _),planar_coordinates_norm_sq e h he hh heh]
  have hRhoNorm : ‖rho‖=eta*sigma*Real.sqrt (a^2+g^2) := by
    rw [show rho=(eta*sigma) • T h from rfl,norm_smul,Real.norm_of_nonneg (mul_nonneg heta hsigma),hThNorm]
  have hRhoBound : ‖rho‖≤ eta*sigma := by
    have ht : ‖T h‖≤1 := by
      simpa only [hh,mul_one] using ((T.le_opNorm h).trans
        (mul_le_mul_of_nonneg_right hTn (norm_nonneg h)))
    rw [show rho=(eta*sigma) • T h from rfl,norm_smul,Real.norm_of_nonneg (mul_nonneg heta hsigma)]
    exact (mul_le_mul_of_nonneg_left ht (mul_nonneg heta hsigma)).trans_eq (mul_one _)
  have hERho : inner ℝ e rho=eta*sigma*a := by
    have hee : inner ℝ e e=1 := by rw [real_inner_self_eq_norm_sq,he,one_pow]
    rw [show rho=(eta*sigma) • T h from rfl,hTh,real_inner_smul_right,inner_add_right,
      real_inner_smul_right,real_inner_smul_right,hee,heh,mul_one,mul_zero,add_zero]
  have hDleading : ‖Delta rho‖≤ eta^2*sigma*|a| *hiddenPlaneHalfWidth a g := by
    rw [hDelta,norm_smul,he,mul_one,Real.norm_eq_abs,hERho]
    simp only [abs_mul,abs_of_nonneg heta,abs_of_nonneg hsigma]
    have hb := mul_le_mul_of_nonneg_left hdelta (by positivity : 0≤ eta^2*sigma*|a|)
    nlinarith
  have hscalar := (twoDimensional_hidden_maximum W w hW hw).1 |a| |g| (abs_nonneg _) (abs_nonneg _) (by simpa only [sq_abs] using hdisc)
  have hscalar' : W^2*|a| *hiddenPlaneHalfWidth a g+w*W*Real.sqrt (a^2+g^2)≤ twoDimensionalValue W w := by
    simpa only [twoDimensionalHiddenValue,sq_abs,hiddenPlaneHalfWidth] using hscalar
  have hLeading : ‖Delta rho‖+‖F‖*‖rho‖≤sigma*(twoDimensionalValue W w*omega^2) := by
    calc
      _ ≤ eta^2*sigma*|a| *hiddenPlaneHalfWidth a g+w*omega*‖rho‖ :=
        add_le_add hDleading (mul_le_mul_of_nonneg_right hF (norm_nonneg rho))
      _ = (sigma*omega^2)*(W^2*|a| *hiddenPlaneHalfWidth a g+w*W*Real.sqrt (a^2+g^2)) := by
        rw [hRhoNorm]
        dsimp only [eta]
        ring
      _ ≤ (sigma*omega^2)*twoDimensionalValue W w :=
        mul_le_mul_of_nonneg_left hscalar' (mul_nonneg hsigma (sq_nonneg omega))
      _ = _ := by ring
  have hError : (‖Delta‖+‖F‖)*(2*‖C-1‖*‖rho‖)≤ sigma*(2*W^2*(W+w)*omega^3) := by
    have hfirst : ‖Delta‖+‖F‖≤ eta+w*omega := add_le_add hDn hF
    have hsecond : 2*‖C-1‖*‖rho‖≤2*eta*(eta*sigma) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hCnorm (by norm_num)) hRhoBound (norm_nonneg rho) (by positivity)
    have hm := mul_le_mul hfirst hsecond (by positivity) (by positivity : 0≤ eta+w*omega)
    exact hm.trans_eq (by dsimp only [eta];ring)
  have hresult := centred_inverse_residual_bound C hCsmall Delta F rho
  have hmodel : cgOperator C+Delta=cgOperator (1+eta • M) := by
    dsimp only [C,Delta,cgOperator]
    rw [← map_add]
    congr 1
    module
  change ‖rho+cgOperator (1+eta • M) u+F u‖≤_
  rw [hmodel] at hresult
  have hresult' : ‖rho+cgOperator (1+eta • M) u+F u‖≤‖Delta rho‖+‖F‖*‖rho‖+
      (‖Delta‖+‖F‖)*(2*‖C-1‖*‖rho‖) := by
    simpa only [_root_.add_apply,add_assoc] using hresult
  exact hresult'.trans (by nlinarith [hLeading,hError])

end
end krylov.OneGradient
