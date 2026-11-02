import krylov.Functions.RankOneCriticalScalar
import krylov.Convergence.OneGradientCubicSource

/-!
Article: main_krylov, thm:LB, genuine arbitrary-dimensional cubic critical point.
Use: explicitly construct the true critical point uniformly over bounded
rank-one cubic coefficients, including data-dependent discontinuous choices.
Source: stable scalar quadratic root and the actual polynomial gradient.
-/
namespace krylov.Functions
noncomputable section
open krylov.Convergence
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Explicit true small critical branch; R is the actual inverse of the
quadratic Hessian, not a prescribed minimizer expansion. Article: thm:LB. -/
def rankOneCriticalPoint (R : E →L[ℝ] E) (g a : E) (t : ℝ) : E :=
  -(R g)-(t/2*(rankOneCriticalRoot (t*inner ℝ a (R a)) (inner ℝ a (R g)))^2) • R a

/-- The explicitly constructed vector is a true zero of the actual
cubic objective's gradient. Article: main_krylov, thm:LB. -/
theorem rankOneCriticalPoint_critical (Q R : E →L[ℝ] E)
    (hQR : ∀ v : E,Q (R v)=v) (g a : E) (t : ℝ)
    (hdisc : 0≤1-2*(t*inner ℝ a (R a))*(inner ℝ a (R g))) :
    oneGradientCubicGradient Q g a t (rankOneCriticalPoint R g a t)=0 := by
  let u := rankOneCriticalRoot (t*inner ℝ a (R a)) (inner ℝ a (R g))
  have hu := rankOneCriticalRoot_equation _ _ hdisc
  have hcoord : inner ℝ a (rankOneCriticalPoint R g a t)=u := by
    simp only [rankOneCriticalPoint,inner_sub_right,inner_neg_right,real_inner_smul_right]
    change -(inner ℝ a (R g))-t/2*u^2*inner ℝ a (R a)=u
    change (t*inner ℝ a (R a))/2*u^2+u+inner ℝ a (R g)=0 at hu
    nlinarith only [hu]
  rw [oneGradientCubicGradient,hcoord]
  simp only [rankOneCriticalPoint,map_sub,map_neg,map_smul,hQR]
  change g+(-g-(t/2*u^2) • a)+(t/2*u^2) • a=0
  abel

/-- A bounded actual inverse controls the true forcing and rank-one
inverse pairings, with constants independent of the source parameters.
Article: main_krylov, thm:LB. -/
theorem rankOne_inverse_pairing_bound (R : E →L[ℝ] E) (K : ℝ) (_hK : 0≤K)
    (hR : ‖R‖≤K) (a v : E) : |inner ℝ a (R v)|≤K*‖a‖*‖v‖ := by
  have hn := (R.le_opNorm v).trans (mul_le_mul_of_nonneg_right hR (norm_nonneg v))
  have hh := (norm_inner_le_norm (𝕜 := ℝ) a (R v)).trans
    (mul_le_mul_of_nonneg_left hn (norm_nonneg a))
  rw [Real.norm_eq_abs] at hh
  nlinarith only [hh]

/-- Original small forcing gives a real, uniformly controlled critical
branch. The bound is uniform in every |t|≤M and every actual inverse
with norm at most K; no smoothness of their selection is required.
Article: main_krylov, thm:LB. -/
theorem rankOneCriticalPoint_bounds (R : E →L[ℝ] E) (g a : E) (t M K : ℝ)
    (hM : 0≤M) (hK : 0≤K) (ht : |t|≤M) (hR : ‖R‖≤K)
    (hsmall : 2*M*K^2*‖a‖^3*‖g‖≤1) :
    0≤1-2*(t*inner ℝ a (R a))*(inner ℝ a (R g)) ∧
      ‖rankOneCriticalPoint R g a t+R g‖≤2*M*K^3*‖a‖^3*‖g‖^2 ∧
      ‖rankOneCriticalPoint R g a t‖≤2*K*‖g‖ := by
  have hc := rankOne_inverse_pairing_bound R K hK hR a g
  have hq : |inner ℝ a (R a)|≤K*‖a‖^2 := by
    simpa only [pow_two,mul_assoc] using rankOne_inverse_pairing_bound R K hK hR a a
  have hprod : |2*(t*inner ℝ a (R a))*(inner ℝ a (R g))|≤2*M*K^2*‖a‖^3*‖g‖ := by
    calc
      _=2*|t| *|inner ℝ a (R a)| *|inner ℝ a (R g)| := by
        simp only [abs_mul,abs_of_nonneg (by norm_num : 0≤(2:ℝ))]
        ring
      _≤2*M*(K*‖a‖^2)*(K*‖a‖*‖g‖) := by gcongr
      _=_ := by ring
  have hd : 0≤1-2*(t*inner ℝ a (R a))*(inner ℝ a (R g)) := by
    have hh := (le_abs_self _).trans (hprod.trans hsmall)
    linarith only [hh]
  have hu := (rankOneCriticalRoot_bound (t*inner ℝ a (R a)) (inner ℝ a (R g))).trans
    (mul_le_mul_of_nonneg_left hc (by norm_num : 0≤(2:ℝ)))
  have hRa := (R.le_opNorm a).trans (mul_le_mul_of_nonneg_right hR (norm_nonneg a))
  have hRg := (R.le_opNorm g).trans (mul_le_mul_of_nonneg_right hR (norm_nonneg g))
  have hrem : ‖rankOneCriticalPoint R g a t+R g‖≤2*M*K^3*‖a‖^3*‖g‖^2 := by
    have he : rankOneCriticalPoint R g a t+R g=
        -(t/2*(rankOneCriticalRoot (t*inner ℝ a (R a)) (inner ℝ a (R g)))^2) • R a := by
      dsimp only [rankOneCriticalPoint]
      module
    rw [he,norm_smul,Real.norm_eq_abs,abs_neg,abs_mul,abs_div,abs_pow]
    norm_num only [abs_of_nonneg (by norm_num : 0≤(2:ℝ))]
    calc
      _≤M/2*(2*(K*‖a‖*‖g‖))^2*(K*‖a‖) := by gcongr
      _=_ := by ring
  refine ⟨hd,hrem,?_⟩
  have hn := norm_add_le (rankOneCriticalPoint R g a t+R g) (-(R g))
  rw [add_neg_cancel_right,norm_neg] at hn
  have hscale := mul_le_mul_of_nonneg_right hsmall (by positivity : 0≤K*‖g‖)
  nlinarith only [hn,hrem,hRg,hscale]

end
end krylov.Functions
