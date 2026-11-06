import nesterov.Trace.SymbolReduction
import nesterov.Trace.Rigidity

/-! Curvatures below the endpoint are strictly Schur after common-mode
cancellation. Their positive trace kernels give one radial comparison. -/
namespace nesterov.Trace
noncomputable section
open Polynomial Complex Metric Set Real
open scoped Topology
namespace DoubleRootData
variable (A : DoubleRootData)

theorem phi_affine (lam : ℝ) : A.phi lam=C lam*A.phi 1+C (1-lam)*A.phi 0 := by
  unfold phi
  simp only [C_1,C_0,one_mul,zero_mul,zero_sub,map_sub]
  ring

theorem curvature_symbol (lam : ℝ) (z : ℂ) :
    ((1-z)*eval (A.phi 0) z*star (eval (A.phi lam) z)).re=
      lam*A.unitSymbol z+(1-lam)*(1-z.re)*Complex.normSq (eval (A.phi 0) z) := by
  rw [A.phi_affine lam,eval_add,eval_mul,eval_mul,eval_C,eval_C]
  unfold unitSymbol
  simp only [Complex.star_def,Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,
    Complex.sub_re,Complex.sub_im,Complex.one_re,Complex.one_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.conj_re,Complex.conj_im,Complex.normSq_apply]
  ring

theorem curvature_strict_of_closed (hcop : IsCoprime A.u A.v)
    (hS : ∀ ω∈Ioo (0:ℝ) Real.pi,0≤A.symbol ω) {lam : ℝ} (hlam0 : 0<lam) (hlam1 : lam<1)
    (hclosed : ∀ z : ℂ,eval (A.phi lam) z=0 → ‖z‖≤1) :
    ∀ z : ℂ,eval (A.phi lam) z=0 → ‖z‖<1 := by
  intro z hz
  have hle := hclosed z hz
  by_contra hn
  have hnorm : ‖z‖=1 := le_antisymm hle (le_of_not_gt hn)
  have hns : Complex.normSq z=1 := by rw [Complex.normSq_eq_norm_sq,hnorm,one_pow]
  have hz1 : z≠1 := by
    intro he
    rw [he,eval_one,A.phi_one] at hz
    exact (Complex.ofReal_ne_zero.mpr hlam0.ne') hz
  have hξ : 0<1-z.re := by
    have hre : z.re≤1 := (Complex.re_le_norm z).trans hle
    refine lt_of_le_of_ne (sub_nonneg.mpr hre) ?_
    intro hh
    have hr : z.re=1 := by linarith
    have hi : z.im=0 := by simp only [Complex.normSq_apply,hr] at hns;nlinarith
    exact hz1 (Complex.ext hr hi)
  have hS0 : 0≤A.unitSymbol z := A.unitSymbol_nonneg hS z hns
  have he := A.curvature_symbol lam z
  rw [hz,star_zero,mul_zero,Complex.zero_re] at he
  have hp : 0<(1-lam)*(1-z.re) := mul_pos (sub_pos.mpr hlam1) hξ
  have hφ0 : eval (A.phi 0) z=0 := by
    by_contra hne
    have hh := mul_pos hp (Complex.normSq_pos.mpr hne)
    nlinarith [mul_nonneg hlam0.le hS0]
  have hv : eval A.v z=0 := by
    simpa only [phi,C_0,zero_mul,zero_sub,eval_neg,neg_eq_zero] using hφ0
  have hu : eval A.u z=0 := by
    have hh := hz
    simp only [phi,eval_sub,eval_mul,eval_C,hv,sub_zero] at hh
    exact (mul_eq_zero.mp hh).resolve_left (Complex.ofReal_ne_zero.mpr hlam0.ne')
  obtain ⟨a,b,hab⟩ := hcop
  have hh := congrArg (fun p=>eval p z) hab
  rw [eval_add,eval_mul,eval_mul,hu,hv,mul_zero,mul_zero,zero_add] at hh
  norm_num only [eval,Polynomial.map_one,Polynomial.eval_one] at hh

def curvatureQuotient (lam : ℝ) (hs : ∀ z : ℂ,eval (A.phi lam) z=0 → ‖z‖<1) : StableQuotient where
  numerator := A.numerator
  denominator := A.phi lam
  denominator_ne := by
    apply Polynomial.leadingCoeff_ne_zero.mp
    rw [A.phi_leadingCoeff]
    exact neg_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr A.v_ne_zero)
  degree_eq := A.numerator_degree.trans (A.phi_natDegree lam).symm
  leading_eq := by rw [A.numerator_leading,A.phi_leadingCoeff,A.v_leading]
  roots_inside := hs

theorem curvatureQuotient_one {lam : ℝ} (hlam : 0<lam)
    (hs : ∀ z : ℂ,eval (A.phi lam) z=0 → ‖z‖<1) :
    (A.curvatureQuotient lam hs).diskFunction 1=((2/(lam*A.y)-1:ℝ):ℂ) := by
  have hd : eval (A.curvatureQuotient lam hs).denominator (1:ℂ)⁻¹≠0 := by
    change eval (A.phi lam) (1:ℂ)⁻¹≠0
    rw [inv_one,eval_one,A.phi_one]
    exact Complex.ofReal_ne_zero.mpr hlam.ne'
  rw [StableQuotient.diskFunction_reciprocal _ (by norm_num : (1:ℂ)≠0) hd]
  simp only [curvatureQuotient,inv_one,eval_one,A.numerator_one,A.phi_one]
  push_cast
  field_simp [hlam.ne',A.y_pos.ne']

end DoubleRootData
end
end nesterov.Trace
