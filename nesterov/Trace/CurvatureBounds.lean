import nesterov.Trace.Curvature

/-! Positive source symbols give a uniform radial comparison at all strictly
stable curvatures below the limiting endpoint. -/
namespace nesterov.Trace
noncomputable section
open Polynomial Complex Metric Set Real
open scoped Topology
namespace DoubleRootData
variable (A : DoubleRootData)

theorem curvature_symbol_nonneg {lam : ℝ} (hlam0 : 0<lam) (hlam1 : lam<1)
    (hS : ∀ ω∈Ioo (0:ℝ) Real.pi,0≤A.symbol ω) {z : ℂ} (hz : Complex.normSq z=1) :
    0≤((1-z)*eval (A.phi 0) z*star (eval (A.phi lam) z)).re := by
  rw [A.curvature_symbol]
  have hξ : 0≤1-z.re := by
    simp only [Complex.normSq_apply] at hz
    nlinarith [sq_nonneg z.im]
  exact add_nonneg (mul_nonneg hlam0.le (A.unitSymbol_nonneg hS z hz))
    (mul_nonneg (mul_nonneg (sub_nonneg.mpr hlam1.le) hξ) (Complex.normSq_nonneg _))

theorem curvature_boundary {lam : ℝ} (hlam : 0<lam)
    (hs : ∀ z : ℂ,eval (A.phi lam) z=0 → ‖z‖<1) {z : ℂ}
    (hz : Complex.normSq z=1) (hz1 : z≠1) :
    boundaryValue (A.curvatureQuotient lam hs).diskFunction z=
      (1+z.re)*((1-z)*eval (A.phi 0) z*star (eval (A.phi lam) z)).re/
        (2*(1-z.re)^2*Complex.normSq (eval (A.phi lam) z)) := by
  let Q := A.curvatureQuotient lam hs
  have hnorm : ‖z‖=1 := by
    apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤1)).mp
    rw [Complex.sq_norm,hz,one_pow]
  have hz0 : z≠0 := fun hh=>by rw [hh,norm_zero] at hnorm;norm_num at hnorm
  have hd : eval (A.phi lam) z≠0 := fun hh=>by
    have hi := hs z hh
    rw [hnorm] at hi
    exact lt_irrefl _ hi
  have hi : z⁻¹=star z := by
    rw [Complex.inv_def,hz]
    simp only [inv_one,Complex.ofReal_one,mul_one,Complex.star_def]
  have hdc : eval (A.phi lam) z⁻¹≠0 := by rw [hi,eval_conj];exact star_ne_zero.mpr hd
  have hFi : (Q.diskFunction z).im=
      -(((-z*(z+1)*eval A.q z)/eval (A.phi lam) z).im) := by
    rw [Q.diskFunction_reciprocal hz0 hdc,hi,eval_conj,eval_conj]
    rw [←star_div₀]
    simp only [Q,curvatureQuotient,Complex.sub_im,Complex.one_im,sub_zero,
      Complex.star_def,Complex.conj_im,A.numerator_eval]
  have hreal : (Q.diskFunction 1).im=0 := by rw [A.curvatureQuotient_one hlam];rfl
  rw [boundaryValue_eq_weighted_im hz hz1 hreal,hFi]
  have hφ0 : eval (A.phi 0) z= -(z-1)^2*eval A.q z := by
    simp only [phi,C_0,zero_mul,zero_sub,eval_neg]
    change -eval A.method.recurrencePolynomial z=_
    rw [A.factor,eval_mul,eval_pow,eval_sub,eval_X,eval_C,Complex.ofReal_one]
    ring
  rw [hφ0]
  simpa only [mul_neg,neg_mul] using weighted_quotient_identity hz hz1 (eval A.q z) (eval (A.phi lam) z) hd

theorem curvature_boundary_nonneg {lam : ℝ} (hlam0 : 0<lam) (hlam1 : lam<1)
    (hs : ∀ z : ℂ,eval (A.phi lam) z=0 → ‖z‖<1)
    (hS : ∀ ω∈Ioo (0:ℝ) Real.pi,0≤A.symbol ω) :
    ∀ z : ℂ,Complex.normSq z=1 → 0≤boundaryValue (A.curvatureQuotient lam hs).diskFunction z := by
  let Q := A.curvatureQuotient lam hs
  have hF := Q.diskFunction_diffCont
  have hG := Q.diskFunction_dslope_diffCont
  have hc : ContinuousOn (boundaryValue Q.diskFunction) (sphere (0:ℂ) 1) := by
    apply (boundaryValue_continuousOn ?_ ?_).mono sphere_subset_closedBall
    · simpa only [closure_ball (0:ℂ) (by norm_num : (1:ℝ)≠0)] using hF.2
    · simpa only [closure_ball (0:ℂ) (by norm_num : (1:ℝ)≠0)] using hG.2
  have hreal : (Q.diskFunction 1).im=0 := by rw [A.curvatureQuotient_one hlam0];rfl
  have hconj : ∀ z∈sphere (0:ℂ) 1,boundaryValue Q.diskFunction (star z)=boundaryValue Q.diskFunction z := by
    intro z hz
    have hn : ‖z‖=1 := by simpa [mem_sphere,dist_zero_right] using hz
    apply Q.boundaryValue_conj _ hreal
    rw [Complex.normSq_eq_norm_sq,hn,one_pow]
  apply nonneg_unit_of_upper hc hconj
  intro ω hω
  let z := Complex.exp ((ω:ℂ)*Complex.I)
  have hz : Complex.normSq z=1 := by simp [z,Complex.normSq_eq_norm_sq]
  have him : z.im=Real.sin ω := by
    change (Complex.exp ((ω:ℂ)*Complex.I)).im=Real.sin ω
    rw [Complex.exp_mul_I,←Complex.ofReal_cos,←Complex.ofReal_sin]
    simp only [Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,
      Complex.I_im,mul_one,zero_mul,add_zero,zero_add]
  have hz1 : z≠1 := by
    intro hh
    have hp := Real.sin_pos_of_pos_of_lt_pi hω.1 hω.2
    rw [←him,hh,Complex.one_im] at hp
    exact lt_irrefl _ hp
  change 0≤boundaryValue Q.diskFunction z
  rw [A.curvature_boundary hlam0 hs hz hz1]
  have hξ : 0≤1+z.re := by
    simp only [Complex.normSq_apply] at hz
    nlinarith [sq_nonneg z.im]
  exact div_nonneg (mul_nonneg hξ (A.curvature_symbol_nonneg hlam0 hlam1 hS hz))
    (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (Complex.normSq_nonneg _))

theorem curvature_radial_bounds {lam : ℝ} (hlam0 : 0<lam) (hlam1 : lam<1)
    (hs : ∀ z : ℂ,eval (A.phi lam) z=0 → ‖z‖<1)
    (hS : ∀ ω∈Ioo (0:ℝ) Real.pi,0≤A.symbol ω) {x : ℝ} (hx0 : 0<x) (hx1 : x<1) :
    0≤((A.curvatureQuotient lam hs).diskFunction (x:ℂ)).re ∧
      ((A.curvatureQuotient lam hs).diskFunction (x:ℂ)).re≤2/(lam*A.y)-1 := by
  let Q := A.curvatureQuotient lam hs
  have hreal : (Q.diskFunction 1).im=0 := by rw [A.curvatureQuotient_one hlam0];rfl
  have hB := A.curvature_boundary_nonneg hlam0 hlam1 hs hS
  have hh := radial_comparison Q.diskFunction_diffCont Q.diskFunction_dslope_diffCont
    Q.diskFunction_zero hreal (fun z hz=>by
      have hn : ‖z‖=1 := by simpa [mem_sphere,dist_zero_right] using hz
      exact hB z (by rw [Complex.normSq_eq_norm_sq,hn,one_pow])) hx0 hx1
  rw [A.curvatureQuotient_one hlam0,Complex.ofReal_re] at hh
  exact hh

end DoubleRootData
end
end nesterov.Trace
