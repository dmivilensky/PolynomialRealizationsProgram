import jacobi.Fredholm.GreenDecay
import jacobi.Variational.PositivePartCalculus

/-!
Article: jacobi, Theorem D.7.
The actual diagonal equation has its exact zero first integral. Its constant
is fixed from the genuine free diagonal limit by the mean value theorem,
without an assumed derivative limit. This common calculus lemma is applied
to the actual continuous Euler representative in the optimizer module.
Source: Gel'fand--Dikii, smooth positive-cube calculus and the real mean value theorem.
Use: the true optimizer profile, turning geometry and normalized quadratures use this same function.
-/
namespace jacobi.Fredholm
noncomputable section
open Real Set MeasureTheory Filter jacobi.Variational jacobi.Young
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The literal autonomous Fredholm first-integral polynomial with its continuous positive-part branch.
Use: the true optimizer profile, turning geometry and normalized quadratures use this same function.
Article: jacobi, Appendix D.4 (green first integral and optimizer geometry).
-/
def phase (A e g : ℝ) : ℝ := (2*g-1)^2-(4/3:ℝ)*A^2*g*(max (g-e) 0)^3

/-- The exact conserved expression of the autonomous Fredholm Green equation.
Use: its zero derivative and actual free limit prove the printed first integral.
Article: jacobi, Appendix D.4 (green first integral and optimizer geometry).
-/
def conserved (A e : ℝ) (g d : ℝ → ℝ) (x : ℝ) : ℝ := (d x^2-phase A e (g x))/g x

/-- The true autonomous Green equation makes its literal conserved expression constant.
Use: fixes the profile's first integral from the actual free limit, with no assumed conservation certificate.
Article: jacobi, Appendix D.4 (green first integral and optimizer geometry).
Proof: differentiate the positive cube also at the switching level.
The quotient derivative has numerator d times the exact Gel'fand--Dikii
identity, so it is zero wherever the actual diagonal is positive. -/
theorem conserved_hasDerivAt (A e : ℝ) {g d : ℝ → ℝ}
    (hg : ∀ x,HasDerivAt g (d x) x) (hd : ∀ x,DifferentiableAt ℝ d x)
    (hpos : ∀ x,0<g x)
    (hgd : ∀ x,2*g x*deriv d x-d x^2-4*(1-A^2*(max (g x-e) 0)^2)*g x^2+1=0) (x : ℝ) :
    HasDerivAt (conserved A e g d) 0 x := by
  -- Every derivative is of the actual value and slope; clipping is differentiated through its C1 cube.
  have hp := (positiveCube_hasDerivAt (g x-e)).comp x ((hg x).sub_const e)
  have hF := ((((hg x).const_mul 2).sub_const 1).pow 2).sub
    ((((hg x).mul hp).const_mul ((4/3:ℝ)*A^2)))
  convert (((hd x).hasDerivAt.pow 2).sub hF).div (hg x) (hpos x).ne' using 1
  · funext t
    dsimp only [conserved,phase,Pi.pow_apply,Pi.mul_apply,Pi.sub_apply,Pi.div_apply,Function.comp_def]
    ring
  · dsimp only [Pi.pow_apply,Pi.mul_apply,Pi.sub_apply,Function.comp_def]
    norm_num only [Nat.cast_ofNat,Nat.reduceSub,pow_one]
    symm
    apply div_eq_zero_iff.mpr
    left
    linear_combination (d x)*(hgd x)

/-- The genuine free limit forces the conserved Green first integral to be zero.
Use: yields the actual optimizer equation d²=F(g) and excludes any undetermined energy constant.
Article: jacobi, Theorem D.7.
Proof: actual zero derivative gives a constant. On each interval [n,n+1],
the real mean value theorem supplies a slope equal to g(n+1)-g(n).
The actual free limit makes these slopes tend to zero. Evaluating the
conserved expression along that sequence fixes its constant at zero. -/
theorem green_first_integral (A e : ℝ) (he : (1/2:ℝ)≤e) {g d : ℝ → ℝ}
    (hg : ∀ x,HasDerivAt g (d x) x) (hd : ∀ x,DifferentiableAt ℝ d x)
    (hpos : ∀ x,0<g x)
    (hgd : ∀ x,2*g x*deriv d x-d x^2-4*(1-A^2*(max (g x-e) 0)^2)*g x^2+1=0)
    (hlim : Tendsto g atTop (𝓝 (1/2:ℝ))) (x : ℝ) : d x^2=phase A e (g x) := by
  -- The mean-value slopes avoid an unsupported assertion that a convergent function has derivative limit zero.
  have hY := conserved_hasDerivAt A e hg hd hpos hgd
  have hconst (t : ℝ) : conserved A e g d t=conserved A e g d 0 :=
    is_const_of_deriv_eq_zero (fun t => (hY t).differentiableAt) (fun t => (hY t).deriv) t 0
  have hc : Continuous g := continuous_iff_continuousAt.mpr fun t => (hg t).continuousAt
  have hmean (n : ℕ) : ∃ c : ℝ,c∈Ioo (n:ℝ) ((n:ℝ)+1) ∧ d c=g ((n:ℝ)+1)-g n := by
    obtain ⟨c,hc',hd'⟩ := exists_hasDerivAt_eq_slope g d (by linarith : (n:ℝ)<(n:ℝ)+1)
      hc.continuousOn (fun t _ht => hg t)
    exact ⟨c,hc',by simpa only [add_sub_cancel_left,div_one] using hd'⟩
  choose c hcn hcd using hmean
  have hcat : Tendsto c atTop atTop := tendsto_atTop_mono (fun n => (hcn n).1.le) tendsto_natCast_atTop_atTop
  have hgn := hlim.comp (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop)
  have hgn1 := hlim.comp (tendsto_atTop_add_const_right atTop (1:ℝ) tendsto_natCast_atTop_atTop)
  have hdn : Tendsto (fun n => d (c n)) atTop (𝓝 0) := by
    simpa only [hcd,sub_self,Function.comp_def] using hgn1.sub hgn
  have hgc := hlim.comp hcat
  let Φ (z : ℝ × ℝ) := (z.2^2-phase A e z.1)/z.1
  have hΦ : ContinuousAt Φ ((1/2:ℝ),0) := by unfold Φ phase; fun_prop (disch := norm_num)
  have hzero : Φ ((1/2:ℝ),0)=0 := by
    have hh : (1/2:ℝ)-e≤0 := by linarith
    norm_num [Φ,phase,max_eq_right hh]
  have hseq : Tendsto (fun n => conserved A e g d (c n)) atTop (𝓝 0) := by
    have hh := hΦ.tendsto.comp (hgc.prodMk_nhds hdn)
    rw [hzero] at hh
    exact hh
  have hz : conserved A e g d 0=0 := by
    have hh : Tendsto (fun _n : ℕ => conserved A e g d 0) atTop (𝓝 0) := by
      simpa only [hconst] using hseq
    exact tendsto_nhds_unique tendsto_const_nhds hh
  have hx : conserved A e g d x=0 := (hconst x).trans hz
  exact sub_eq_zero.mp ((div_eq_zero_iff.mp hx).resolve_right (hpos x).ne')

end
end jacobi.Fredholm
