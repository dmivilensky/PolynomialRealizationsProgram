import nesterov.Flow.Kernel
import nesterov.Flow.Quadrature
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import polyak.Realization.Auxiliary

/-!
Article: Lemma `lem:spread`, the analytic estimates for the spread frequency band.
Use: exact hyperbolic decomposition, positivity on every compact nonzero lag
band and decay of the oscillatory integral before discretizing the spectrum.
-/
namespace nesterov.Flow
noncomputable section
open Set Filter intervalIntegral
open scoped Topology

def spreadU (x : ℝ) : ℝ := ∫ lam in (1:ℝ)..2,lam^2*(1-Real.cos (lam*x))
def spreadV (x : ℝ) : ℝ := ∫ lam in (1:ℝ)..2,lam^2*Real.cos (lam*x)

theorem forwardKernel_decomposition {c : ℝ} (hc : c≠0) (θ m γ q : ℝ) :
    forwardKernel θ m c γ q =
      γ^2*(Real.exp (-c*q)-Real.cos (γ*q))+
        ((3*c-θ)/c)*γ^2*Real.sinh (c*q)-delta θ m c*kernelA c γ q+
        (θ-2*c)*γ*Real.sin (γ*q) := by
  have hh := Real.cosh_sub_sinh (c*q)
  have he : Real.exp (-c*q)=Real.exp (-(c*q)) := by congr 1; ring
  rw [he]
  dsimp [forwardKernel,kernelA,kernelB]
  rw [←hh]
  field_simp
  ring

theorem spreadU_pos {x : ℝ} (hx : 0<x) : 0<spreadU x := by
  have hcount : (Set.range (fun n : ℤ => (n:ℝ)*(2*Real.pi)/x)).Countable := countable_range _
  obtain ⟨lam,hlam,hnot⟩ := hcount.dense_compl ℝ |>.inter_open_nonempty
    (Ioo (1:ℝ) 2) isOpen_Ioo ⟨3/2,by norm_num⟩
  have hcos : Real.cos (lam*x)≠1 := by
    intro h
    obtain ⟨n,hn⟩ := (Real.cos_eq_one_iff _).mp h
    apply hnot
    refine ⟨n,?_⟩
    apply (div_eq_iff (ne_of_gt hx)).mpr
    linarith
  apply integral_pos (by norm_num) (by fun_prop)
    (fun l _ => mul_nonneg (sq_nonneg _) (by linarith [Real.cos_le_one (l*x)]))
  exact ⟨lam,⟨hlam.1.le,hlam.2.le⟩,mul_pos (sq_pos_of_pos (by linarith [hlam.1]))
    (sub_pos.mpr (lt_of_le_of_ne (Real.cos_le_one _) hcos))⟩

theorem continuous_spreadU : Continuous spreadU := by
  unfold spreadU
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f:=fun x lam : ℝ => lam^2*(1-Real.cos (lam*x))) (by fun_prop) 1 2

theorem spreadU_uniform_positive {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    ∃ η : ℝ,0<η ∧ ∀ x∈Icc a b,η≤spreadU x := by
  obtain ⟨x,hx,hmin⟩ := isCompact_Icc.exists_isMinOn ⟨a,⟨le_rfl,hab⟩⟩
    continuous_spreadU.continuousOn
  exact ⟨spreadU x,spreadU_pos (ha.trans_le hx.1),fun y hy => hmin hy⟩

/-- One integration by parts bounds the weighted oscillatory integral. -/
theorem abs_spreadV_le {x : ℝ} (hx : 0<x) : |spreadV x|≤9/x := by
  have hxn : x≠0 := ne_of_gt hx
  have hu (lam : ℝ) : HasDerivAt (fun y : ℝ => y^2) (2*lam) lam := by
    simpa using hasDerivAt_pow 2 lam
  have hv (lam : ℝ) : HasDerivAt (fun y : ℝ => Real.sin (y*x)/x) (Real.cos (lam*x)) lam := by
    simpa [mul_div_cancel_right₀ _ hxn] using
      (((hasDerivAt_id' lam).mul_const x).sin.div_const x)
  have hh := integral_mul_deriv_eq_deriv_mul (a:=(1:ℝ)) (b:=2)
    (fun lam _ => hu lam) (fun lam _ => hv lam)
    ((by fun_prop : Continuous (fun lam : ℝ => 2*lam)).intervalIntegrable _ _)
    ((by fun_prop : Continuous (fun lam : ℝ => Real.cos (lam*x))).intervalIntegrable _ _)
  change spreadV x = 2^2*(Real.sin (2*x)/x)-1^2*(Real.sin (1*x)/x)-
    ∫ lam in (1:ℝ)..2,(2*lam)*(Real.sin (lam*x)/x) at hh
  have hb (lam : ℝ) (hlam : lam∈uIoc (1:ℝ) 2) :
      ‖(2*lam)*(Real.sin (lam*x)/x)‖≤4/x := by
    rw [uIoc_of_le (by norm_num)] at hlam
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (by linarith [hlam.1] : 0≤2*lam),abs_div,abs_of_pos hx,
      ←mul_div_assoc]
    apply (div_le_div_iff_of_pos_right hx).mpr
    nlinarith [mul_le_mul_of_nonneg_left (Real.abs_sin_le_one (lam*x))
      (show 0≤2*lam by linarith [hlam.1]),hlam.2]
  have hi := norm_integral_le_of_norm_le_const hb
  norm_num only [Real.norm_eq_abs,show |(2:ℝ)-1|=1 by norm_num,mul_one] at hi
  rw [hh]
  calc
    _ ≤ |(2:ℝ)^2*(Real.sin (2*x)/x)-1^2*(Real.sin (1*x)/x)|+
        |∫ lam in (1:ℝ)..2,(2*lam)*(Real.sin (lam*x)/x)| := abs_sub _ _
    _ ≤ (4/x+1/x)+4/x := by
      apply add_le_add _ hi
      apply (abs_sub _ _).trans
      simp only [abs_mul,abs_div,abs_of_pos hx]
      norm_num
      rw [←mul_div_assoc,←add_div,←one_div x,←add_div]
      exact (div_le_div_iff_of_pos_right hx).mpr
        (by linarith [Real.abs_sin_le_one (2*x),Real.abs_sin_le_one x])
    _ = _ := by ring


/-- Uniform frequency-variable Lipschitz estimate on a bounded lag band. -/
theorem weighted_cos_lipschitz {x y q X : ℝ} (hx : x∈Icc (1:ℝ) 2)
    (hy : y∈Icc (1:ℝ) 2) (hq : 0≤q) (hX : q≤X) :
    |x^2*Real.cos (x*q)-y^2*Real.cos (y*q)|≤(4+4*X)*|x-y| := by
  have hs : |x^2-y^2|≤4*|x-y| := by
    rw [show x^2-y^2=(x-y)*(x+y) by ring,abs_mul,
      abs_of_nonneg (by linarith [hx.1,hy.1] : 0≤x+y)]
    nlinarith [abs_nonneg (x-y),hx.2,hy.2]
  have hsin := Real.abs_cos_sub_cos_le (x*q) (y*q)
  have he : |x*q-y*q|=|x-y| *q := by rw [←sub_mul,abs_mul,abs_of_nonneg hq]
  rw [he] at hsin
  have hy2 : |y^2|≤4 := by rw [abs_of_nonneg (sq_nonneg y)]; nlinarith [hy.1,hy.2]
  have he' : x^2*Real.cos (x*q)-y^2*Real.cos (y*q)=
      (x^2-y^2)*Real.cos (x*q)+y^2*(Real.cos (x*q)-Real.cos (y*q)) := by ring
  rw [he']
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_mul]
  have ha := mul_le_mul hs (Real.abs_cos_le_one (x*q)) (abs_nonneg _) (by positivity : 0≤4*|x-y|)
  have hb := mul_le_mul hy2 hsin (abs_nonneg _) (by norm_num : (0:ℝ)≤4)
  have hq' := mul_le_mul_of_nonneg_right hX (abs_nonneg (x-y))
  nlinarith only [ha,hb,hq']

theorem weighted_one_sub_cos_lipschitz {x y q X : ℝ} (hx : x∈Icc (1:ℝ) 2)
    (hy : y∈Icc (1:ℝ) 2) (hq : 0≤q) (hX : q≤X) :
    |x^2*(1-Real.cos (x*q))-y^2*(1-Real.cos (y*q))|≤(8+4*X)*|x-y| := by
  have hs : |x^2-y^2|≤4*|x-y| := by
    rw [show x^2-y^2=(x-y)*(x+y) by ring,abs_mul,
      abs_of_nonneg (by linarith [hx.1,hy.1] : 0≤x+y)]
    nlinarith [abs_nonneg (x-y),hx.2,hy.2]
  have hc := weighted_cos_lipschitz hx hy hq hX
  have he : x^2*(1-Real.cos (x*q))-y^2*(1-Real.cos (y*q))=
      (x^2-y^2)-(x^2*Real.cos (x*q)-y^2*Real.cos (y*q)) := by ring
  rw [he]
  exact (abs_sub _ _).trans (by nlinarith)

/-- One midpoint grid approximates both oscillatory averages at every lag
in the chosen compact interval. -/
theorem midpoint_UV_error {J : ℕ} (hJ : 0<J) {X q : ℝ} (hq : 0≤q) (hX : q≤X) :
    |spreadU q-midpointAverage J (fun lam => lam^2*(1-Real.cos (lam*q)))|≤(8+4*X)/(2*J) ∧
    |spreadV q-midpointAverage J (fun lam => lam^2*Real.cos (lam*q))|≤(8+4*X)/(2*J) := by
  constructor
  · exact midpoint_error hJ (by fun_prop) (by linarith)
      (fun x hx y hy => weighted_one_sub_cos_lipschitz hx hy hq hX)
  · have hh := midpoint_error hJ (by fun_prop) (show 0≤4+4*X by linarith)
      (fun x hx y hy => weighted_cos_lipschitz hx hy hq hX)
    apply hh.trans
    exact (div_le_div_iff_of_pos_right (by positivity : 0<(2:ℝ)*J)).mpr (by linarith)

end
end nesterov.Flow
