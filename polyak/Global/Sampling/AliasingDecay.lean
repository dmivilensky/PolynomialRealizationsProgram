import polyak.Global.Circle.Basic
import Mathlib.Analysis.PSeries

/-! Two genuine integrations by parts. Right derivatives at the finitely
many analytic junctions suffice, so no false global C2 hypothesis is used. -/
noncomputable section
namespace polyak.Global.Sampling
open MeasureTheory Set Complex

 theorem fourierCoeffOn_norm_bound (f : ℝ→ℂ) (n : ℤ) :
    ‖fourierCoeffOn Real.two_pi_pos f n‖≤
      (1/(2*Real.pi))*(∫x in (0:ℝ)..(2*Real.pi),‖f x‖) := by
  rw [fourierCoeffOn_eq_integral]
  simp only [sub_zero,norm_smul,Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr Real.two_pi_pos)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hh:=intervalIntegral.norm_integral_le_integral_norm (μ:=volume)
    (f:=fun x : ℝ=>fourier (-n) (x:AddCircle (2*Real.pi-0)) • f x) Real.two_pi_pos.le
  have he (x : ℝ) : ‖fourier (-n) (x:AddCircle (2*Real.pi-0)) • f x‖=‖f x‖ := by
    rw [norm_smul,fourier_apply,_root_.Circle.norm_coe,one_mul]
  simpa only [he] using hh

 theorem fourierCoeff_eq_On (h : C(Circle,ℂ)) (n : ℤ) :
    fourierCoeff h n=fourierCoeffOn Real.two_pi_pos (fun x : ℝ=>h (Circle.ofReal x)) n := by
  rw [fourierCoeff_eq_intervalIntegral _ _ 0,fourierCoeffOn_eq_integral]
  simp only [zero_add,sub_zero]
  congr 1
  apply intervalIntegral.integral_congr
  intro x _
  simp only [fourier_coe_apply,sub_zero]
  rfl

 theorem fourierCoeff_second_derivative (h : C(Circle,ℂ)) {g g' : ℝ→ℂ}
    (hg : ContinuousOn g (Icc (0:ℝ) (2*Real.pi)))
    (hgend : g (2*Real.pi)=g 0)
    (hd : ∀x∈Ioo (0:ℝ) (2*Real.pi),HasDerivWithinAt (fun x=>h (Circle.ofReal x)) (g x) (Ioi x) x)
    (hd' : ∀x∈Ioo (0:ℝ) (2*Real.pi),HasDerivWithinAt g (g' x) (Ioi x) x)
    (hi : IntervalIntegrable g' volume 0 (2*Real.pi)) {n : ℤ} (hn : n≠0) :
    fourierCoeff h n= -fourierCoeffOn Real.two_pi_pos g' n/(n:ℂ)^2 := by
  have hcont : Continuous (fun x : ℝ=>h (Circle.ofReal x)):=h.continuous.comp Circle.continuous_ofReal
  have hgc : ContinuousOn g (uIcc (0:ℝ) (2*Real.pi)):=by simpa only [uIcc_of_le Real.two_pi_pos.le] using hg
  have hper : h (Circle.ofReal (2*Real.pi))=h (Circle.ofReal 0) := by
    congr 1
    change ((2*Real.pi:ℝ):Circle)=(0:ℝ)
    simp
  have h1:=fourierCoeffOn_of_hasDeriv_right Real.two_pi_pos hn hcont.continuousOn
    (by simpa only [min_eq_left Real.two_pi_pos.le,max_eq_right Real.two_pi_pos.le] using hd) hgc.intervalIntegrable
  have h2:=fourierCoeffOn_of_hasDeriv_right Real.two_pi_pos hn hgc
    (by simpa only [min_eq_left Real.two_pi_pos.le,max_eq_right Real.two_pi_pos.le] using hd') hi
  rw [hper,sub_self,mul_zero,zero_sub] at h1
  rw [hgend,sub_self,mul_zero,zero_sub] at h2
  rw [fourierCoeff_eq_On,h1,h2]
  push_cast
  field_simp
  simp only [Complex.I_sq]
  ring

/-- The actual O(n^-2) bound needed by the aliasing lemma, with an explicit
finite constant from the integrable second right derivative. -/
theorem fourierCoeff_decay_of_piecewise_C2 (h : C(Circle,ℂ)) {g g' : ℝ→ℂ}
    (hg : ContinuousOn g (Icc (0:ℝ) (2*Real.pi)))
    (hgend : g (2*Real.pi)=g 0)
    (hd : ∀x∈Ioo (0:ℝ) (2*Real.pi),HasDerivWithinAt (fun x=>h (Circle.ofReal x)) (g x) (Ioi x) x)
    (hd' : ∀x∈Ioo (0:ℝ) (2*Real.pi),HasDerivWithinAt g (g' x) (Ioi x) x)
    (hi : IntervalIntegrable g' volume 0 (2*Real.pi)) :
    ∃C : ℝ,0≤C ∧ ∀n : ℤ,n≠0→‖fourierCoeff h n‖≤C/(n:ℝ)^2 := by
  let C:ℝ:=(1/(2*Real.pi))*(∫x in (0:ℝ)..(2*Real.pi),‖g' x‖)
  have hC : 0≤C:=mul_nonneg (by positivity)
    (intervalIntegral.integral_nonneg Real.two_pi_pos.le (fun _ _=>norm_nonneg _))
  refine ⟨C,hC,fun n hn=>?_⟩
  rw [fourierCoeff_second_derivative h hg hgend hd hd' hi hn,norm_div,norm_neg,norm_pow,Complex.norm_intCast,sq_abs]
  exact div_le_div_of_nonneg_right (fourierCoeffOn_norm_bound g' n) (sq_nonneg _)

end polyak.Global.Sampling
