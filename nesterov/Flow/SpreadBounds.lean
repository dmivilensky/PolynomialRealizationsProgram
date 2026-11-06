import nesterov.Flow.Kernel
import nesterov.Flow.SpreadAnalysis
import nesterov.Flow.SmallLag

/-!
Article: Lemma `lem:spread`, large-lag estimates independent of quadrature size.
Use: isolate the one oscillatory moment that is controlled by the spread.
-/
namespace nesterov.Flow
noncomputable section
open Finset
variable {J : Type*} [Fintype J]

def Spectrum.average (ν : Spectrum J) (f : ℝ→ℝ) : ℝ := ∑ j,ν.weight j*f (ν.frequency j)

theorem Spectrum.average_const (ν : Spectrum J) (C : ℝ) : ν.average (fun _=>C)=C := by
  simp [average,←sum_mul,ν.weight_sum]

theorem Spectrum.average_le (ν : Spectrum J) {f : ℝ→ℝ} {C : ℝ}
    (h : ∀ j,f (ν.frequency j)≤C) : ν.average f≤C := by
  rw [←ν.average_const C]
  exact sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (h j) (ν.weight_nonneg j))

theorem Spectrum.le_average (ν : Spectrum J) {f : ℝ→ℝ} {C : ℝ}
    (h : ∀ j,C≤f (ν.frequency j)) : C≤ν.average f := by
  rw [←ν.average_const C]
  exact sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (h j) (ν.weight_nonneg j))

def hyperbolicBuffer (a c q : ℝ) : ℝ := Real.exp (-c*q)+a*Real.sinh (c*q)
def bufferFloor (a : ℝ) : ℝ := min (Real.exp (-1)) (a*Real.sinh 1)

theorem bufferFloor_pos {a : ℝ} (ha : 0<a) : 0<bufferFloor a := by
  exact lt_min (Real.exp_pos _) (mul_pos ha (Real.sinh_pos_iff.mpr (by norm_num)))

theorem bufferFloor_le {a c q : ℝ} (ha : 0≤a) (hcq : 0≤c*q) :
    bufferFloor a≤hyperbolicBuffer a c q := by
  have hsin := Real.sinh_nonneg_iff.mpr hcq
  by_cases hh : c*q≤1
  · have he : Real.exp (-1)≤Real.exp (-c*q) := Real.exp_le_exp.mpr (by linarith)
    exact (min_le_left _ _).trans (by dsimp [hyperbolicBuffer]; nlinarith [mul_nonneg ha hsin])
  · have hs : Real.sinh 1≤Real.sinh (c*q) := Real.sinh_le_sinh.mpr (by linarith)
    exact (min_le_right _ _).trans (by dsimp [hyperbolicBuffer]; nlinarith [Real.exp_pos (-c*q)])

theorem buffer_sinh_le {a c q : ℝ} :
    a*Real.sinh (c*q)≤hyperbolicBuffer a c q := by
  dsimp [hyperbolicBuffer]
  linarith [Real.exp_pos (-c*q)]

theorem cosh_le_one_add_sinh {x : ℝ} (hx : 0≤x) : Real.cosh x≤1+Real.sinh x := by
  have hh := Real.cosh_sub_sinh x
  have he : Real.exp (-x)≤1 := by simpa using Real.exp_le_exp.mpr (neg_nonpos.mpr hx)
  linarith

theorem Spectrum.average_forward_decomposition (ν : Spectrum J) {c : ℝ} (hc : c≠0)
    (θ m q : ℝ) :
    ν.average (fun γ=>forwardKernel θ m c γ q)=
      hyperbolicBuffer ((3*c-θ)/c) c q*ν.average (fun γ=>γ^2)-
      ν.average (fun γ=>γ^2*Real.cos (γ*q))-
      delta θ m c*ν.average (fun γ=>kernelA c γ q)+
      (θ-2*c)*ν.average (fun γ=>γ*Real.sin (γ*q)) := by
  simp only [average,mul_sum,←sum_sub_distrib,←sum_add_distrib]
  apply sum_congr rfl
  intro j _
  rw [forwardKernel_decomposition hc]
  dsimp [hyperbolicBuffer]
  ring

/-- Once the oscillatory moment is suppressed, one scale bound controls every
large lag, uniformly in the number of frequency atoms. -/
theorem Spectrum.forward_long_lower (ν : Spectrum J) {θ m c γ₀ q d : ℝ}
    (hc : 0<c) (hq : 0≤q) (hg0 : 0≤γ₀)
    (hb : 0≤θ-2*c) (hbc : θ-2*c≤c) (ha : 0<(3*c-θ)/c)
    (hd : 0≤delta θ m c) (hdp : 0<d)
    (hfreq : ∀ j,γ₀≤ν.frequency j ∧ ν.frequency j≤2*γ₀)
    (hfloor : d≤hyperbolicBuffer ((3*c-θ)/c) c q)
    (hosc : ν.average (fun γ=>γ^2*Real.cos (γ*q))≤
      hyperbolicBuffer ((3*c-θ)/c) c q*ν.average (fun γ=>γ^2)/2)
    (hscale : (2*delta θ m c+2*c*γ₀)/d+delta θ m c/((3*c-θ)/c)≤γ₀^2/4) :
    (γ₀^2/4)*hyperbolicBuffer ((3*c-θ)/c) c q≤
      ν.average (fun γ=>forwardKernel θ m c γ q) := by
  let D := hyperbolicBuffer ((3*c-θ)/c) c q
  have hD : 0≤D := (hdp.trans_le hfloor).le
  have hs : 0≤Real.sinh (c*q) := Real.sinh_nonneg_iff.mpr (mul_nonneg hc.le hq)
  have hA : ν.average (fun γ=>kernelA c γ q)≤2+Real.sinh (c*q) := by
    apply ν.average_le
    intro j
    dsimp [kernelA]
    linarith [Real.neg_one_le_cos (ν.frequency j*q),cosh_le_one_add_sinh (mul_nonneg hc.le hq)]
  have hsin : -2*γ₀≤ν.average (fun γ=>γ*Real.sin (γ*q)) := by
    apply ν.le_average
    intro j
    have hf := hfreq j
    have hgp : 0≤ν.frequency j := hg0.trans hf.1
    nlinarith [mul_le_mul_of_nonneg_left (Real.neg_one_le_sin (ν.frequency j*q)) hgp]
  have hmom : γ₀^2≤ν.average (fun γ=>γ^2) :=
    ν.le_average (fun j=>pow_le_pow_left₀ hg0 (hfreq j).1 2)
  have hW := ν.average_forward_decomposition hc.ne' θ m q
  have hc1 := mul_le_mul_of_nonneg_left hA hd
  have hc2 := mul_le_mul_of_nonneg_left hsin hb
  have hc3 := mul_le_mul_of_nonneg_left hmom hD
  have hrough : D*γ₀^2/2-delta θ m c*(2+Real.sinh (c*q))-2*c*γ₀≤
      ν.average (fun γ=>forwardKernel θ m c γ q) := by
    have hb' := mul_le_mul_of_nonneg_right hbc (mul_nonneg (by norm_num : (0:ℝ)≤2) hg0)
    dsimp only [D] at *
    linarith
  have hDs := buffer_sinh_le (a:=(3*c-θ)/c) (c:=c) (q:=q)
  have h₁ : 2*delta θ m c+2*c*γ₀≤((2*delta θ m c+2*c*γ₀)/d)*D := by
    have hh := mul_le_mul_of_nonneg_left hfloor
      (div_nonneg (by positivity : 0≤2*delta θ m c+2*c*γ₀) hdp.le)
    rw [div_mul_cancel₀ _ hdp.ne'] at hh
    exact hh
  have h₂ : delta θ m c*Real.sinh (c*q)≤(delta θ m c/((3*c-θ)/c))*D := by
    have hh := mul_le_mul_of_nonneg_left hDs (div_nonneg hd ha.le)
    have he : delta θ m c/((3*c-θ)/c)*(((3*c-θ)/c)*Real.sinh (c*q))=
        delta θ m c*Real.sinh (c*q) := by
      rw [←mul_assoc,div_mul_cancel₀ _ ha.ne']
    rw [he] at hh
    exact hh
  have h₃ := mul_le_mul_of_nonneg_right hscale hD
  nlinarith only [hrough,h₁,h₂,h₃]


/-- The same buffer controls the total nonnegative kernel used as margin. -/
theorem Spectrum.average_kernel_upper (ν : Spectrum J) {c γ₀ q a d : ℝ}
    (hc : 0<c) (hq : 0≤q) (hg0 : 0≤γ₀) (ha : 0<a) (hd : 0<d)
    (hfreq : ∀ j,ν.frequency j≤2*γ₀)
    (hfloor : d≤hyperbolicBuffer a c q) :
    ν.average (fun γ=>kernelA c γ q+kernelB c γ q)≤
      (3/d+(1+2*γ₀/c)/a)*hyperbolicBuffer a c q := by
  have hs : 0≤Real.sinh (c*q) := Real.sinh_nonneg_iff.mpr (mul_nonneg hc.le hq)
  have hlocal : ν.average (fun γ=>kernelA c γ q+kernelB c γ q)≤
      3+(1+2*γ₀/c)*Real.sinh (c*q) := by
    apply ν.average_le
    intro j
    have hh := mul_le_mul_of_nonneg_right (hfreq j) (div_nonneg hs hc.le)
    have hh' : ν.frequency j*Real.sinh (c*q)/c≤(2*γ₀/c)*Real.sinh (c*q) := by
      convert hh using 1 <;> ring
    dsimp [kernelA,kernelB]
    nlinarith [cosh_le_one_add_sinh (mul_nonneg hc.le hq),
      Real.neg_one_le_cos (ν.frequency j*q),Real.neg_one_le_sin (ν.frequency j*q),hh']
  have h₁ := mul_le_mul_of_nonneg_left hfloor (by positivity : 0≤3/d)
  rw [div_mul_cancel₀ _ hd.ne'] at h₁
  have h₂ := mul_le_mul_of_nonneg_left (buffer_sinh_le (a:=a) (c:=c) (q:=q))
    (by positivity : 0≤(1+2*γ₀/c)/a)
  have he : (1+2*γ₀/c)/a*(a*Real.sinh (c*q))=(1+2*γ₀/c)*Real.sinh (c*q) := by
    rw [←mul_assoc,div_mul_cancel₀ _ ha.ne']
  rw [he] at h₂
  nlinarith only [hlocal,h₁,h₂]

theorem Spectrum.forward_medium_lower (ν : Spectrum J) {θ m c γ₀ q u : ℝ}
    (hc : 0<c) (hq : 0≤q) (hg0 : 0≤γ₀)
    (hb : 0≤θ-2*c) (hbc : θ-2*c≤c) (ha : 0≤(3*c-θ)/c)
    (hd : 0≤delta θ m c) (hcq : c*q≤1)
    (hfreq : ∀ j,ν.frequency j≤2*γ₀)
    (hU : γ₀^2*u≤ν.average (fun γ=>γ^2*(1-Real.cos (γ*q)))) :
    γ₀^2*u-4*c*γ₀^2*q-3*delta θ m c-2*c*γ₀≤
      ν.average (fun γ=>forwardKernel θ m c γ q) := by
  have hA : ν.average (fun γ=>kernelA c γ q)≤3 := by
    apply ν.average_le
    intro j
    have hh := cosh_sub_one_le_sq (mul_nonneg hc.le hq) hcq
    dsimp [kernelA]
    nlinarith [Real.neg_one_le_cos (ν.frequency j*q),pow_le_pow_left₀ (mul_nonneg hc.le hq) hcq 2]
  have hsin : -2*γ₀≤ν.average (fun γ=>γ*Real.sin (γ*q)) := by
    apply ν.le_average
    intro j
    have hj := ν.frequency_nonneg j
    nlinarith [mul_le_mul_of_nonneg_left (Real.neg_one_le_sin (ν.frequency j*q)) hj,hfreq j]
  have hmom : ν.average (fun γ=>γ^2)≤4*γ₀^2 := by
    apply ν.average_le
    intro j
    have hj := ν.frequency_nonneg j
    nlinarith [pow_le_pow_left₀ hj (hfreq j) 2]
  have hmom0 : 0≤ν.average (fun γ=>γ^2) := ν.le_average (fun _=>sq_nonneg _)
  have hsin0 : 0≤Real.sinh (c*q) := Real.sinh_nonneg_iff.mpr (mul_nonneg hc.le hq)
  have he : 1-c*q≤Real.exp (-c*q) := by
    have hh := Real.add_one_le_exp (-c*q)
    linarith
  have hsplit : ν.average (fun γ=>γ^2*(1-Real.cos (γ*q)))=
      ν.average (fun γ=>γ^2)-ν.average (fun γ=>γ^2*Real.cos (γ*q)) := by
    simp only [average,mul_sub,mul_one,sum_sub_distrib]
  rw [hsplit] at hU
  rw [ν.average_forward_decomposition hc.ne']
  have hbuf : 1-c*q≤hyperbolicBuffer ((3*c-θ)/c) c q := by
    dsimp [hyperbolicBuffer]
    nlinarith [mul_nonneg ha hsin0]
  have h₁ := mul_le_mul_of_nonneg_right hbuf hmom0
  have h₂ := mul_le_mul_of_nonneg_left hmom (mul_nonneg hc.le hq)
  have h₃ := mul_le_mul_of_nonneg_left hA hd
  have h₄ := mul_le_mul_of_nonneg_left hsin hb
  have h₅ := mul_le_mul_of_nonneg_right hbc (by positivity : 0≤2*γ₀)
  nlinarith only [hU,h₁,h₂,h₃,h₄,h₅]


theorem Spectrum.average_kernel_medium_upper (ν : Spectrum J) {c γ₀ q : ℝ}
    (hc : 0<c) (hq : 0≤q) (_hg0 : 0≤γ₀) (hcq : c*q≤1)
    (hfreq : ∀ j,ν.frequency j≤2*γ₀) :
    ν.average (fun γ=>kernelA c γ q+kernelB c γ q)≤4+4*γ₀*q := by
  have hcosh := cosh_sub_one_le_sq (mul_nonneg hc.le hq) hcq
  have hsinh := sinh_sub_self_le_cube (mul_nonneg hc.le hq) hcq
  have ht : (c*q)^3≤c*q := by
    have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg hc.le hq) hcq 2)
      (mul_nonneg hc.le hq)
    nlinarith only [hh]
  have hs : Real.sinh (c*q)≤2*c*q := by linarith [mul_nonneg hc.le hq]
  apply ν.average_le
  intro j
  have hγ := ν.frequency_nonneg j
  have hm := mul_le_mul_of_nonneg_left hs (div_nonneg hγ hc.le)
  have he : ν.frequency j/c*(2*c*q)=2*ν.frequency j*q := by field_simp
  rw [he] at hm
  have hnorm := mul_le_mul_of_nonneg_right (hfreq j) hq
  dsimp [kernelA,kernelB]
  have hγsin : ν.frequency j*Real.sinh (c*q)/c≤2*ν.frequency j*q := by
    convert hm using 1
    ring
  nlinarith [Real.neg_one_le_cos (ν.frequency j*q),Real.neg_one_le_sin (ν.frequency j*q),
    pow_le_pow_left₀ (mul_nonneg hc.le hq) hcq 2]


theorem Spectrum.backward_margin (ν : Spectrum J) {θ m c γ₀ q ε : ℝ}
    (hc : 0<c) (hq : 0≤q) (hg0 : 0≤γ₀) (hb : 0≤θ-2*c)
    (hε1 : ε≤1) (hεb : ε≤(θ-2*c)*γ₀)
    (hδ : delta θ m c+1≤γ₀^2) (hfreq : ∀ j,γ₀≤ν.frequency j) :
    ε*ν.average (fun γ=>kernelA c γ q+kernelB c γ q)≤
      ν.average (fun γ=>backwardKernel θ m c γ q) := by
  unfold average
  rw [mul_sum]
  apply sum_le_sum
  intro j _
  have hγ : 0≤ν.frequency j := ν.frequency_nonneg j
  have hcoef : ε≤ν.frequency j^2-delta θ m c := by
    have hh := pow_le_pow_left₀ hg0 (hfreq j) 2
    linarith
  have hb' : ε≤(θ-2*c)*ν.frequency j := hεb.trans (mul_le_mul_of_nonneg_left (hfreq j) hb)
  have hA := mul_le_mul_of_nonneg_right hcoef (kernelA_nonneg c (ν.frequency j) q)
  have hB := mul_le_mul_of_nonneg_right hb' (kernelB_nonneg hc hγ hq)
  have hh : ε*(kernelA c (ν.frequency j) q+kernelB c (ν.frequency j) q)≤
      backwardKernel θ m c (ν.frequency j) q := by dsimp [backwardKernel]; nlinarith only [hA,hB]
  have hw := mul_le_mul_of_nonneg_left hh (ν.weight_nonneg j)
  nlinarith only [hw]

end
end nesterov.Flow
