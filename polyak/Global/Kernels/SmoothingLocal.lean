import polyak.Global.Kernels.ScaledMoments
import polyak.Global.Kernels.Oscillation

/-! The actual local convolution and the uniform first-order Taylor error. -/
noncomputable section
namespace polyak.Global.Kernels
open MeasureTheory Set Function Complex
open scoped Topology

def cis (x:ℝ) : ℂ := Complex.exp ((x:ℂ)*Complex.I)

@[simp] theorem cis_norm (x:ℝ) : ‖cis x‖=1 := Complex.norm_exp_ofReal_mul_I x

@[simp] theorem cis_add (x y:ℝ) : cis (x+y)=cis x*cis y := by
  simp only [cis,Complex.ofReal_add,add_mul,Complex.exp_add]

@[simp] theorem cis_re (x:ℝ) : (cis x).re=Real.cos x := Complex.exp_ofReal_mul_I_re x

@[fun_prop] theorem continuous_cis : Continuous cis := by unfold cis;fun_prop

theorem cis_difference_bound (x y:ℝ) : ‖cis x-cis y‖≤|x-y| := by
  have he : cis x-cis y=cis y*(cis (x-y)-1) := by
    rw [mul_sub,mul_one,←cis_add]
    congr 2
    ring
  rw [he,norm_mul,cis_norm,one_mul]
  unfold cis
  rw [mul_comm ((x-y:ℝ):ℂ)]
  simpa only [Real.norm_eq_abs] using (Real.norm_exp_I_mul_ofReal_sub_one_le (x:=x-y))

theorem cis_integrable (μ:Measure ℝ) [IsFiniteMeasure μ] (g:ℝ→ℝ) (hg:Continuous g) :
    Integrable (fun x=>cis (g x)) μ := by
  apply (integrable_const (1:ℝ)).mono' ((continuous_cis.comp hg).aestronglyMeasurable)
  exact ae_of_all _ fun x=>le_of_eq (cis_norm (g x))

def localAverage (Φ:ℝ→ℝ) (n ε v:ℝ) : ℂ :=
  ∫t,cis (n*(v+t)-Φ (v+t))∂kernelMeasure ε

/-- An actual convolution estimate, with the exact scaled second moment. -/
theorem localAverage_taylor (Φ dΦ:ℝ→ℝ) (hΦ:Continuous Φ) {M2:ℝ}
    (hTaylor:∀v t,|Φ (v+t)-Φ v-dΦ v*t|≤M2*t^2/2) (n ε v:ℝ) :
    ‖localAverage Φ n ε v-
      cis (n*v-Φ v)*(kernelHat ε (n-dΦ v):ℂ)‖≤M2*mK*ε^2/2 := by
  let A : ℝ→ℝ := fun t=>n*(v+t)-Φ (v+t)
  let B : ℝ→ℝ := fun t=>n*v-Φ v+(n-dΦ v)*t
  have hA : Continuous A := by unfold A;fun_prop
  have hB : Continuous B := by unfold B;fun_prop
  have hbound : ∀t,‖cis (A t)-cis (B t)‖≤(M2/2)*t^2 := by
    intro t
    have hh := cis_difference_bound (A t) (B t)
    have he : A t-B t= -(Φ (v+t)-Φ v-dΦ v*t) := by dsimp [A,B];ring
    rw [he,abs_neg] at hh
    nlinarith [hTaylor v t]
  have hI := norm_integral_le_of_norm_le ((kernelMeasure_integrable_square ε).const_mul (M2/2))
    (ae_of_all _ hbound)
  rw [integral_sub (cis_integrable _ _ hA) (cis_integrable _ _ hB),integral_const_mul,
    kernelMeasure_second_moment] at hI
  have hIB : ∫t,cis (B t)∂kernelMeasure ε=
      cis (n*v-Φ v)*(kernelHat ε (n-dΦ v):ℂ) := by
    dsimp [B]
    simp_rw [cis_add]
    rw [integral_const_mul]
    congr 1
    exact kernel_characteristic ε (n-dΦ v)
  rw [hIB] at hI
  change ‖localAverage Φ n ε v-_‖≤_ at hI
  nlinarith [hI]

/-- The true source D_n controls the shifted Fourier argument. -/
theorem localAverage_constant (Φ dΦ:ℝ→ℝ) (hΦ:Continuous Φ) {M1 M2:ℝ}
    (hDerivative:∀v,|dΦ v|≤M1)
    (hTaylor:∀v t,|Φ (v+t)-Φ v-dΦ v*t|≤M2*t^2/2) (n ε v:ℝ) :
    ‖localAverage Φ n ε v-cis (n*v-Φ v)*(kernelHat ε n:ℂ)‖≤
      M2*mK*ε^2/2+oscillation ε M1 n := by
  have hfirst := localAverage_taylor Φ dΦ hΦ hTaylor n ε v
  have hsecond : ‖cis (n*v-Φ v)*(kernelHat ε (n-dΦ v):ℂ)-
      cis (n*v-Φ v)*(kernelHat ε n:ℂ)‖≤oscillation ε M1 n := by
    rw [←mul_sub,norm_mul,cis_norm,one_mul,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    apply le_oscillation
    simpa only [sub_sub_cancel_left,abs_neg] using hDerivative v
  have ht:=norm_add_le
    (localAverage Φ n ε v-cis (n*v-Φ v)*(kernelHat ε (n-dΦ v):ℂ))
    (cis (n*v-Φ v)*(kernelHat ε (n-dΦ v):ℂ)-cis (n*v-Φ v)*(kernelHat ε n:ℂ))
  rw [sub_add_sub_cancel] at ht
  exact ht.trans (add_le_add hfirst hsecond)

end polyak.Global.Kernels
