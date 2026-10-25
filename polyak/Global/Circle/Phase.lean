import polyak.Global.Circle.Kernel
import polyak.Global.Kernels.SmoothingLocal

/-! True periodic phase moments on the actual circle. -/
noncomputable section
namespace polyak.Global.Circle
open MeasureTheory Set Function Complex
open scoped Topology

def phaseLift (Φ:ℝ→ℝ) (hp:Periodic Φ (2*Real.pi)) : Circle→ℝ := hp.lift

theorem phaseLift_continuous {Φ:ℝ→ℝ} (hp:Periodic Φ (2*Real.pi)) (hc:Continuous Φ) :
    Continuous (phaseLift Φ hp) := hc.quotient_lift _

@[simp] theorem phaseLift_ofReal {Φ:ℝ→ℝ} (hp:Periodic Φ (2*Real.pi)) (v:ℝ) :
    phaseLift Φ hp (ofReal v)=Φ v := hp.lift_coe v

def wave (Φ:ℝ→ℝ) (hp:Periodic Φ (2*Real.pi)) (n:ℤ) (x:Circle) : ℂ :=
  fourier n x*Kernels.cis (-phaseLift Φ hp x)

theorem wave_continuous {Φ:ℝ→ℝ} (hp:Periodic Φ (2*Real.pi)) (hc:Continuous Φ) (n:ℤ) :
    Continuous (wave Φ hp n) :=
  (fourier n).continuous.mul (Kernels.continuous_cis.comp (phaseLift_continuous hp hc).neg)

@[simp] theorem wave_norm {Φ:ℝ→ℝ} (hp:Periodic Φ (2*Real.pi)) (n:ℤ) (x:Circle) :
    ‖wave Φ hp n x‖=1 := by
  simp only [wave,norm_mul,Kernels.cis_norm,mul_one]
  exact (AddCircle.toCircle (n•x)).norm_coe

@[simp] theorem wave_ofReal {Φ:ℝ→ℝ} (hp:Periodic Φ (2*Real.pi)) (n:ℤ) (v:ℝ) :
    wave Φ hp n (ofReal v)=Kernels.cis ((n:ℝ)*v-Φ v) := by
  rw [wave,fourier_ofReal,phaseLift_ofReal]
  change Kernels.cis ((n:ℝ)*v)*Kernels.cis (-Φ v)=_
  rw [←Kernels.cis_add]
  rfl

theorem wave_integrable {Φ:ℝ→ℝ} (hp:Periodic Φ (2*Real.pi)) (hc:Continuous Φ)
    (n:ℤ) (μ:Measure Circle) [IsFiniteMeasure μ] : Integrable (wave Φ hp n) μ := by
  apply (integrable_const (1:ℝ)).mono' (wave_continuous hp hc n).aestronglyMeasurable
  exact ae_of_all _ fun x=>by rw [wave_norm]

def phaseMoment (Φ:ℝ→ℝ) (hp:Periodic Φ (2*Real.pi)) (μ:Measure Circle) (n:ℤ) : ℂ :=
  ∫x,wave Φ hp n x∂μ

def phaseConstraint (Φ:ℝ→ℝ) (hp:Periodic Φ (2*Real.pi)) (μ:Measure Circle) (n:ℤ) : ℝ :=
  (phaseMoment Φ hp μ 0-phaseMoment Φ hp μ n).re

def phaseMinimizer (Φ:ℝ→ℝ) (hp:Periodic Φ (2*Real.pi)) (μ:Measure Circle) : ℝ :=
  (phaseMoment Φ hp μ 0).re

def averagedWave (Φ:ℝ→ℝ) (hp:Periodic Φ (2*Real.pi)) (n:ℤ) (ε:ℝ) (x:Circle) : ℂ :=
  ∫t,wave Φ hp n (x+ofReal t)∂Kernels.kernelMeasure ε

theorem averagedWave_ofReal {Φ:ℝ→ℝ} (hp:Periodic Φ (2*Real.pi)) (n:ℤ) (ε v:ℝ) :
    averagedWave Φ hp n ε (ofReal v)=Kernels.localAverage Φ n ε v := by
  simp only [averagedWave,←ofReal_add,wave_ofReal,Kernels.localAverage]

end polyak.Global.Circle
