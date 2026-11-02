import jacobi.Analytic.RealPrefixInverse
import jacobi.Analytic.ComplexifyInverse
import Mathlib.Analysis.Analytic.Constructions

/-!
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
The genuine complex GL operator at every real disk order is the
complexification of the already inverted original real operator.
Its invertibility is proved, rather than assumed for analytic inversion.
Use: identifies the complex GL operator at real order with the genuine real integral operator on every continuous input.
-/
namespace jacobi.Analytic
noncomputable section
open Set Metric jacobi.Reference jacobi.GelfandLevitan
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local irreducible] OrderDisk.kernel jacobi.GelfandLevitan.kernel

/-- Complex inclusion preserves the literal physical prefix product of two real continuous kernels.
Use: identifies the complex GL operator at real order with the genuine real integral operator on every continuous input.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: evaluate the proved physical prefix formulas; real inclusion preserves the actual integrand product and commutes with its Bochner interval integral. -/
theorem prefixProduct_ofReal (K F : C(KernelSquare,ℝ)) :
    prefixProduct (continuousOfReal K) (continuousOfReal F)=continuousOfReal (prefixProduct K F) := by
  ext p
  rcases p with ⟨t,s⟩
  rw [prefixProduct_apply]
  change (∫ r in (0:ℝ)..(t:ℝ),(K (t,halfParameterClamp r):ℂ)*(F (halfParameterClamp r,s):ℂ))=
    (prefixProduct K F (t,s):ℂ)
  rw [prefixProduct_apply]
  simpa only [_root_.Complex.ofReal_mul] using intervalIntegral.integral_ofReal
    (f := fun r => K (t,halfParameterClamp r)*F (halfParameterClamp r,s))

/-- The genuine analytic continuous-kernel map at any real disk order is exactly the complex inclusion of the original real kernel.
Use: the base complex GL inverse acts on the same source kernel and original real equations.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: evaluate the actual kernel map on the disk and apply the proved equality of the original real and continued infinite kernel series. -/
theorem OrderDisk.kernelMap_real {a0 b : ℝ} (D : OrderDisk a0) (hb : -1<b)
    (hbd : ‖(b:ℂ)-(a0:ℂ)‖≤D.radius) :
    D.kernelMap (b:ℂ)=continuousOfReal (realKernelMap b hb) := by
  ext p
  rw [D.kernelMap_apply hbd p]
  exact D.kernel_real hb hbd p.1.property p.2.property

/-- The actual continued GL operator at every real disk order extends the original real GL operator on every continuous kernel input.
Use: real invertibility gives genuine complex base invertibility by splitting actual inputs into real and imaginary parts.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: use the exact real identification of the infinite kernel and the proved complex-inclusion identity for the physical prefix integral; real inclusion also preserves the unchanged identity term. -/
theorem OrderDisk.GLoperator_real {a0 b : ℝ} (D : OrderDisk a0) (hb : -1<b)
    (hbd : ‖(b:ℂ)-(a0:ℂ)‖≤D.radius) (K : C(KernelSquare,ℝ)) :
    D.GLoperator (b:ℂ) (continuousOfReal K)=continuousOfReal (realGLoperator b hb K) := by
  change continuousOfReal K+prefixProduct (continuousOfReal K) (D.kernelMap (b:ℂ))=
    continuousOfReal (K+prefixProduct K (realKernelMap b hb))
  rw [D.kernelMap_real hb hbd,prefixProduct_ofReal]
  ext p
  simp only [continuousOfReal,ContinuousMap.coe_mk,ContinuousMap.add_apply,_root_.Complex.ofReal_add]

/-- The original complex GL operator at every real order in the common disk is genuinely invertible on continuous kernels.
Use: supplies the actual base unit for local holomorphic GL inversion, without an unproved invertibility or coercivity certificate.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the same real physical GL operator is already proved invertible for arbitrary continuous forcing. The complex operator extends it exactly, so the proved real-and-imaginary-part construction gives its complex inverse. -/
theorem OrderDisk.GLoperator_real_isUnit {a0 b : ℝ} (D : OrderDisk a0) (hb : -1<b)
    (hbd : ‖(b:ℂ)-(a0:ℂ)‖≤D.radius) : IsUnit (D.GLoperator (b:ℂ)) :=
  isUnit_complex_of_real (realGLoperator_isUnit b hb) (D.GLoperator_real hb hbd)

end
end jacobi.Analytic
