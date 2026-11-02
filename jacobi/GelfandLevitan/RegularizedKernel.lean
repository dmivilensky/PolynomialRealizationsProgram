import jacobi.Reference.ZeroGreenSeries
import jacobi.Reference.NormingAsymptotic
import jacobi.Reference.SpectralSlopeBounds

/-!
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
The regularization here subtracts the actual reference Green series
from the previously constructed original GL kernel. The exact series
identity and its term derivatives use the original norming products
and original solutions, before taking any derivative of an infinite sum.
Use: regularized_kernel_series identifies its sum with F-flat, and regularizedTerm_hasDerivAt supplies the genuine individual spatial derivatives.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The original regularized GL summand, with its actual total spectral displacement.
Use: regularized_kernel_series identifies its sum with F-flat, and regularizedTerm_hasDerivAt supplies the genuine individual spatial derivatives.
Article: jacobi, Theorem 2.1.
-/
def regularizedTerm (a : ℝ) (ha : -1<a) (k : ℕ) (t s : ℝ) : ℝ :=
  kernelTerm a ha k t s-displacementMass a ha*zeroGreenTerm a k t s

/-- The actual regularization of the original, already constructed GL kernel.
Use: its regularized series will be differentiated to provide the continuous part of dot F in Differentiability of K.
Article: jacobi, Theorem 2.1.
-/
def regularizedKernel (a : ℝ) (ha : -1<a) (t s : ℝ) : ℝ :=
  kernel a ha t s-displacementMass a ha*zeroGreenKernel a t s

/-- The actual F-flat series is absolutely convergent everywhere on the closed physical half square.
Use: regularized_kernel_series identifies its sum and later termwise differentiation starts from this proved convergent series.
Article: jacobi, Theorem 2.1.
Proof: the original F and Green series are absolutely summable; multiplication by the fixed actual displacement sum and subtraction preserve absolute summability. -/
theorem regularized_absolute_summable {a : ℝ} (ha : -1<a) {t s : ℝ}
    (ht : t∈Icc (0:ℝ) (1/2)) (hs : s∈Icc (0:ℝ) (1/2)) :
    Summable (fun k : ℕ => |regularizedTerm a ha k t s|) := by
  have hF : Summable (fun k => kernelTerm a ha k t s) :=
    summable_norm_iff.mp (by simpa only [Real.norm_eq_abs] using kernel_absolute_summable a ha ht hs)
  have hG : Summable (fun k => zeroGreenTerm a k t s) :=
    summable_norm_iff.mp (by simpa only [Real.norm_eq_abs] using zeroGreen_absolute_summable ha ht hs)
  simpa only [Real.norm_eq_abs,regularizedTerm] using (hF.sub (hG.mul_left (displacementMass a ha))).norm

/-- The sum of the genuine regularized terms is exactly the regularization of the original GL kernel.
Use: identifies the eventual derivative-series theorem with the actual F-flat used in Differentiability of K, rather than a separately postulated kernel.
Article: jacobi, Theorem 2.1.
Proof: subtract the two independently proved absolutely convergent original series. -/
theorem regularized_kernel_series {a : ℝ} (ha : -1<a) {t s : ℝ}
    (ht : t∈Icc (0:ℝ) (1/2)) (hs : s∈Icc (0:ℝ) (1/2)) :
    HasSum (fun k : ℕ => regularizedTerm a ha k t s) (regularizedKernel a ha t s) := by
  have hF : Summable (fun k => kernelTerm a ha k t s) :=
    summable_norm_iff.mp (by simpa only [Real.norm_eq_abs] using kernel_absolute_summable a ha ht hs)
  have hG : Summable (fun k => zeroGreenTerm a k t s) :=
    summable_norm_iff.mp (by simpa only [Real.norm_eq_abs] using zeroGreen_absolute_summable ha ht hs)
  exact hF.hasSum.sub (hG.hasSum.mul_left (displacementMass a ha))

/-- The genuine regularized kernel is continuous on the entire closed physical half square.
Use: supplies the base continuity needed for the regularized derivative series and subsequent GL differentiation.
Article: jacobi, Theorem 2.1.
Proof: subtract the fixed multiple of the independently proved continuous actual Green series from the original continuous F. -/
theorem regularizedKernel_continuousOn {a : ℝ} (ha : -1<a) :
    ContinuousOn (fun p : ℝ × ℝ => regularizedKernel a ha p.1 p.2)
      (Icc (0:ℝ) (1/2)×ˢIcc (0:ℝ) (1/2)) :=
  (kernel_continuousOn a ha).sub ((zeroGreenKernel_continuousOn ha).const_mul _)

/-- The actual regularized kernel is symmetric in its original physical coordinates.
Use: its second-coordinate derivative follows from the proved first-coordinate derivative after interchanging the coordinates.
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
Proof: the original F is symmetric, and every actual Green summand is symmetric. -/
theorem regularizedKernel_symmetric (a : ℝ) (ha : -1<a) (t s : ℝ) :
    regularizedKernel a ha t s=regularizedKernel a ha s t := by
  have hG : zeroGreenKernel a t s=zeroGreenKernel a s t :=
    tsum_congr (fun k => by unfold zeroGreenTerm; ring)
  simp only [regularizedKernel,kernel_symmetric a ha t s,hG]

/-- The genuine real selected solution has its actual spatial slope as derivative.
Use: regularizedTerm_hasDerivAt differentiates the original spectral tensors without introducing any derivative certificate as a hypothesis.
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
Proof: compose the already proved genuine complex spatial derivative with the real-part continuous linear map. -/
theorem realSolution_hasDerivAt (a E : ℝ) {t : ℝ} (ht : t∈Ioo (0:ℝ) 1) :
    HasDerivAt (realSolution a E) (realSlope a E t) t := by
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (solution_hasDerivAt a (E:ℂ) ht)

/-- The literal derivative of a regularized original summand in its first coordinate.
Use: its summable uniform bound permits actual termwise differentiation of F-flat; the definition retains the same reference norm and displacement as regularizedTerm.
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
-/
def regularizedSlopeTerm (a : ℝ) (ha : -1<a) (k : ℕ) (t s : ℝ) : ℝ :=
  (normingRatio a ha k*realSlope a (jacobi.Bessel.sigma a ha k) t*
      realSolution a (jacobi.Bessel.sigma a ha k) s-
    realSlope a (eigenvalue a k) t*realSolution a (eigenvalue a k) s)/norming a k-
  displacementMass a ha*(realSlope a (eigenvalue a k) t*realSolution a (eigenvalue a k) s/
    (norming a k*(jacobi.Bessel.phaseGrid a k)^2))

/-- Each regularized original summand has exactly its displayed genuine slope derivative.
Use: the regularized uniform derivative theorem applies this to the original terms whose sum has already been identified with F-flat.
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
Proof: differentiate the two actual spatial solutions using realSolution_hasDerivAt and apply the community constant product, quotient and subtraction rules. -/
theorem regularizedTerm_hasDerivAt (a : ℝ) (ha : -1<a) (k : ℕ) (s : ℝ)
    {t : ℝ} (ht : t∈Ioo (0:ℝ) 1) :
    HasDerivAt (fun x => regularizedTerm a ha k x s) (regularizedSlopeTerm a ha k t s) t := by
  have hsig := realSolution_hasDerivAt a (jacobi.Bessel.sigma a ha k) ht
  have htau := realSolution_hasDerivAt a (eigenvalue a k) ht
  exact ((((hsig.const_mul _).mul_const _).sub (htau.mul_const _)).div_const _).sub
    (((htau.mul_const _).div_const _).const_mul _)

/-- The genuine slope numerator splits into a refined norming error and an actual spectral tensor difference.
Use: regularizedSlopeTerm_tail_bound gains the summable log(k)/k^2 bound after canceling the true reference norm scale.
Article: jacobi, Theorem 2.1.
Proof: expand the actual regularized numerator and collect the two spectral tensors, retaining the diagonal Green subtraction exactly. -/
theorem regularizedSlopeTerm_decomposition (a : ℝ) (ha : -1<a) (k : ℕ) (t s : ℝ) :
    regularizedSlopeTerm a ha k t s=
    ((normingRatio a ha k-1-displacementMass a ha/(jacobi.Bessel.phaseGrid a k)^2)*
      realSlope a (jacobi.Bessel.sigma a ha k) t*realSolution a (jacobi.Bessel.sigma a ha k) s+
    (1+displacementMass a ha/(jacobi.Bessel.phaseGrid a k)^2)*
      ((realSlope a (jacobi.Bessel.sigma a ha k) t-realSlope a (eigenvalue a k) t)*
          realSolution a (jacobi.Bessel.sigma a ha k) s+
        realSlope a (eigenvalue a k) t*
          (realSolution a (jacobi.Bessel.sigma a ha k) s-realSolution a (eigenvalue a k) s)))/
    norming a k := by
  unfold regularizedSlopeTerm
  ring

end
end jacobi.GelfandLevitan
