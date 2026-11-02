import jacobi.Reference.ZeroGreenWronskian
import jacobi.Reference.ZeroGreenRows
import jacobi.Reference.RealSpectralDerivatives
import jacobi.Reference.NegativeQuotient

/-!
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
The selected-solution Green factor is defined using the original
solutions and the independently proved actual Wronskian. Its full
spatial row is continuous despite the singular right-end behavior of
the unreflected selected solution. The genuine reference Green
identity supplies the coefficients for its spectral identification.
Use: zeroGreenFactor uses precisely the independently proved selected-solution Wronskian, so its normalization is fixed before comparison with the actual spectral series.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Filter MeasureTheory
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The original positive real zero-energy Green denominator, evaluated at the nonsingular midpoint.
Use: zeroGreenFactor uses precisely the independently proved selected-solution Wronskian, so its normalization is fixed before comparison with the actual spectral series.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
-/
def zeroGreenConstant (a : ℝ) : ℝ := (zeroGreenWronskian a (1/2)).re

/-- The original selected-solution Green denominator is positive.
Use: coefficient evaluation and the derivative jump of zeroGreenFactor divide only by the genuine nonzero normalization.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
Proof: specialize the independently proved true Wronskian positivity to its nonsingular midpoint. -/
theorem zeroGreenConstant_pos {a : ℝ} (ha : -1<a) : 0<zeroGreenConstant a :=
  zeroGreenWronskian_pos ha (by norm_num : (1/2:ℝ)∈Ioo (0:ℝ) 1)

/-- The selected left/right Green factor formed from the original reference solution and its reflection.
Use: the full Green factorization identifies this original expression with zeroGreenKernel by computing every coefficient in the proved complete reference basis.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
-/
def zeroGreenFactor (a t s : ℝ) : ℝ :=
  realSolution a (jacobi.Jacobi.endpointCorrection a) (min t s)*
    realSolution a (jacobi.Jacobi.endpointCorrection a) (1-max t s)/zeroGreenConstant a

attribute [local irreducible] zeroGreenFactor zeroGreenConstant realSolution
attribute [local irreducible] solution

/-- Every actual selected-solution Green row with an interior source is continuous on the whole closed original unit interval.
Use: the full coefficient identity and the actual continuous L2 embedding imply pointwise Green factorization, including both physical endpoints.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
Proof: the minimum keeps the left selected argument below s<1, while the reflected maximum keeps the right selected argument below 1-s<1. Both arguments stay nonnegative, so genuine endpoint-inclusive original joint continuity applies everywhere on the closed row. -/
theorem zeroGreenFactor_continuousOn {a s : ℝ} (ha : -1<a) (hs : s∈Ioo (0:ℝ) 1) :
    ContinuousOn (fun t => zeroGreenFactor a t s) (Icc (0:ℝ) 1) := by
  -- Neither unreflected selected solution is evaluated at its opposite singular endpoint.
  unfold zeroGreenFactor
  intro t ht
  have hl : min t s∈Ico (0:ℝ) 1 := ⟨le_min ht.1 hs.1.le,(min_le_right t s).trans_lt hs.2⟩
  have hr : 1-max t s∈Ico (0:ℝ) 1 :=
    ⟨sub_nonneg.mpr (max_le ht.2 hs.2.le),by linarith [le_max_right t s,hs.1]⟩
  have hc (E x : ℝ) (hx : x∈Ico (0:ℝ) 1) : ContinuousAt (realSolution a E) x := by
    unfold realSolution
    have hpair : ContinuousAt (fun y : ℝ => (y,(E:ℂ))) x :=
      continuousAt_id.prodMk continuousAt_const
    have hcc : ContinuousAt (fun y : ℝ => solution a (E:ℂ) y) x :=
      (solution_joint_continuous ha hx (E:ℂ)).comp_of_eq hpair rfl
    exact Complex.continuous_re.continuousAt.comp hcc
  have hmin : ContinuousAt (fun x : ℝ => min x s) t := continuousAt_id.min continuousAt_const
  have hmax : ContinuousAt (fun x : ℝ => 1-max x s) t :=
    continuousAt_const.sub (continuousAt_id.max continuousAt_const)
  have hleft : ContinuousAt (fun x : ℝ => realSolution a (jacobi.Jacobi.endpointCorrection a) (min x s)) t :=
    (hc _ _ hl).comp_of_eq hmin rfl
  have hright : ContinuousAt (fun x : ℝ => realSolution a (jacobi.Jacobi.endpointCorrection a) (1-max x s)) t :=
    (hc _ _ hr).comp_of_eq hmax rfl
  exact (hleft.mul hright).div_const _ |>.continuousWithinAt

/-- The selected-solution Green row is a genuine continuous function on the same full interval as the reference Hilbert basis.
Use: its original coefficient computation can be compared to zeroGreenRow in the actual L2 space, then continuous representatives give pointwise equality.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
-/
def zeroGreenFactorRow (a : ℝ) (ha : -1<a) (s : ℝ) (hs : s∈Ioo (0:ℝ) 1) : C(Interval,ℝ) :=
  ⟨fun t => zeroGreenFactor a t s,(zeroGreenFactor_continuousOn ha hs).comp_continuous
    continuous_subtype_val (fun t => t.property)⟩

/-- The exact original reference energy difference is the genuine positive squared phase.
Use: the real Green identity and the factor-row coefficient calculation use the original denominator varpi_k^2 with no spectral rescaling.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
Proof: cancel the exact endpoint correction in the independently defined original reference eigenvalue. -/
theorem reference_energy_phase (a : ℝ) (k : ℕ) :
    eigenvalue a k- jacobi.Jacobi.endpointCorrection a=(jacobi.Bessel.phaseGrid a k)^2 := by
  rw [eigenvalue_eq]
  change _-(1/4-a^2)=_
  ring

/-- The original Green identity at c_0 holds with the genuine real solutions and their actual real slopes.
Use: computes both halves of every coefficient of zeroGreenFactorRow, discharging the normalization in the complete spectral Green factorization.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
Proof: specialize the proved complex Green identity to the two original real energies, convert the actual integral to the inclusion of its real integral, and use the independently proved reality of the genuine spatial slopes. -/
theorem reference_zero_green_identity {a t : ℝ} (ha : -1<a) (k : ℕ) (ht : t∈Ioo (0:ℝ) 1) :
    (jacobi.Bessel.phaseGrid a k)^2*
      (∫ x in (0:ℝ)..t,realSolution a (eigenvalue a k) x*realSolution a (jacobi.Jacobi.endpointCorrection a) x)=
      realSolution a (eigenvalue a k) t*realSlope a (jacobi.Jacobi.endpointCorrection a) t-
        realSlope a (eigenvalue a k) t*realSolution a (jacobi.Jacobi.endpointCorrection a) t := by
  -- Every slope in this identity is the already proved actual spatial derivative.
  have hh := reference_green_identity ha (eigenvalue a k:ℂ) (jacobi.Jacobi.endpointCorrection a:ℂ) ht
  have hi : (∫ x in (0:ℝ)..t,solution a (eigenvalue a k:ℂ) x*solution a (jacobi.Jacobi.endpointCorrection a:ℂ) x)=
      ((∫ x in (0:ℝ)..t,realSolution a (eigenvalue a k) x*realSolution a (jacobi.Jacobi.endpointCorrection a) x):ℝ) := by
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro x _hx
    dsimp only
    rw [Complex.ofReal_mul,realSolution_cast,realSolution_cast]
  have he : (eigenvalue a k:ℂ)-(jacobi.Jacobi.endpointCorrection a:ℂ)=((jacobi.Bessel.phaseGrid a k)^2:ℝ) := by
    exact_mod_cast reference_energy_phase a k
  have hw : referenceWronskian a (eigenvalue a k:ℂ) (jacobi.Jacobi.endpointCorrection a:ℂ) t=
      ((realSolution a (eigenvalue a k) t*realSlope a (jacobi.Jacobi.endpointCorrection a) t-
        realSlope a (eigenvalue a k) t*realSolution a (jacobi.Jacobi.endpointCorrection a) t:ℝ):ℂ) := by
    simp only [referenceWronskian,Complex.ofReal_sub,Complex.ofReal_mul,realSolution_cast,realSlope,
      solutionSlope_real a (eigenvalue a k) ht,solutionSlope_real a (jacobi.Jacobi.endpointCorrection a) ht]
  rw [hi,he,hw,← Complex.ofReal_mul] at hh
  exact Complex.ofReal_injective hh

end
end jacobi.Reference
