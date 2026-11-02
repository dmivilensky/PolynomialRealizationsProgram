import jacobi.Analysis.HyperbolicFourierIntegral
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
Article: jacobi, Theorem C.5.
The genuine periodic cosh arc is reconstructed from its exact Fourier
coefficients using mathlib's uniform Fourier theorem. Subtracting its
values at zero and twice the physical coordinate will evaluate the
original shifted sine-square series.
Source: Fourier series of a continuous function with absolutely summable
coefficients, mathlib has_pointwise_sum_fourier_series_of_summable.
Use: coshCircle and its original normalized Fourier integrals use period two.
-/
namespace jacobi.Analysis
noncomputable section
open Complex Set MeasureTheory
open scoped Topology

/-- The two-period circle uses its actual positive period.
Use: coshCircle and its original normalized Fourier integrals use period two.
Article: jacobi, Theorem C.5.
-/
local instance : Fact (0<(2:ℝ)) := ⟨by norm_num⟩

/-- The actual continuous periodic cosh arc with period two.
Use: coshCircle_fourierCoeff evaluates its original Fourier coefficients before reconstructing the genuine sine resolvent series.
Article: jacobi, Theorem C.5.
-/
def coshCircle (r:ℂ) : C(AddCircle (2:ℝ),ℂ) :=
  ⟨AddCircle.liftIco 2 0 (fun x:ℝ => Complex.cosh (r*(1-(x:ℂ)))),
    AddCircle.liftIco_zero_continuous
      (by norm_num only [Complex.ofReal_zero,Complex.ofReal_ofNat,sub_zero,mul_one,
        show (1:ℂ)-2= -1 by norm_num,mul_neg_one,Complex.cosh_neg])
      (by fun_prop)⟩

/-- The genuine periodic arc has its original unperiodized value throughout the defining half-open period.
Use: the original physical points zero and 2t are evaluated exactly in the Fourier reconstruction.
Article: jacobi, Theorem C.5.
Proof: the additive-circle representative is exactly x on [0,2). -/
theorem coshCircle_apply (r:ℂ) {x:ℝ} (hx:x∈Ico (0:ℝ) 2) :
    coshCircle r (x:AddCircle (2:ℝ))=Complex.cosh (r*(1-(x:ℂ))) := by
  exact AddCircle.liftIco_zero_coe_apply (f:=fun x:ℝ => Complex.cosh (r*(1-(x:ℂ)))) hx

/-- The literal integer Fourier coefficient of the original periodic cosh arc.
Use: coshCircle_fourierCoeff and the genuine absolute summability criterion reconstruct the actual original periodic function.
Article: jacobi, Theorem C.5.
-/
def coshCoefficient (r:ℂ) (n:ℤ) : ℂ :=
  r*Complex.sinh r/(r^2+(Real.pi:ℂ)^2*(n:ℂ)^2)

/-- Every genuine Fourier coefficient of the original continuous cosh arc is its exact resolvent rational expression.
Use: coshCircle_hasSum evaluates the original series through the community Fourier theorem.
Article: jacobi, Theorem C.5.
Proof: the actual additive-circle coefficient is half the integral over
the original period [0,2]. The proved exact primitive computes that
same integrand, including the integer frequency and normalization. -/
theorem coshCircle_fourierCoeff (r:ℂ) (n:ℤ)
    (hD:r^2+(Real.pi:ℂ)^2*(n:ℂ)^2≠0) :
    fourierCoeff (coshCircle r) n=coshCoefficient r n := by
  -- The period normalization is retained before the exact integral is substituted.
  rw [fourierCoeff_eq_intervalIntegral _ n 0]
  simp only [zero_add]
  have he (x:ℝ) : fourier (-n) (x:AddCircle (2:ℝ))=
      Complex.exp (-(Real.pi:ℂ)*(n:ℂ)*Complex.I*(x:ℂ)) := by
    rw [fourier_coe_apply]
    congr 1
    push_cast
    ring
  have hi : (∫x in (0:ℝ)..2,fourier (-n) (x:AddCircle (2:ℝ)) • coshCircle r (x:AddCircle (2:ℝ)))=
      ∫x in (0:ℝ)..2,Complex.exp (-(Real.pi:ℂ)*(n:ℂ)*Complex.I*(x:ℂ))*
        Complex.cosh (r*(1-(x:ℂ))) := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num : (0:ℝ)≤2)
    intro x hx
    dsimp only
    rw [he,coshCircle_apply r ⟨hx.1.le,hx.2⟩]
    rfl
  rw [hi]
  change ((1/2:ℝ):ℂ)*(∫x in (0:ℝ)..2,
    Complex.exp (-(Real.pi:ℂ)*(n:ℂ)*Complex.I*(x:ℂ))*Complex.cosh (r*(1-(x:ℂ))))=_
  rw [cosh_fourier_integral r n hD]
  unfold coshCoefficient
  push_cast
  ring

/-- The actual cosh coefficients are even in the genuine integer frequency.
Use: the shifted sine resolvent series pairs the positive and negative Fourier frequencies exactly.
Article: jacobi, Theorem C.5.
Proof: the original denominator contains only the squared integer frequency. -/
theorem coshCoefficient_neg (r:ℂ) (n:ℤ) : coshCoefficient r (-n)=coshCoefficient r n := by
  simp only [coshCoefficient,Int.cast_neg,neg_sq]

/-- Absolute summability of the original positive Fourier tail gives absolute summability of the full genuine integer sequence.
Use: coshCircle_hasSum applies the community Fourier reconstruction with its actual required summability premise proved from the original shifted Bessel spectrum.
Article: jacobi, Theorem C.5.
Proof: pair the identical actual positive and negative tails and retain the finite zero-frequency coefficient separately. -/
theorem coshCoefficient_summable (r:ℂ)
    (hs:Summable (fun k:ℕ => coshCoefficient r (k+1))) : Summable (coshCoefficient r) :=
  hs.of_add_one_of_neg_add_one (by simpa only [coshCoefficient_neg] using hs)

/-- The exact original periodic cosh function is the sum of its genuine complex Fourier series.
Use: subtracting its values at zero and 2t produces the original shifted sine-square profile at U.
Article: jacobi, Theorem C.5.
Source: mathlib has_pointwise_sum_fourier_series_of_summable.
Proof: the genuine coefficient integral has the proved rational value,
and the positive/negative tail argument proves full absolute summability.
The standard Fourier theorem reconstructs the same original continuous arc. -/
theorem coshCircle_hasSum (r:ℂ)
    (hD:∀n:ℤ,r^2+(Real.pi:ℂ)^2*(n:ℂ)^2≠0)
    (hs:Summable (fun k:ℕ => coshCoefficient r (k+1))) (x:AddCircle (2:ℝ)) :
    HasSum (fun n:ℤ => coshCoefficient r n*fourier n x) (coshCircle r x) := by
  have he : fourierCoeff (coshCircle r)=coshCoefficient r := funext (fun n => coshCircle_fourierCoeff r n (hD n))
  have h := has_pointwise_sum_fourier_series_of_summable (f:=coshCircle r)
    (by rw [he]; exact coshCoefficient_summable r hs) x
  simpa only [he,smul_eq_mul] using h

end
end jacobi.Analysis
