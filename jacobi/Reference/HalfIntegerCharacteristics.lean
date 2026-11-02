import jacobi.Reference.NormingSigns
import jacobi.Bessel.HalfInteger
import Mathlib.Order.Hom.Set

/-!
Article: jacobi, Proposition C.4.
The two original printed characteristic functions coincide at each
half-integer order. Euler reflection is used in its globally valid
reciprocal form, including Gamma poles and the removable origin.
The proved exhaustive zero sets and genuine increasing enumerations
then identify the original target and reference spectra index by index.
Use: half_integer_characteristics proves equality of the original printed characteristics at the two special orders.
-/
namespace jacobi.Reference
noncomputable section
open Real Set _root_.Complex
set_option backward.isDefEq.respectTransparency false

/-- Euler reflection for the actual entire reciprocal-Gamma factors, including their zeros.
Use: half_integer_characteristics proves equality of the original printed characteristics at the two special orders.
Article: jacobi, Proposition C.4.
Source: Euler's Gamma reflection formula, Complex.Gamma_mul_Gamma_one_sub.
Proof: invert the globally valid community reflection identity; pi is nonzero and no Gamma factor is cancelled at a pole. -/
theorem reciprocalGamma_reflection (z : ℂ) :
    (Complex.Gamma z)⁻¹*(Complex.Gamma (1-z))⁻¹=Complex.sin ((Real.pi:ℂ)*z)/(Real.pi:ℂ) := by
  have h := congrArg Inv.inv (Complex.Gamma_mul_Gamma_one_sub z)
  simpa only [mul_inv,inv_div] using h

/-- The literal reference Gamma characteristic at order -1/2 is exactly the cosine characteristic.
Use: half_integer_characteristics identifies the actual Bessel and reference functions at alpha=-1/2.
Article: jacobi, Proposition C.4.
Source: Euler's reflection formula and the half-integer Bessel identity, DLMF 10.16.1.
Proof: the two Gamma arguments are 1/2-x and 1/2+x; their reciprocal product is cos(pi*x)/pi. -/
theorem characteristicGamma_neg_half (x : ℂ) :
    characteristicGamma (-1/2) x=Complex.cos ((Real.pi:ℂ)*x)/(Real.pi:ℂ) := by
  have h := reciprocalGamma_reflection ((1/2:ℂ)-x)
  have hg : gamma (-1/2)=1/2 := by norm_num [gamma]
  rw [characteristicGamma,hg]
  push_cast
  rw [show (1/2:ℂ)+x=1-((1/2:ℂ)-x) by ring,h]
  rw [show (Real.pi:ℂ)*((1/2:ℂ)-x)=(Real.pi:ℂ)/2-(Real.pi:ℂ)*x by ring,
    Complex.sin_pi_div_two_sub]

/-- The order 1/2 reference characteristic has the exact sine formula without division at its removable frequency origin.
Use: half_integer_characteristics compares the actual reference characteristic with the genuine entire normalized Bessel function.
Article: jacobi, Proposition C.4.
Source: Euler reflection and reciprocal Gamma recurrence, proved in mathlib.
Proof: the reciprocal recurrence absorbs x into Gamma(1+x)^(-1).
The remaining reciprocal pair Gamma(x)^(-1)*Gamma(1-x)^(-1) is the original reflection formula. -/
theorem characteristicGamma_half (x : ℂ) :
    x*characteristicGamma (1/2) x=Complex.sin ((Real.pi:ℂ)*x)/(Real.pi:ℂ) := by
  -- Use reciprocal recurrence at its zeros as well as at ordinary Gamma arguments.
  have hg : gamma (1/2)=1 := by norm_num [gamma]
  have hr := Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one x
  change (Complex.Gamma x)⁻¹=x*(Complex.Gamma (x+1))⁻¹ at hr
  rw [characteristicGamma,hg]
  push_cast
  rw [show (1:ℂ)+x=x+1 by ring]
  calc
    _ = (Complex.Gamma (1-x))⁻¹*(x*(Complex.Gamma (x+1))⁻¹) := by ring
    _ = (Complex.Gamma x)⁻¹*(Complex.Gamma (1-x))⁻¹ := by rw [← hr]; ring
    _ = _ := reciprocalGamma_reflection x

/-- The two literal Bessel characteristic constants have their exact special-order values.
Use: half_integer_characteristics compares actual printed normalizations rather than only their zero sets.
Article: jacobi, Proposition C.4.
Proof: Gamma(1/2)=sqrt(pi) and Gamma(3/2)=sqrt(pi)/2;
the actual pi half powers are sqrt(pi) and its inverse. -/
theorem half_integer_characteristic_constants :
    characteristicSigmaConstant (1/2)=1 ∧ characteristicSigmaConstant (-1/2)=1/Real.pi := by
  -- Keep the printed normalization constants; equality of zeros alone would not fix them.
  have hΓ : Real.Gamma (3/2)=Real.sqrt Real.pi/2 := by
    have h := Real.Gamma_add_one (s := (1/2:ℝ)) (by norm_num)
    norm_num only [show (1/2:ℝ)+1=3/2 by ring,Real.Gamma_one_half_eq] at h
    linarith
  have hp : Real.pi^(1/2:ℝ)=Real.sqrt Real.pi := (Real.sqrt_eq_rpow _).symm
  have hpn : Real.pi^(-(1/2:ℝ))=(Real.sqrt Real.pi)⁻¹ := by rw [Real.rpow_neg Real.pi_pos.le,hp]
  constructor
  · norm_num only [characteristicSigmaConstant,show -(1/2:ℝ)-1/2= -1 by ring,
      show (1/2:ℝ)+1=3/2 by ring,Real.rpow_neg_one,hp,hΓ]
    field_simp [(Real.sqrt_pos.mpr Real.pi_pos).ne']
  · norm_num only [characteristicSigmaConstant,show -(-(1/2:ℝ))-1/2=0 by ring,
      show -(1/2:ℝ)+1=1/2 by ring,Real.rpow_zero,hpn,Real.Gamma_one_half_eq,mul_one]
    rw [div_eq_mul_inv,← mul_inv,← pow_two,Real.sq_sqrt Real.pi_pos.le,one_div]

/-- The actual original Bessel and reference characteristics agree everywhere at both special orders.
Use: half_integer_spectra proves genuine index-by-index spectral coincidence and then the original F=K=0 special cases.
Article: jacobi, Proposition C.4.
Proof: at -1/2 both actual characteristics are cos(sqrt(z))/pi.
At 1/2 multiply their actual frequency forms by sqrt(z) and use the
two independently proved sine identities. At z=0 both original values are one. -/
theorem half_integer_characteristics (a : ℝ) (ha : a=(1/2:ℝ) ∨ a= -(1/2:ℝ)) (z : ℂ) :
    characteristicSigma a z=characteristicTau a z := by
  -- The removable origin is handled directly, never by cancelling its zero frequency.
  have hc (b : ℝ) (hb : b=(1/2:ℝ) ∨ b= -(1/2:ℝ)) :
      jacobi.Jacobi.endpointCorrection b=0 := by rcases hb with rfl | rfl <;> norm_num [jacobi.Jacobi.endpointCorrection]
  have hw : (Complex.sqrt z)^2=z := frequency_square z
  rcases ha with rfl | rfl
  · rw [characteristicSigma,half_integer_characteristic_constants.1,Complex.ofReal_one,one_mul,
      characteristicTau,hc _ (Or.inl rfl),Complex.ofReal_zero,sub_zero]
    by_cases hz : Complex.sqrt z=0
    · have hz0 : z=0 := by rw [hz,zero_pow (by norm_num)] at hw; exact hw.symm
      subst z
      norm_num [jacobi.Bessel.normalized_zero (a := (1/2:ℂ)) (by norm_num),characteristicGamma,gamma]
    · apply mul_left_cancel₀ hz
      have hN := jacobi.Bessel.normalized_half (Complex.sqrt z)
      rw [hw] at hN
      norm_num only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat]
      rw [hN]
      have h := characteristicGamma_half (Complex.sqrt z/(Real.pi:ℂ))
      rw [mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)] at h
      have h' := congrArg (fun w:ℂ => (Real.pi:ℂ)*w) h
      field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero] at h'
      linear_combination -h'
  · rw [show -(1/2:ℝ)= -1/2 by ring]
    have hcorr : jacobi.Jacobi.endpointCorrection (-1/2)=0 := by norm_num [jacobi.Jacobi.endpointCorrection]
    rw [characteristicSigma,half_integer_characteristic_constants.2,characteristicTau,
      hcorr,Complex.ofReal_zero,sub_zero,characteristicGamma_neg_half]
    have hN := jacobi.Bessel.normalized_neg_half (Complex.sqrt z)
    rw [hw] at hN
    push_cast
    rw [hN]
    rw [mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)]
    ring

/-- At each special order the original target spectrum is exactly the original reference spectrum in the same enumeration.
Use: half_integer_GL proves the source norming ratios are one and its actual transformation kernel is zero.
Article: jacobi, Proposition C.4.
Proof: equality of the original characteristics identifies their
exhaustive complex zero sets. Their actual real spectral ranges agree,
so the two strictly increasing natural enumerations agree index by index. -/
theorem half_integer_spectra {a : ℝ} (ha : -1<a)
    (hs : a=(1/2:ℝ) ∨ a= -(1/2:ℝ)) : jacobi.Bessel.sigma a ha=eigenvalue a := by
  -- The full zero sets are proved for the original functions; neither spectrum is redefined as the other.
  apply (jacobi.Bessel.sigma_strictMono ha).eq_of_range_eq (eigenvalue_strictMono ha)
  ext x
  constructor
  · rintro ⟨k,rfl⟩
    have h := (characteristicSigma_zero_iff ha (jacobi.Bessel.sigma a ha k:ℂ)).mpr ⟨k,rfl⟩
    rw [half_integer_characteristics a hs] at h
    obtain ⟨l,hl⟩ := (characteristicTau_zero_iff a _).mp h
    exact ⟨l,Complex.ofReal_injective hl.symm⟩
  · rintro ⟨k,rfl⟩
    have h := (characteristicTau_zero_iff a (eigenvalue a k:ℂ)).mpr ⟨k,rfl⟩
    rw [← half_integer_characteristics a hs] at h
    obtain ⟨l,hl⟩ := (characteristicSigma_zero_iff ha _).mp h
    exact ⟨l,Complex.ofReal_injective hl.symm⟩

end
end jacobi.Reference
