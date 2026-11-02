import jacobi.Analysis.HyperbolicFourierSeries

/-!
Article: jacobi, Theorem C.5.
Pair the positive and negative Fourier frequencies of the actual cosh
arc. The resulting sine-square series has exactly the normalization of
the article's shifted profile, multiplied by r*sinh(r).
Use: fourier_pair_sine uses exactly the source frequencies pi*k.
-/
namespace jacobi.Analysis
noncomputable section
open Complex Set

/-- The Fourier period two is positive in the original physical normalization.
Use: fourier_pair_sine uses exactly the source frequencies pi*k.
Article: jacobi, Theorem C.5.
-/
local instance : Fact (0<(2:ℝ)) := ⟨by norm_num⟩

/-- The original opposite Fourier frequencies combine into precisely four times the corresponding sine square.
Use: cosh_sine_hasSum groups the same original Fourier series without changing any coefficient or frequency.
Article: jacobi, Theorem C.5.
Proof: evaluate both original circle characters, use Euler's formula,
and then the exact complex cosine double-angle identity. -/
theorem fourier_pair_sine (n:ℤ) (t:ℝ) :
    2-fourier n ((2*t:ℝ):AddCircle (2:ℝ))-fourier (-n) ((2*t:ℝ):AddCircle (2:ℝ))=
      4*Complex.sin ((Real.pi:ℂ)*(n:ℂ)*(t:ℂ))^2 := by
  -- The characters are evaluated before combining their original positive and negative phases.
  have he (m:ℤ) : fourier m ((2*t:ℝ):AddCircle (2:ℝ))=
      Complex.exp ((2*(Real.pi:ℂ)*(m:ℂ)*(t:ℂ))*Complex.I) := by
    rw [fourier_coe_apply]
    congr 1
    push_cast
    ring
  rw [he n,he (-n)]
  push_cast
  rw [show 2*(Real.pi:ℂ)*(-(n:ℂ))*(t:ℂ)= -(2*((Real.pi:ℂ)*(n:ℂ)*(t:ℂ))) by ring,
    show 2*(Real.pi:ℂ)*(n:ℂ)*(t:ℂ)=2*((Real.pi:ℂ)*(n:ℂ)*(t:ℂ)) by ring,
    Complex.exp_mul_I,Complex.exp_mul_I,Complex.cos_neg,Complex.sin_neg,
    Complex.cos_two_mul_eq_one_sub]
  ring

/-- The original continuous periodic cosh arc yields the exact genuine shifted sine-square sum.
Use: half_sine_shifted_profile evaluates the article's actual spectral profile after discharging the denominator and summability premises from its actual slit domain.
Article: jacobi, Theorem C.5.
Proof: subtract the proved Fourier sums at zero and twice the physical
coordinate. Pair positive and negative integer frequencies; their zero
term vanishes and their exact character difference is four sine squares.
Remove the original initial zero term to retain the article's positive spectrum. -/
theorem cosh_sine_hasSum (r:ℂ)
    (hD:∀n:ℤ,r^2+(Real.pi:ℂ)^2*(n:ℂ)^2≠0)
    (hs:Summable (fun k:ℕ => coshCoefficient r (k+1)))
    {t:ℝ} (ht:t∈Ico (0:ℝ) 1) :
    HasSum (fun k:ℕ => 4*coshCoefficient r (k+1)*
      Complex.sin ((Real.pi:ℂ)*(k+1:ℂ)*(t:ℂ))^2)
        (Complex.cosh r-Complex.cosh (r*(1-2*(t:ℂ)))) := by
  -- The subtraction and the pairing concern actual convergent original Fourier series.
  have h0 := coshCircle_hasSum r hD hs 0
  have ht' := coshCircle_hasSum r hD hs ((2*t:ℝ):AddCircle (2:ℝ))
  have h := (h0.sub ht').nat_add_neg
  simp only [fourier_zero,mul_one,sub_self,add_zero] at h
  have hp : HasSum (fun n:ℕ => 4*coshCoefficient r n*
      Complex.sin ((Real.pi:ℂ)*(n:ℂ)*(t:ℂ))^2)
        (coshCircle r 0-coshCircle r ((2*t:ℝ):AddCircle (2:ℝ))) := by
    convert h using 1
    ext n
    rw [coshCoefficient_neg,fourier_eval_zero,fourier_eval_zero]
    have hf := fourier_pair_sine (n:ℤ) t
    norm_cast at hf ⊢
    push_cast at hf ⊢
    linear_combination -coshCoefficient r (n:ℤ)*hf
  have hv0 : coshCircle r 0=Complex.cosh r := by
    simpa only [AddCircle.coe_zero,Complex.ofReal_zero,sub_zero,mul_one] using coshCircle_apply r (x:=0) (by norm_num)
  have hvt : coshCircle r ((2*t:ℝ):AddCircle (2:ℝ))=Complex.cosh (r*(1-2*(t:ℂ))) := by
    simpa only [Complex.ofReal_mul,Complex.ofReal_ofNat] using
      coshCircle_apply r (x:=2*t) ⟨by linarith [ht.1],by linarith [ht.2]⟩
  rw [hv0,hvt] at hp
  simpa only [Finset.sum_range_one,Nat.cast_zero,mul_zero,zero_mul,Complex.sin_zero,
    zero_pow (by decide: (2:ℕ)≠0),sub_zero,Nat.cast_add,Nat.cast_one] using (hasSum_nat_add_iff' 1).mpr hp

end
end jacobi.Analysis
