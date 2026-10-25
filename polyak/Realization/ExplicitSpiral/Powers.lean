import polyak.Realization.ExplicitSpiral.Coordinates

/-!
Article: every complex power has the exact real rational source coordinates.
Use: identify both the finite initial slacks and the three phase residues.
-/
namespace polyak.Realization.ExplicitSpiral
noncomputable section

/-- Article: the real power coordinate follows the scalar characteristic recurrence. -/
theorem powerReal_rec (r : ℝ) (n : ℕ) :
    Source.powerReal r (n+2)=2*r*radialCosine r*Source.powerReal r (n+1)-
      r^2*Source.powerReal r n := by
  unfold Source.powerReal
  rw [Source.chebT_rec]
  simp only [pow_add,pow_one]
  ring

/-- Article: the imaginary power coordinate follows the same recurrence, including zero. -/
theorem powerImag_rec (r : ℝ) (n : ℕ) :
    Source.powerImag r (n+2)=2*r*radialCosine r*Source.powerImag r (n+1)-
      r^2*Source.powerImag r n := by
  cases n with
  | zero => norm_num [Source.powerImag,Spectral.chebU,Polynomial.Chebyshev.U]; ring
  | succ n =>
    simp only [Source.powerImag,Nat.succ_ne_zero,↓reduceIte,Nat.succ_sub_one]
    rw [Source.chebU_rec]
    simp only [pow_add,pow_one]
    ring

/-- Article: the norm and exact real part determine all powers without choosing a phase. -/
theorem power_coordinates {r : ℝ} (_hr : 0<r) {z : ℂ}
    (hn : Complex.normSq z=r^2) (hz : z.re=Source.lambdaReal r) (k : ℕ) :
    (z^k).re=Source.powerReal r k ∧ (z^k).im=z.im*Source.powerImag r k := by
  have he : z^2=(2*z.re : ℝ)*z-(r^2 : ℝ) := by
    apply Complex.ext
    · simp only [pow_two,Complex.mul_re,Complex.sub_re,Complex.ofReal_re,Complex.ofReal_im,
        zero_mul,sub_zero]
      rw [Complex.normSq_apply] at hn
      nlinarith
    · simp only [pow_two,Complex.mul_im,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,
        zero_mul,add_zero,sub_zero]
      ring
  have hrec (n : ℕ) : z^(n+2)=(2*z.re : ℝ)*z^(n+1)-(r^2 : ℝ)*z^n := by
    rw [pow_add,pow_add,pow_one,he]
    ring
  have hc : z.re=r*radialCosine r := by
    rw [hz]
    unfold Source.lambdaReal radialCosine
    ring
  induction k using Nat.twoStepInduction with
  | zero => norm_num [Source.powerReal,Source.powerImag,Spectral.chebT,Polynomial.Chebyshev.T]
  | one =>
    constructor
    · rw [pow_one,hc]
      norm_num [Source.powerReal,Spectral.chebT,Polynomial.Chebyshev.T]
    · norm_num [Source.powerImag,Spectral.chebU,Polynomial.Chebyshev.U]
  | more n ih ih' =>
    rw [hrec]
    constructor
    · simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
        zero_mul,sub_zero,ih.1,ih'.1,hc,powerReal_rec]
      ring
    · simp only [Complex.sub_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
        zero_mul,add_zero,ih.2,ih'.2,hc,powerImag_rec]
      ring

end
end polyak.Realization.ExplicitSpiral
