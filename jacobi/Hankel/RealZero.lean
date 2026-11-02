import jacobi.Hankel.ZeroHolomorphy
import jacobi.Bessel.OrdinaryPhase

/-!
Article: jacobi, Lemma E.1.
Use: the real restriction of the constructed complex frequency branches can be identified with the original ordered enumeration in Lemma E.1.
-/
namespace jacobi.Hankel
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Every original Bessel frequency zero in the right half-plane at real admissible order is one of the actual positive real numbered Bessel zeros.
Use: the real restriction of the constructed complex frequency branches can be identified with the original ordered enumeration in Lemma E.1.
Article: jacobi, Lemma E.1.
Proof: the earlier actual singular Green identity makes the squared frequency positive real. Its imaginary part is twice the product of the true real and imaginary frequency coordinates; the positive real coordinate forces the imaginary coordinate to vanish. Exhaustiveness of the original positive zero enumeration finishes the identification. -/
theorem frequency_zero_real {a : ℝ} (ha : -1<a) {z : ℂ} (hz : 0<z.re)
    (hzero : jacobi.Bessel.normalized (a:ℂ) (z^2)=0) :
    ∃ m : ℕ,z=(jacobi.Bessel.positiveZero a ha m:ℂ) := by
  -- The actual Green identity supplies reality of every spectral zero before any zero numbering is used.
  obtain ⟨ℓ,_hℓ,hℓeq⟩ := jacobi.Bessel.normalized_zero_positive ha hzero
  have him := congrArg Complex.im hℓeq
  simp only [pow_two,Complex.mul_im,Complex.ofReal_im] at him
  have hprod : (2*z.re)*z.im=0 := by nlinarith
  have hi : z.im=0 := (mul_eq_zero.mp hprod).resolve_left (mul_ne_zero (by norm_num) hz.ne')
  have hre : z=(z.re:ℂ) := Complex.ext rfl (by simpa only [Complex.ofReal_im] using hi)
  have hF : jacobi.Bessel.normalized (a:ℂ) ((z.re^2:ℝ):ℂ)=0 := by
    rw [Complex.ofReal_pow,← hre]
    exact hzero
  obtain ⟨m,hm⟩ := jacobi.Bessel.positiveZero_exhaustive ha hz ((jacobi.Bessel.cylindrical_zero_iff ha hz).mpr hF)
  exact ⟨m,hre.trans (congrArg Complex.ofReal hm.symm)⟩

end
end jacobi.Hankel
