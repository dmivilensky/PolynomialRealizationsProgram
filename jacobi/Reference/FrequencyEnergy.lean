import jacobi.Reference.WaveEquation

/-!
Article: jacobi, Appendix C.1 (negative-energy bounds).
The genuine frequency energy uses the solution and its actual derivative.
The large real-frequency terms cancel exactly. Only twice the imaginary
frequency and the true singular potential contribute to its logarithmic
growth, giving the source exponential type and strip bounds.
Use: removes the large real oscillation from the actual reference energy derivative.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Complex
open scoped Topology ComplexConjugate
set_option backward.isDefEq.respectTransparency false

/-- The exact defect between the frequency norm square and its complex square has only the imaginary-frequency size.
Use: removes the large real oscillation from the actual reference energy derivative.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Proof: factor the genuine defect as omega*(conj(omega)-omega). The
second factor is purely imaginary with norm twice abs(Im omega).
Multiplicativity of the actual complex norm gives the precise identity. -/
theorem frequency_square_defect (omega : ℂ) :
    ‖((‖omega‖^2:ℝ):ℂ)-omega^2‖=2*|omega.im| * ‖omega‖ := by
  -- The exact identity keeps the sharp exponential type t rather than introducing exp(t*norm(omega)).
  have he : ((‖omega‖^2:ℝ):ℂ)-omega^2=(conj omega-omega)*omega := by
    rw [Complex.ofReal_pow,← Complex.mul_conj' omega]
    ring
  have hi : conj omega-omega=((-2*omega.im:ℝ):ℂ)*Complex.I := by
    apply Complex.ext <;> simp only [sub_re,sub_im,conj_re,conj_im,mul_re,mul_im,
      ofReal_re,ofReal_im,Complex.I_re,Complex.I_im] <;> ring
  rw [he,norm_mul,hi,norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one,
    abs_mul,abs_neg]
  norm_num

/-- The genuine quadratic frequency energy of a complex state and its true spatial derivative.
Use: propagates the actual reference initial state from t of order |omega|^-1 to the full source half interval.
Article: jacobi, Appendix C.1 (negative-energy bounds).
-/
def frequencyEnergy (omega u v : ℂ) : ℝ := ‖u‖^2+‖v‖^2/‖omega‖^2

/-- The actual complex-frequency state energy is nonnegative for every genuine state.
Use: multiplying the differential energy bound by positive integrating factors preserves the required inequality.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Proof: both squared norms are nonnegative, and division by a squared norm preserves nonnegativity. -/
theorem frequencyEnergy_nonneg (omega u v : ℂ) : 0≤frequencyEnergy omega u v := by
  unfold frequencyEnergy
  positivity

/-- The true complex quadratic energy obeys the sharp cancellation estimate for any state of the original reference equation.
Use: supplies the original high-frequency differential inequality, with twice the imaginary part rather than the full frequency norm.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Proof: combine the two genuine real parts before taking any norm.
The resulting coefficient is |omega|^2-omega^2+Q. Bound its norm by
the exact imaginary-frequency defect plus abs(Q), and use the
nonnegative square (|omega| *|u|-|v|)^2 to bound the mixed state product. -/
theorem frequencyEnergy_algebra {omega u v : ℂ} (homega : 0<‖omega‖) (Q : ℝ) :
    2*(v*conj u).re+2*(((Q:ℂ)-omega^2)*u*conj v).re/‖omega‖^2≤
      (2*|omega.im|+|Q|/‖omega‖)*frequencyEnergy omega u v := by
  -- Cancellation precedes the norm bound, which is essential for uniform real-frequency estimates.
  let R := ‖omega‖
  let D : ℂ := ((R^2:ℝ):ℂ)-omega^2+(Q:ℂ)
  have hR : 0<R := homega
  have hid : 2*(v*conj u).re+2*(((Q:ℂ)-omega^2)*u*conj v).re/R^2=
      2*(D*u*conj v).re/R^2 := by
    dsimp [D]
    simp only [mul_re,mul_im,sub_re,sub_im,add_re,add_im,conj_re,conj_im,ofReal_re,ofReal_im,pow_two]
    field_simp
    ring
  have hD : ‖D‖≤2*|omega.im| * R+|Q| := by
    apply (norm_add_le _ _).trans
    rw [frequency_square_defect,Complex.norm_real,Real.norm_eq_abs]
  have hre : (D*u*conj v).re≤‖D‖*‖u‖*‖v‖ := by
    calc
      _ ≤ ‖D*u*conj v‖ := Complex.re_le_norm _
      _ = _ := by rw [norm_mul,norm_mul,Complex.norm_conj]
  have hprod : 2*R*‖u‖*‖v‖≤R^2*‖u‖^2+‖v‖^2 := by
    nlinarith [sq_nonneg (R*‖u‖-‖v‖)]
  have hmul := mul_le_mul_of_nonneg_right hD (show 0≤‖u‖*‖v‖ by positivity)
  have hmix := mul_le_mul_of_nonneg_left hprod (show 0≤2*|omega.im| * R+|Q| by positivity)
  rw [hid]
  unfold frequencyEnergy
  change 2*(D*u*conj v).re/R^2≤(2*|omega.im|+|Q|/R)*(‖u‖^2+‖v‖^2/R^2)
  apply (div_le_iff₀ (sq_pos_of_pos hR)).mpr
  field_simp
  nlinarith [hmul,hmix,mul_le_mul_of_nonneg_left hre (show 0≤R by positivity)]

/-- The actual original reference wave energy as a genuine function of the physical spatial coordinate.
Use: the high-frequency integrating factor is applied to the original source wave and its actual derivative.
Article: jacobi, Appendix C.1 (negative-energy bounds).
-/
def waveEnergy (a : ℝ) (omega : ℂ) (t : ℝ) : ℝ :=
  frequencyEnergy omega (wave a omega t) (waveSlope a omega t)

/-- The genuine original reference energy has the exact spatial derivative built from its true state derivatives.
Use: applies the proved sharp quadratic cancellation bound to the actual reference solution.
Article: jacobi, Lemma C.1.
Proof: differentiate both true squared norms by the community real
real and imaginary part derivative rules, retain the fixed frequency denominator,
and combine the two real derivatives into the actual complex real parts. -/
theorem waveEnergy_hasDerivAt (a : ℝ) (omega : ℂ) {t : ℝ} (ht : t∈Ioo 0 1) :
    HasDerivAt (waveEnergy a omega)
      (2*(waveSlope a omega t*conj (wave a omega t)).re+
        2*(waveAcceleration a omega t*conj (waveSlope a omega t)).re/‖omega‖^2) t := by
  -- All differentiated states were independently proved to be the actual original first and second derivatives.
  have hnorm {f : ℝ → ℂ} {f' : ℂ} (hf : HasDerivAt f f' t) :
      HasDerivAt (fun s => ‖f s‖^2) (2*(f'*conj (f t)).re) t := by
    have hr : HasDerivAt (fun s => (f s).re) f'.re t := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hf
    have hi : HasDerivAt (fun s => (f s).im) f'.im t := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hf
    convert (hr.pow 2).add (hi.pow 2) using 1
    · funext s
      rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
      simp only [Pi.add_apply,pow_two,Pi.mul_apply]
    · simp only [mul_re,conj_re,conj_im]
      ring
  exact (hnorm (wave_hasDerivAt a omega ht)).add
    ((hnorm (waveSlope_hasDerivAt a omega ht)).div_const (‖omega‖^2))

end
end jacobi.Reference
