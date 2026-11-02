import jacobi.Complex.EvenDescent
import jacobi.Reference.NormingFormula

/-!
Article: jacobi, Appendix C.2 (exact parity splitting).
The literal reciprocal-Gamma formula defines an entire function of
energy. Its zeros are exactly the original reference eigenvalues, and
the derivative at each zero is computed with its exact alternating sign.
Source: Euler's Gamma recurrence and the entire reciprocal Gamma function,
mathlib Analysis.SpecialFunctions.Gamma.Beta.
Use: computes the simple reciprocal-Gamma zeros used in characteristicTau_derivative.
-/
namespace jacobi.Reference
noncomputable section
open Real Set _root_.Complex
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The derivative of reciprocal Gamma satisfies its exact recurrence at every complex argument, including its zeros.
Use: computes the simple reciprocal-Gamma zeros used in characteristicTau_derivative.
Article: jacobi, Appendix C.2 (exact parity splitting).
Source: Euler's recurrence, Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one.
Proof: differentiate the globally valid reciprocal recurrence using the community entire-function theorem. -/
theorem reciprocalGamma_derivative (z : ℂ) :
    deriv (fun s : ℂ => (Complex.Gamma s)⁻¹) z=
      (Complex.Gamma (z+1))⁻¹+z*deriv (fun s : ℂ => (Complex.Gamma s)⁻¹) (z+1) := by
  -- The reciprocal recurrence remains valid at zero, unlike the Gamma recurrence before taking reciprocals.
  have hf := Complex.differentiable_one_div_Gamma (z+1)
  have hd := (hasDerivAt_id z).mul
    (hf.hasDerivAt.comp z ((hasDerivAt_id z).add_const 1))
  have he : (fun s : ℂ => s*(Complex.Gamma (s+1))⁻¹)=
      (fun s => (Complex.Gamma s)⁻¹) :=
    funext fun s => (Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one s).symm
  change HasDerivAt (fun s : ℂ => s*(Complex.Gamma (s+1))⁻¹) _ z at hd
  rw [he] at hd
  simpa only [one_mul,mul_one,Function.comp_apply,id_eq] using hd.deriv

/-- Reciprocal Gamma has the exact nonzero derivative (-1)^n*n! at its zero -n.
Use: supplies the actual reference characteristic derivative, rather than assuming a residue formula at Gamma poles.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Source: the classical reciprocal-Gamma zero formula, proved here by Euler's recurrence.
Proof: the reciprocal recurrence gives derivative one at zero. At each
successive negative integer its first term vanishes and the remaining
factor is -(n+1), exactly the next signed factorial. -/
theorem reciprocalGamma_derivative_neg_nat (n : ℕ) :
    deriv (fun s : ℂ => (Complex.Gamma s)⁻¹) (-(n:ℂ))=(-1:ℂ)^n*(n.factorial:ℂ) := by
  -- This induction includes the totalized Gamma values at the poles, where reciprocal Gamma is genuinely analytic.
  induction n with
  | zero =>
    rw [Nat.cast_zero,neg_zero,reciprocalGamma_derivative]
    simp
  | succ n ih =>
    rw [reciprocalGamma_derivative]
    have he : -((n+1:ℕ):ℂ)+1= -(n:ℂ) := by push_cast; ring
    rw [he,Complex.Gamma_neg_nat_eq_zero,inv_zero,zero_add,ih,pow_succ,Nat.factorial_succ]
    push_cast
    ring

/-- The literal even frequency form of the article's reference characteristic.
Use: descends to the actual entire energy characteristic and computes its derivatives at the genuine reference frequencies.
Article: jacobi, Appendix C.2 (exact parity splitting).
-/
def characteristicGamma (a : ℝ) (x : ℂ) : ℂ :=
  (Complex.Gamma ((gamma a:ℂ)-x))⁻¹*(Complex.Gamma ((gamma a:ℂ)+x))⁻¹

/-- The actual reciprocal-Gamma frequency characteristic is entire.
Use: proves entire energy dependence of characteristicTau through even_entire_descent.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: both affine arguments compose with the community entire reciprocal Gamma function. -/
theorem characteristicGamma_analytic (a : ℝ) (x : ℂ) :
    AnalyticAt ℂ (characteristicGamma a) x := by
  have hm := Complex.differentiable_one_div_Gamma.analyticAt ((gamma a:ℂ)-x)
  have hp := Complex.differentiable_one_div_Gamma.analyticAt ((gamma a:ℂ)+x)
  exact (hm.comp (f := fun u : ℂ => (gamma a:ℂ)-u)
    (analyticAt_const.sub analyticAt_id)).mul
      (hp.comp (f := fun u : ℂ => (gamma a:ℂ)+u) (analyticAt_const.add analyticAt_id))

/-- The literal Gamma characteristic is even in its frequency argument.
Use: removes the apparent square-root branch in the actual energy formula.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: negating the argument interchanges the two factors. -/
theorem characteristicGamma_even (a : ℝ) (x : ℂ) :
    characteristicGamma a (-x)=characteristicGamma a x := by
  simp only [characteristicGamma,sub_neg_eq_add,← sub_eq_add_neg,mul_comm]

/-- The exact reference characteristic in the article's energy variable and normalization.
Use: supplies Delta_tau itself, its spectral zeros and its reciprocal-derivative normalization; no arbitrary entire prefactor is introduced.
Article: jacobi, Appendix C.2 (exact parity splitting).
-/
def characteristicTau (a : ℝ) (z : ℂ) : ℂ :=
  characteristicGamma a (Complex.sqrt (z-(jacobi.Jacobi.endpointCorrection a:ℂ))/(Real.pi:ℂ))

/-- Every square root with the prescribed energy gives the identical literal reference characteristic.
Use: evaluates the characteristic on polynomial frequency parametrizations without differentiating a branch.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: after division by the nonzero pi both roots have equal squares; use evenness of the actual Gamma product. -/
theorem characteristicTau_eq (a : ℝ) {z omega : ℂ}
    (h : omega^2=z-(jacobi.Jacobi.endpointCorrection a:ℂ)) :
    characteristicTau a z=characteristicGamma a (omega/(Real.pi:ℂ)) := by
  apply jacobi.Complex.even_eq_of_square_eq (characteristicGamma_even a)
  rw [div_pow,div_pow,frequency_square,h]

/-- The literal reciprocal-Gamma characteristic is entire in energy, including its square-root branch point.
Use: justifies genuine characteristic derivatives, zeros and contour arguments in Proposition C.2.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: the entire frequency product is even, so even_entire_descent
gives an entire function of the squared frequency. Compose with the
actual energy shift; no slit-plane restriction remains. -/
theorem characteristicTau_analytic (a : ℝ) (z : ℂ) : AnalyticAt ℂ (characteristicTau a) z := by
  -- Even descent applies before shifting the energy, so its branch point is covered by the same entire function.
  let f : ℂ → ℂ := fun w => characteristicGamma a (w/(Real.pi:ℂ))
  have hf (w : ℂ) : AnalyticAt ℂ f w :=
    (characteristicGamma_analytic a (w/(Real.pi:ℂ))).comp
      (f := fun u : ℂ => u/(Real.pi:ℂ)) analyticAt_id.div_const
  have he (w : ℂ) : f (-w)=f w := by
    dsimp [f]
    rw [neg_div,characteristicGamma_even]
  exact (jacobi.Complex.even_entire_descent hf he
    (z-(jacobi.Jacobi.endpointCorrection a:ℂ))).comp
      (f := fun u : ℂ => u-(jacobi.Jacobi.endpointCorrection a:ℂ))
      (analyticAt_id.sub analyticAt_const)

/-- The reference characteristic vanishes exactly at the genuine reference eigenvalues, with no additional complex zeros.
Use: fixes the full characteristic zero set in the source norming formulas and parity argument.
Article: jacobi, Appendix C.2 (norming ratios).
Proof: a zero Gamma reciprocal has argument a nonpositive integer. Each
of the two factors therefore gives one of the opposite true reference
frequencies; squaring yields the original eigenvalue. Conversely its
positive frequency makes the first Gamma reciprocal vanish. -/
theorem characteristicTau_zero_iff (a : ℝ) (z : ℂ) :
    characteristicTau a z=0 ↔ ∃ k : ℕ,z=(eigenvalue a k:ℂ) := by
  -- The two possible root signs yield the same actual energy.
  constructor
  · intro hz
    change (Complex.Gamma ((gamma a:ℂ)-Complex.sqrt (z-(jacobi.Jacobi.endpointCorrection a:ℂ))/(Real.pi:ℂ)))⁻¹*
      (Complex.Gamma ((gamma a:ℂ)+Complex.sqrt (z-(jacobi.Jacobi.endpointCorrection a:ℂ))/(Real.pi:ℂ)))⁻¹=0 at hz
    rcases mul_eq_zero.mp hz with h | h
    all_goals
      obtain ⟨k,hk⟩ := (Complex.Gamma_eq_zero_iff _).mp (inv_eq_zero.mp h)
      refine ⟨k,?_⟩
      have hs := frequency_square (z-(jacobi.Jacobi.endpointCorrection a:ℂ))
      have hpi : (Real.pi:ℂ)≠0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      have he : Complex.sqrt (z-(jacobi.Jacobi.endpointCorrection a:ℂ))=
          (Real.pi:ℂ)*((k:ℂ)+(gamma a:ℂ)) ∨
        Complex.sqrt (z-(jacobi.Jacobi.endpointCorrection a:ℂ))=
          -((Real.pi:ℂ)*((k:ℂ)+(gamma a:ℂ))) := by
        first | left; field_simp [hpi] at hk; linear_combination -hk
              | right; field_simp [hpi] at hk; linear_combination hk
      rcases he with he | he <;> rw [he] at hs
      all_goals
        unfold eigenvalue
        push_cast
        linear_combination -hs
  · rintro ⟨k,rfl⟩
    rw [characteristicTau_eq a (omega := (Real.pi:ℂ)*((k:ℂ)+(gamma a:ℂ))) (by
      unfold eigenvalue; push_cast; ring)]
    rw [mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)]
    simp only [characteristicGamma,show (gamma a:ℂ)-((k:ℂ)+(gamma a:ℂ))= -(k:ℂ) by ring,
      Complex.Gamma_neg_nat_eq_zero,inv_zero,zero_mul]

end
end jacobi.Reference
