import jacobi.Bessel.EdgeData
import jacobi.Variational.FredholmRelaxation

/-!
Article: jacobi, Appendix B.
The genuine canonical product evaluates the actual convergent logarithmic
spectral sum and the previously defined extended Fredholm observation.
All formulas retain the true subcritical spectral pole condition.
Use: turns the complex canonical product into a real-valued Fredholm identity without assuming a logarithm branch.
-/
namespace jacobi.Bessel
noncomputable section
open Real jacobi.Variational
set_option backward.isDefEq.respectTransparency false

/-- The genuine real spectral product equals the original normalized Bessel function at twice the coupling.
Use: turns the complex canonical product into a real-valued Fredholm identity without assuming a logarithm branch.
Article: jacobi, Appendix B.
Proof: the actual summable spectral perturbations give a convergent real
product. Its continuous complex embedding has the same factors as the
proved genuine Bessel canonical product; uniqueness and real parts identify the limits. -/
theorem real_canonical_product {a : ℝ} (ha : -1<a) (s : ℝ) :
    (∏' k, (1-s*edgeValue a ha k))=realNormalized a (2*s) := by
  -- Both limiting products have independently proved convergence, including when a factor vanishes.
  have hm := (Real.multipliable_one_add_of_summable ((edgeValue_summable ha).mul_left (-s)))
  have hr : Multipliable (fun k => 1-s*edgeValue a ha k) := by
    simpa only [neg_mul,sub_eq_add_neg] using hm
  have hmap := hr.hasProd.map Complex.ofRealHom Complex.continuous_ofReal
  have hc : HasProd (fun k => ((1-s*edgeValue a ha k:ℝ):ℂ))
      (normalized (a:ℂ) ((2*s:ℝ):ℂ)) := by
    convert canonical_product_hasProd ha ((2*s:ℝ):ℂ) using 1
    funext k
    unfold edgeValue
    push_cast
    ring
  have he := hmap.unique hc
  exact congrArg Complex.re he

/-- Every actual subcritical Bessel spectral product factor is strictly positive.
Use: legitimizes real logarithms and prevents totalized logarithm values from hiding a spectral pole.
Article: jacobi, Appendix B.
Proof: the genuine edge spectrum decreases, so the top pole condition controls every factor. -/
theorem canonical_factor_pos {a s : ℝ} (ha : -1<a) (hs : 0≤s)
    (hp : s*edgeValue a ha 0<1) (k : ℕ) : 0<1-s*edgeValue a ha k := by
  have hh := mul_le_mul_of_nonneg_left ((edgeValue_properties ha).2.antitone (Nat.zero_le k)) hs
  linarith

/-- The actual logarithmic Bessel spectral sum is genuinely summable.
Use: all closed-form spectral logarithms are convergent series rather than totalized infinite sums.
Article: jacobi, Appendix B.
Proof: apply the community logarithmic summability theorem to the proved genuine summable spectral perturbations. -/
theorem canonical_log_summable {a s : ℝ} (ha : -1<a) (_hs : 0≤s)
    (_hp : s*edgeValue a ha 0<1) :
    Summable (fun k => log (1-s*edgeValue a ha k)) := by
  simpa only [neg_mul,sub_eq_add_neg] using
    Real.summable_log_one_add_of_summable ((edgeValue_summable ha).mul_left (-s))

/-- The actual subcritical normalized Bessel value is the exponential of its full convergent spectral logarithmic sum.
Use: proves positivity and fixes the real logarithm branch in all Fredholm evaluations.
Article: jacobi, Appendix B.
Proof: exponentiating the genuinely convergent real logarithm sum gives
the convergent positive-factor product, whose value has already been
identified with the original normalized Bessel function. -/
theorem canonical_exp_log {a s : ℝ} (ha : -1<a) (hs : 0≤s)
    (hp : s*edgeValue a ha 0<1) :
    exp (∑' k,log (1-s*edgeValue a ha k))=realNormalized a (2*s) := by
  rw [Real.rexp_tsum_eq_tprod (canonical_factor_pos ha hs hp) (canonical_log_summable ha hs hp),
    real_canonical_product ha s]

/-- The original normalized Bessel function is strictly positive throughout its subcritical real spectral interval.
Use: real logarithm, Fredholm derivative and calibration formulas have their genuine positive input.
Article: jacobi, Appendix B.
Proof: it is the exponential of its genuinely convergent real spectral logarithmic sum. -/
theorem subcritical_value_pos {a s : ℝ} (ha : -1<a) (hs : 0≤s)
    (hp : s*edgeValue a ha 0<1) : 0<realNormalized a (2*s) := by
  rw [← canonical_exp_log ha hs hp]
  exact Real.exp_pos _

/-- The full actual Bessel logarithmic spectral sum equals the logarithm of the original normalized Bessel function.
Use: evaluates every source spectral observable f(x)=log(1-s*x) on its true subcritical domain.
Article: jacobi, Appendix B.
Proof: take the real logarithm of the proved positive exponential identity. -/
theorem canonical_log_sum {a s : ℝ} (ha : -1<a) (hs : 0≤s)
    (hp : s*edgeValue a ha 0<1) :
    (∑' k,log (1-s*edgeValue a ha k))=log (realNormalized a (2*s)) := by
  rw [← canonical_exp_log ha hs hp,Real.log_exp]

/-- The true Bessel regularized Fredholm sum has the exact original special-function closed form.
Use: evaluates the arbitrary-spectrum Fredholm threshold at the article's actual Bessel edge data.
Article: jacobi, Appendix B.
Proof: split the actual regularized logarithm into the convergent negative
logarithm sum and linear mass sum. Apply the genuine logarithmic product
identity and the exact first Rayleigh sum. -/
theorem fredholm_log_sum {a s : ℝ} (ha : -1<a) (hs : 0≤s)
    (hp : s*edgeValue a ha 0<1) :
    (∑' k,fredholmLog s (edgeValue a ha k))=
      -log (realNormalized a (2*s))-s/(2*(a+1)) := by
  simp only [fredholmLog]
  rw [((canonical_log_summable ha hs hp).neg).tsum_sub ((edgeValue_summable ha).mul_left s),
    tsum_neg,tsum_mul_left,canonical_log_sum ha hs hp,first_rayleigh_sum ha]
  ring

/-- The previously defined genuine extended Fredholm observation of the actual Bessel edge has the exact printed subcritical closed form.
Use: specializes the fully proved Fredholm variational calibration to the genuine Jacobi--Bessel edge without extra analytic premises.
Article: jacobi, Appendix B.
Proof: the genuine top pole margin controls every actual spectral entry.
The general extended-to-real Fredholm theorem then applies to this proved
summable spectrum; substitute the preceding actual special-function sum. -/
theorem edgeSpectrum_fredholm {a s : ℝ} (ha : -1<a) (hs : 0≤s)
    (hp : s*edgeValue a ha 0<1) :
    (edgeSpectrum a ha).fredholm s=
      ENNReal.ofReal (-log (realNormalized a (2*s))-s/(2*(a+1))) := by
  -- The extended functional keeps its genuine pole definition; the pole margin is discharged from the stated top-eigenvalue condition.
  have he : 0<1-s*edgeValue a ha 0 := by linarith
  have hb (k : ℕ) : s*edgeValue a ha k≤1-(1-s*edgeValue a ha 0) := by
    simpa only [sub_sub_cancel] using
      mul_le_mul_of_nonneg_left ((edgeValue_properties ha).2.antitone (Nat.zero_le k)) hs
  change fredholmSpectrum s (edgeValue a ha)=_
  rw [fredholmSpectrum_eq hs he (edgeValue_summable ha)
    (fun k => ((edgeValue_properties ha).1 k).le) hb,fredholm_log_sum ha hs hp]

end
end jacobi.Bessel
