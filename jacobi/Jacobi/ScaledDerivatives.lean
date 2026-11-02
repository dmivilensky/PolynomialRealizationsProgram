import jacobi.Jacobi.FiniteSpectrum
import jacobi.Jacobi.AnalyticStability

/-!
Article: jacobi, Lemma 1.3.
The real scaled Jacobi polynomial has its genuine explicit derivative.
Its embedded real slope is exactly its actual complex derivative, and
the derivative Mehler--Heine theorem gives the actual Bessel slope limit.
Source: polynomial differentiation, the complex-to-real chain rule and the proved compact-uniform derivative limit.
Use: finite Stieltjes transforms are the actual logarithmic derivatives of the same finite functions.
-/
namespace jacobi.Jacobi
noncomputable section
open Complex Polynomial Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The literal real derivative of the actual squared-edge Jacobi polynomial.
Use: finite Stieltjes transforms are the actual logarithmic derivatives of the same finite functions.
Article: jacobi, Lemma 1.3.
-/
def scaledRealSlope (a b : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (shiftedPolynomial a b n).derivative.eval (x/(4*(n:ℝ)^2))/(4*(n:ℝ)^2)

/-- The declared finite scaled real slope is the actual ordinary derivative.
Use: supplies the genuine real logarithmic derivative in the finite-to-infinite Stieltjes limit.
Article: jacobi, Lemma 1.3.
Proof: use the actual shifted polynomial identity, its community
polynomial derivative and the literal affine scaling chain rule. -/
theorem scaledReal_hasDerivAt (a b : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt (scaledReal a b n) (scaledRealSlope a b n x) x := by
  -- Compose the actual polynomial derivative with the exact affine spectral scaling.
  have harg := (hasDerivAt_id x).div_const (4*(n:ℝ)^2)
  have h := ((shiftedPolynomial a b n).hasDerivAt (x/(4*(n:ℝ)^2))).comp x harg
  have he : scaledReal a b n=fun t => (shiftedPolynomial a b n).eval (t/(4*(n:ℝ)^2)) :=
    funext fun t => scaledReal_eq_shifted a b t n
  rw [he]
  convert h using 1
  · rfl
  · dsimp [scaledRealSlope]
    ring

/-- The real scaled Jacobi function embedded in the complex field is the exact original complex finite function on the real axis.
Use: identifies real and complex actual derivatives before taking their limits.
Article: jacobi, Lemma 1.3.
Proof: reality identifies the real restriction with the original value;
the real-to-complex affine scaling casts preserve the original argument exactly. -/
theorem scaledReal_complex (a b x : ℝ) (n : ℕ) :
    (scaledReal a b n x:ℂ)=normalized (a:ℂ) (b:ℂ) n (1-(x:ℂ)/(2*(n:ℂ)^2)) := by
  have h := Complex.conj_eq_iff_re.mp (normalized_conj a b (1-x/(2*(n:ℝ)^2)) n)
  change (scaledReal a b n x:ℂ)=normalized (a:ℂ) (b:ℂ) n ((1-x/(2*(n:ℝ)^2):ℝ):ℂ) at h
  convert h using 1
  push_cast
  rfl

/-- The actual real scaled slope, embedded in the complex field, is the genuine complex derivative of the finite Mehler--Heine function.
Use: the community complex derivative convergence applies to the literal real polynomial logarithmic derivatives.
Article: jacobi, Lemma 1.3.
Proof: the embedded real function equals the original complex function
on real inputs. Their actual real-parameter derivatives are unique;
restriction of the genuine complex derivative gives the same derivative. -/
theorem scaledRealSlope_complex (a b x : ℝ) (n : ℕ) :
    (scaledRealSlope a b n x:ℂ)=
      deriv (fun z : ℂ => normalized (a:ℂ) (b:ℂ) n (1-z/(2*(n:ℂ)^2))) (x:ℂ) := by
  -- The two differentiated real-parameter functions are genuinely equal everywhere.
  have he : (fun t : ℝ => (scaledReal a b n t:ℂ))=
      fun t : ℝ => normalized (a:ℂ) (b:ℂ) n (1-(t:ℂ)/(2*(n:ℂ)^2)) :=
    funext fun t => scaledReal_complex a b t n
  have hR := (scaledReal_hasDerivAt a b n x).ofReal_comp
  rw [he] at hR
  have harg : DifferentiableAt ℂ (fun z : ℂ => 1-z/(2*(n:ℂ)^2)) (x:ℂ) := by fun_prop
  have hC := ((normalized_analytic (a:ℂ) (b:ℂ) n (1-(x:ℂ)/(2*(n:ℂ)^2))).differentiableAt.comp (x:ℂ) harg).hasDerivAt.comp_ofReal
  exact hR.unique hC

/-- The actual real scaled Jacobi slopes converge to the actual real Bessel slope at every real spectral point.
Use: identifies limits of finite Stieltjes transforms with the original Bessel logarithmic derivative.
Article: jacobi, Lemma 1.3.
Proof: specialize the proved locally uniform complex derivative limit
at the given real point, take real parts and use the exact real-complex derivative identity. -/
theorem scaledRealSlope_tendsto {a b : ℝ} (ha : -1<a) (x : ℝ) :
    Tendsto (fun n : ℕ => scaledRealSlope a b n x) atTop (𝓝 (jacobi.Bessel.realSlope a x)) := by
  have h := (tendstoLocallyUniformlyOn_univ.mpr
    (mehler_heine_deriv_locallyUniform (a := (a:ℂ)) (b := (b:ℂ)) (by simpa using ha))).tendsto_at (mem_univ (x:ℂ))
  have hRe := Complex.continuous_re.continuousAt.tendsto.comp h
  have he (n : ℕ) : (deriv (fun z : ℂ => normalized (a:ℂ) (b:ℂ) n (1-z/(2*(n:ℂ)^2))) (x:ℂ)).re=
      scaledRealSlope a b n x := by rw [← scaledRealSlope_complex,Complex.ofReal_re]
  simpa only [Function.comp_def,he,jacobi.Bessel.realSlope] using hRe

end
end jacobi.Jacobi
