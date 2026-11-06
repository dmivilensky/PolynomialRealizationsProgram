import nesterov.IQC.PolynomialSymbols
import nesterov.Attainment.NormalizedKernels
import Mathlib.Analysis.RCLike.Lemmas

/-! Entire complex-frequency extensions of the actual real-polynomial gap
and skew functions. They retain zeros of either amplitude. -/
noncomputable section
namespace nesterov.Attainment

def amplitude (q : Polynomial ℝ) (t : ℝ) (z : ℂ) : ℂ :=
  (q.map Complex.ofRealHom).eval (Complex.exp ((t : ℂ)+z*Complex.I))

def gapEntire (u p : Polynomial ℝ) (t : ℝ) (z : ℂ) : ℂ :=
  amplitude u t z * amplitude u t (-z) - amplitude p t z * amplitude p t (-z)

def skewEntire (u p : Polynomial ℝ) (t : ℝ) (z : ℂ) : ℂ :=
  (amplitude p t z * amplitude u t (-z) - amplitude p t (-z) * amplitude u t z) /
    (2*Complex.I)

theorem differentiable_amplitude (q : Polynomial ℝ) (t : ℝ) :
    Differentiable ℂ (amplitude q t) := by unfold amplitude; fun_prop

theorem differentiable_gapEntire (u p : Polynomial ℝ) (t : ℝ) :
    Differentiable ℂ (gapEntire u p t) := by unfold gapEntire amplitude; fun_prop

theorem differentiable_skewEntire (u p : Polynomial ℝ) (t : ℝ) :
    Differentiable ℂ (skewEntire u p t) := by unfold skewEntire amplitude; fun_prop

theorem amplitude_neg_real (q : Polynomial ℝ) (t ω : ℝ) :
    amplitude q t (-(ω : ℂ)) = star (amplitude q t (ω : ℂ)) := by
  have hconj : Complex.exp ((t : ℂ)-(ω : ℂ)*Complex.I) =
      star (Complex.exp ((t : ℂ)+(ω : ℂ)*Complex.I)) := by
    rw [Complex.star_def, ← Complex.exp_conj]
    congr 1
    simp [sub_eq_add_neg]
  change (q.map Complex.ofRealHom).eval (Complex.exp ((t : ℂ)+(-(ω : ℂ))*Complex.I)) = _
  rw [show (t : ℂ)+(-(ω : ℂ))*Complex.I = (t : ℂ)-(ω : ℂ)*Complex.I by ring, hconj]
  have hhom : Complex.ofRealHom = algebraMap ℝ ℂ := by ext r; rfl
  have hh := Polynomial.aeval_conj q (Complex.exp ((t : ℂ)+(ω : ℂ)*Complex.I)) (K := ℂ)
  simpa only [amplitude, Polynomial.aeval_def, Polynomial.eval_map, Complex.star_def, hhom] using hh

theorem gap_complex_identity (u p : ℂ) :
    u*star u-p*star p = ((Complex.normSq u-Complex.normSq p : ℝ) : ℂ) := by
  apply Complex.ext <;>
    simp only [Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,
      Complex.star_def,Complex.conj_re,Complex.conj_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.normSq_apply] <;> ring

theorem skew_complex_identity (u p : ℂ) :
    (p*star u-star p*u)/(2*Complex.I) = ((p*star u).im : ℂ) := by
  apply (div_eq_iff (by norm_num : (2*Complex.I : ℂ) ≠ 0)).mpr
  apply Complex.ext <;>
    simp only [Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,
      Complex.star_def,Complex.conj_re,Complex.conj_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im] <;> norm_num
  all_goals ring

theorem gapEntire_real (u p : Polynomial ℝ) (t ω : ℝ) :
    gapEntire u p t (ω : ℂ) =
      ((Complex.normSq (amplitude u t ω)-Complex.normSq (amplitude p t ω) : ℝ) : ℂ) := by
  rw [gapEntire, amplitude_neg_real, amplitude_neg_real]
  exact gap_complex_identity _ _

theorem skewEntire_real (u p : Polynomial ℝ) (t ω : ℝ) :
    skewEntire u p t (ω : ℂ) = ((amplitude p t ω*star (amplitude u t ω)).im : ℂ) := by
  rw [skewEntire, amplitude_neg_real, amplitude_neg_real]
  exact skew_complex_identity _ _

/-- Entire extensions evaluated on the same compact parameter-frequency domain. -/
def gapEntireMap (u p : Polynomial ℝ) (lo hi σ : ℝ) : C(LagDomain lo hi,ℂ) where
  toFun q := gapEntire u p (σ*q.1) q.2
  continuous_toFun := by unfold gapEntire amplitude; fun_prop

def skewEntireMap (u p : Polynomial ℝ) (lo hi σ : ℝ) : C(LagDomain lo hi,ℂ) where
  toFun q := skewEntire u p (σ*q.1) q.2
  continuous_toFun := by unfold skewEntire amplitude; fun_prop

end nesterov.Attainment
