import jacobi.Jacobi.LiouvilleEquation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
Article: jacobi, Appendix C.1 (selected endpoint branch).
The apparent singularity of 1/theta-cot(theta/2)/2 is removed using the
actual analytic divided difference of sinc-cos. This supplies the genuine
regular primitive at the singular endpoint, rather than a regularity premise.
Source: analytic divided differences and the sine/cosine identities.
Use: constructs the genuine removable endpoint in the Jacobi comparison potential.
-/
namespace jacobi.Jacobi
noncomputable section
open Real Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Analytic divided differences retain analyticity at their center and away from it.
Use: constructs the genuine removable endpoint in the Jacobi comparison potential.
Article: jacobi, Appendix C.1 (selected endpoint branch).
Source: the community shifted Taylor-series theorem for dslope.
Proof: at zero shift the actual convergent power series. Elsewhere use the
ordinary quotient formula on a neighborhood avoiding zero. -/
theorem analytic_dslope_zero {f : ℝ → ℝ} (hf : ∀ x,AnalyticAt ℝ f x) (x : ℝ) :
    AnalyticAt ℝ (dslope f 0) x := by
  -- Analyticity is proved for the actual divided difference, including its prescribed derivative value at zero.
  by_cases hx : x=0
  · subst x
    obtain ⟨p,hp⟩ := hf 0
    exact ⟨p.fslope,hp.has_fpower_series_dslope_fslope⟩
  · have hq : AnalyticAt ℝ (fun t : ℝ => (f t-f 0)/t) x :=
      ((hf x).sub analyticAt_const).div analyticAt_id hx
    apply hq.congr
    filter_upwards [eventually_ne_nhds hx] with t ht
    rw [dslope_of_ne _ ht]
    simp only [slope,vsub_eq_sub,sub_zero,smul_eq_mul,div_eq_mul_inv,mul_comm]

/-- The actual sinc function is real analytic at every real point.
Use: the removable cotangent primitive is built from genuine analytic special functions.
Article: jacobi, Proposition B.1.
Proof: sinc is exactly the analytic divided difference of the actual sine function. -/
theorem sinc_analytic (x : ℝ) : AnalyticAt ℝ Real.sinc x := by
  rw [Real.sinc_eq_dslope]
  exact analytic_dslope_zero (fun _ => Real.analyticAt_sin) x

/-- An even differentiable function has zero actual derivative at the origin.
Use: fixes the central value of the removable cotangent primitive without an assumed Taylor coefficient.
Article: jacobi, Proposition B.1.
Source: the elementary derivative parity rule.
Proof: compose its actual derivative with negation and use evenness and uniqueness of the ordinary derivative. -/
theorem even_derivative_zero {f : ℝ → ℝ} (hf : DifferentiableAt ℝ f 0)
    (he : ∀ x,f (-x)=f x) : deriv f 0=0 := by
  have hd : HasDerivAt f (deriv f 0) (-0:ℝ) := by simpa only [neg_zero] using hf.hasDerivAt
  have hn := hd.comp 0 (hasDerivAt_neg (0:ℝ))
  have heq : (fun x : ℝ => f (-x))=f := funext he
  change HasDerivAt (fun x : ℝ => f (-x)) (deriv f 0*(-1)) 0 at hn
  rw [heq] at hn
  have hh := hn.unique hf.hasDerivAt
  linarith

/-- The literal numerator sinc-cos in the regular cotangent primitive.
Use: one analytic divided difference removes its actual vanishing endpoint value.
Article: jacobi, Proposition B.1.
-/
def cotangentNumerator (x : ℝ) : ℝ := sinc x-cos x

/-- The actual removable cotangent primitive, with its analytic endpoint value.
Use: the source's residual potential is its genuine ordinary derivative and has a uniform C1 bound.
Article: jacobi, Proposition B.1.
-/
def regularCotangent (t : ℝ) : ℝ :=
  dslope cotangentNumerator 0 (t/2)/(2*sinc (t/2))

/-- The original sinc-cos numerator is analytic everywhere.
Use: analyticity of its actual divided difference supplies all endpoint derivatives of the comparison remainder.
Article: jacobi, Proposition B.1.
Proof: both original functions are analytic, and subtraction preserves analyticity. -/
theorem cotangentNumerator_analytic (x : ℝ) : AnalyticAt ℝ cotangentNumerator x :=
  (sinc_analytic x).sub Real.analyticAt_cos

/-- The removable cotangent primitive has the exact endpoint value zero.
Use: the actual primitive of the Liouville remainder starts at zero, as required by the comparison integral.
Article: jacobi, Proposition B.1.
Proof: sinc-cos is even and analytic, so its genuine central derivative,
which defines the divided difference at zero, vanishes. -/
theorem regularCotangent_zero : regularCotangent 0=0 := by
  have he : ∀ x,cotangentNumerator (-x)=cotangentNumerator x := by
    intro x
    simp only [cotangentNumerator,sinc_neg,cos_neg]
  have hd := even_derivative_zero (cotangentNumerator_analytic 0).differentiableAt he
  simp only [regularCotangent,zero_div,dslope_same,hd,sinc_zero,mul_one]

/-- Sinc has no zero on the actual interior interval between its first sine zeros.
Use: the regular cotangent primitive is analytic throughout the source comparison interval, including zero.
Article: jacobi, Proposition B.1.
Proof: at zero its actual value is one; at either sign the original sine
and argument have matching nonzero signs before the first sine zero. -/
theorem sinc_ne_zero_between {x : ℝ} (hx : x∈Ioo (-Real.pi) Real.pi) : sinc x≠0 := by
  -- Both sides of the removable endpoint are handled on their genuine real branches.
  by_cases h0 : x=0
  · simpa only [h0,sinc_zero] using (one_ne_zero : (1:ℝ)≠0)
  · rw [sinc_of_ne_zero h0]
    apply div_ne_zero _ h0
    rcases lt_or_gt_of_ne h0 with hn | hp
    · exact (Real.sin_neg_of_neg_of_neg_pi_lt hn hx.1).ne
    · exact (Real.sin_pos_of_pos_of_lt_pi hp hx.2).ne'

/-- The actual removable cotangent primitive is analytic throughout (-2*pi,2*pi).
Use: its genuine first two derivatives are continuous and bounded on the compact source comparison interval.
Article: jacobi, Proposition B.1.
Proof: its divided-difference numerator is analytic everywhere. The actual
sinc denominator is nonzero on this whole interval; composition and quotient preserve analyticity. -/
theorem regularCotangent_analytic {t : ℝ} (ht : t∈Ioo (-2*Real.pi) (2*Real.pi)) :
    AnalyticAt ℝ regularCotangent t := by
  have hi : AnalyticAt ℝ (fun x : ℝ => x/2) t := analyticAt_id.div_const
  exact ((analytic_dslope_zero cotangentNumerator_analytic (t/2)).comp (f := fun x : ℝ => x/2) hi).div
    ((analyticAt_const.mul ((sinc_analytic (t/2)).comp (f := fun x : ℝ => x/2) hi)))
    (mul_ne_zero (by norm_num) (sinc_ne_zero_between ⟨by linarith [ht.1],by linarith [ht.2]⟩))

/-- Away from zero the analytic regularization is precisely the source's original cotangent expression.
Use: identifies the genuinely smooth comparison primitive with the printed singular formula on its actual domain.
Article: jacobi, Proposition B.1.
Proof: expand the genuine divided difference and sinc, cancel only the
actual nonzero argument and sine, and simplify ordinary field algebra. -/
theorem regularCotangent_eq {t : ℝ} (ht : t∈Ioo 0 Real.pi) :
    regularCotangent t=1/t-(1/2)*(cos (t/2)/sin (t/2)) := by
  -- The endpoint extension is not used to cancel a vanishing denominator.
  have hh : t/2≠0 := ne_of_gt (by linarith [ht.1])
  have hs := (half_angle_positive ht).1
  rw [regularCotangent,dslope_of_ne _ hh]
  simp only [slope,vsub_eq_sub,cotangentNumerator,sinc_zero,cos_zero,sub_self,sub_zero,smul_eq_mul,
    sinc_of_ne_zero hh]
  field_simp [hh,ht.1.ne',hs.ne']

end
end jacobi.Jacobi
