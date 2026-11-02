import jacobi.Bessel.PoissonNegative
import jacobi.Bessel.Contiguous

/-!
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
The leading coefficient belongs to the original normalized entire Bessel
function throughout alpha>-1. The actual Poisson integral gives it for
alpha>-1/2; the proved genuine three-order recurrence extends it to the
full article range without a presumed asymptotic expansion.
Use: supplies both raised orders in normalized_negative_leading and hence the full-order Bessel characteristic normalization.
-/
namespace jacobi.Bessel
noncomputable section
open Real Set MeasureTheory Filter _root_.Complex
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual original normalized Bessel function has its exact leading negative-axis coefficient throughout the Poisson order range.
Use: supplies both raised orders in normalized_negative_leading and hence the full-order Bessel characteristic normalization.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Source: Poisson's integral and Watson's lemma, both proved here for the original functions.
Proof: multiply the exact endpoint limit for the original Poisson--cosh integral by its genuine normalization. Its Gamma(alpha+1/2) factor cancels exactly. -/
theorem normalized_negative_leading_poisson {a : ℝ} (ha : -(1/2:ℝ)<a) :
    Tendsto (fun y : ℝ => y^(a+1/2)*Real.exp (-y)*(normalized (a:ℂ) ((-y^2:ℝ):ℂ)).re)
      atTop (𝓝 (Real.Gamma (a+1)*(2:ℝ)^(a-1/2)/Real.sqrt Real.pi)) := by
  -- The constant comes from the actual integral normalization, rather than a new normalization of the Bessel function.
  let C := 2*Real.Gamma (a+1)/(Real.sqrt Real.pi*Real.Gamma (a+1/2))
  have hh := (poisson_cosh_leading ha).const_mul C
  have he : C*(Real.Gamma (a+1/2)*(2:ℝ)^(a-1/2)/2)=
      Real.Gamma (a+1)*(2:ℝ)^(a-1/2)/Real.sqrt Real.pi := by
    dsimp [C]
    field_simp [(Real.Gamma_pos_of_pos (show 0<(2*a+1)/2 by linarith)).ne']
  rw [he] at hh
  apply hh.congr'
  filter_upwards with y
  rw [poisson_negative_integral ha]
  dsimp [C]
  ring

/-- The actual real negative-axis Bessel values satisfy the exact positive three-order recurrence.
Use: transfers the two proved raised-order endpoint limits to the whole original order range in normalized_negative_leading.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Source: the genuine Bessel order recurrence, proved in Contiguous.
Proof: specialize the actual entire contiguous identity to -y^2 and take its real part; its scalar coefficient is real. -/
theorem normalized_negative_contiguous {a : ℝ} (ha : -1<a) (y : ℝ) :
    (normalized (a:ℂ) ((-y^2:ℝ):ℂ)).re=
      (normalized ((a+1:ℝ):ℂ) ((-y^2:ℝ):ℂ)).re+
        y^2/(4*(a+1)*(a+2))*(normalized ((a+2:ℝ):ℂ) ((-y^2:ℝ):ℂ)).re := by
  have hh := normalized_contiguous (a := (a:ℂ)) (by simpa only [Complex.ofReal_re] using ha) ((-y^2:ℝ):ℂ)
  have hc : ((-y^2:ℝ):ℂ)/(4*((a:ℂ)+1)*((a:ℂ)+2))=
      ((-y^2/(4*(a+1)*(a+2)):ℝ):ℂ) := by push_cast; rfl
  rw [hc] at hh
  have he := congrArg Complex.re hh
  simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at he
  push_cast at he ⊢
  linear_combination he

/-- The actual normalized entire Bessel function has the exact original negative-axis leading coefficient for every order alpha>-1.
Use: proves the fully normalized Bessel characteristic asymptotic and removes the Poisson integral's temporary order restriction.
Article: jacobi, Appendix C.2 (norming ratios).
Source: the original Bessel contiguous recurrence, Poisson's integral and Watson's endpoint lemma, all proved here.
Proof: both orders alpha+1 and alpha+2 lie in the genuine Poisson
range. After the original three-order recurrence is rescaled, the
first term has an extra factor 1/y and tends to zero. The second
has the exact full-order coefficient by Euler's Gamma recurrence
and the actual two-power shift; no asymptotic remainder is assumed. -/
theorem normalized_negative_leading {a : ℝ} (ha : -1<a) :
    Tendsto (fun y : ℝ => y^(a+1/2)*Real.exp (-y)*(normalized (a:ℂ) ((-y^2:ℝ):ℂ)).re)
      atTop (𝓝 (Real.Gamma (a+1)*(2:ℝ)^(a-1/2)/Real.sqrt Real.pi)) := by
  -- Apply the actual Poisson result only at two raised admissible orders; the original order is recovered by a proved entire identity.
  have h1 := normalized_negative_leading_poisson (a := a+1) (by linarith)
  have h2 := normalized_negative_leading_poisson (a := a+2) (by linarith)
  have hlim := (h1.div_atTop tendsto_id).add (h2.const_mul (1/(4*(a+1)*(a+2))))
  have hc : 1/(4*(a+1)*(a+2))*(Real.Gamma (a+2+1)*(2:ℝ)^(a+2-1/2)/Real.sqrt Real.pi)=
      Real.Gamma (a+1)*(2:ℝ)^(a-1/2)/Real.sqrt Real.pi := by
    rw [Real.Gamma_add_one (s := a+2) (by linarith),
      show a+2=a+1+1 by ring,Real.Gamma_add_one (s := a+1) (by linarith),
      show a+1+1-1/2=(a-1/2)+2 by ring,Real.rpow_add (by norm_num : (0:ℝ)<2),Real.rpow_two]
    norm_num
    field_simp [show a+1≠0 by linarith,show a+1+1≠0 by linarith]
  simp only [zero_add,hc] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy
  have hp1 : y^(a+1+1/2)=y^(a+1/2)*y := by
    rw [← Real.rpow_add_one hy.ne']
    congr 1
    ring
  have hp2 : y^(a+2+1/2)=y^(a+1/2)*y^2 := by
    rw [← Real.rpow_two y,← Real.rpow_add hy]
    congr 1
    ring
  rw [normalized_negative_contiguous ha,hp1,hp2]
  dsimp only [id_eq]
  field_simp [hy.ne']

end
end jacobi.Bessel
