import jacobi.Reference.Eigenfunctions
import jacobi.Jacobi.Orthogonality
import jacobi.Jacobi.DerivativeIdentity

/-!
Article: jacobi, Lemma C.1.
The actual Jacobi weighted norms satisfy a parameter-shifting recurrence.
Its proof uses the already established genuine singular-weight flux and
the actual polynomial derivative identity. This supplies the exact
reference norms without importing an orthogonal-polynomial norm formula.
Use: evaluates the reference Gegenbauer norming integrals by an exact change of coordinate.
-/
namespace jacobi.Reference
noncomputable section
open Real Set MeasureTheory Polynomial
set_option backward.isDefEq.respectTransparency false

/-- The genuine endpoint-normalized Jacobi squared norm for its literal shifted weight.
Use: evaluates the reference Gegenbauer norming integrals by an exact change of coordinate.
Article: jacobi, Lemma C.1.
-/
def jacobiNorm (a b : ℝ) (n : ℕ) : ℝ :=
  ∫ x in (0:ℝ)..1,jacobi.Jacobi.weight a b x*((jacobi.Jacobi.shiftedPolynomial a b n).eval x)^2

/-- Every actual weighted Jacobi norm is strictly positive in the full original parameter range.
Use: normalization of the genuine reference orthogonal system has no zero denominator.
Article: jacobi, Lemma C.1.
Proof: the actual polynomial is nonzero, its square is a nonzero nonnegative polynomial, and the established positive-weight integral theorem applies. -/
theorem jacobiNorm_pos {a b : ℝ} (ha : -1<a) (hb : -1<b) (n : ℕ) : 0<jacobiNorm a b n := by
  let p := jacobi.Jacobi.shiftedPolynomial a b n
  have hp : p≠0 := jacobi.Jacobi.shiftedPolynomial_ne_zero ha hb n
  have h := jacobi.Jacobi.weighted_polynomial_integral_pos ha hb (mul_ne_zero hp hp)
    (fun x _ => by rw [Polynomial.eval_mul]; exact mul_self_nonneg _)
  simpa only [jacobiNorm,Polynomial.eval_mul,pow_two] using h

/-- The genuine Jacobi polynomial energy equals its actual eigenvalue times its actual weighted squared norm.
Use: obtains the exact parameter-shifting norm recurrence without a literature norm assumption.
Article: jacobi, Lemma C.1.
Proof: differentiate flux*p*p'. The genuine polynomial equation makes
its derivative equal flux*(p')^2-lambda*weight*p^2. All terms have proved
convergent integrals and the original continuous flux vanishes at both
singular endpoints, so the fundamental theorem gives the exact identity. -/
theorem jacobi_energy {a b : ℝ} (ha : -1<a) (hb : -1<b) (n : ℕ) :
    (∫ x in (0:ℝ)..1,jacobi.Jacobi.fluxWeight a b x*((jacobi.Jacobi.shiftedPolynomial a b n).derivative.eval x)^2)=
      (n:ℝ)*(n+a+b+1)*jacobiNorm a b n := by
  -- The boundary expression contains the genuine vanishing Jacobi flux; no endpoint differentiability of a singular weight is presumed.
  let p := jacobi.Jacobi.shiftedPolynomial a b n
  let l : ℝ := (n:ℝ)*(n+a+b+1)
  let W := fun x => jacobi.Jacobi.fluxWeight a b x*p.eval x*p.derivative.eval x
  have hflux := jacobi.Jacobi.fluxWeight_properties ha hb
  have hcont : Continuous W := (hflux.1.mul p.continuous).mul p.derivative.continuous
  have hi1 : IntervalIntegrable (fun x => jacobi.Jacobi.fluxWeight a b x*(p.derivative.eval x)^2) volume 0 1 :=
    jacobi.Jacobi.weight_mul_integrable (by linarith : -1<a+1) (by linarith : -1<b+1) (p.derivative.continuous.pow 2)
  have hi2 : IntervalIntegrable (fun x => l*(jacobi.Jacobi.weight a b x*(p.eval x)^2)) volume 0 1 :=
    (jacobi.Jacobi.weight_mul_integrable ha hb (p.continuous.pow 2)).const_mul l
  have hI : IntervalIntegrable (fun x => jacobi.Jacobi.fluxWeight a b x*(p.derivative.eval x)^2-
      l*(jacobi.Jacobi.weight a b x*(p.eval x)^2)) volume 0 1 := hi1.sub hi2
  have hd (x : ℝ) (hx : x∈Ioo (0:ℝ) 1) : HasDerivAt W
      (jacobi.Jacobi.fluxWeight a b x*(p.derivative.eval x)^2-l*(jacobi.Jacobi.weight a b x*(p.eval x)^2)) x := by
    have h := ((jacobi.Jacobi.fluxWeight_hasDerivAt a b hx).mul (p.hasDerivAt x)).mul (p.derivative.hasDerivAt x)
    have he := jacobi.Jacobi.shifted_sturm_equation (b := b) ha n x
    change jacobi.Jacobi.sturm a b p x+l*p.eval x=0 at he
    convert h using 1
    rw [jacobi.Jacobi.fluxWeight_eq a b hx]
    dsimp [jacobi.Jacobi.sturm] at he
    simp only [Pi.mul_apply,jacobi.Jacobi.fluxWeight_eq a b hx]
    linear_combination - jacobi.Jacobi.weight a b x*p.eval x*he
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by norm_num : (0:ℝ)≤1) hcont.continuousOn hd hI
  have hzero : W 1-W 0=0 := by dsimp [W]; rw [hflux.2.1,hflux.2.2]; ring
  rw [hzero,intervalIntegral.integral_sub hi1 hi2,intervalIntegral.integral_const_mul] at h
  exact sub_eq_zero.mp h

/-- The exact genuine Jacobi norms satisfy their full parameter-shifting recurrence.
Use: evaluates every source reference squared norm from the convergent degree-zero Beta integral.
Article: jacobi, Lemma C.1.
Proof: the actual derivative is a fixed multiple of the genuine lower-degree polynomial with both parameters shifted by one. Substitute it into the proved Sturm energy identity and cancel the actual positive eigenvalue. -/
theorem jacobiNorm_recurrence {a b : ℝ} (ha : -1<a) (hb : -1<b) (n : ℕ) :
    jacobiNorm a b (n+1)=((n:ℝ)+1)*(n+a+b+2)/(a+1)^2*jacobiNorm (a+1) (b+1) n := by
  -- Every norm is its original convergent integral; cancellation uses the proved full parameter range.
  let l : ℝ := ((n:ℝ)+1)*(n+a+b+2)
  have hl : 0<l := mul_pos (by positivity) (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hA : a+1≠0 := by linarith
  have he := jacobi_energy ha hb (n+1)
  have hid : (fun x => jacobi.Jacobi.fluxWeight a b x*((jacobi.Jacobi.shiftedPolynomial a b (n+1)).derivative.eval x)^2)=
      fun x => (l/(a+1))^2*(jacobi.Jacobi.weight (a+1) (b+1) x*((jacobi.Jacobi.shiftedPolynomial (a+1) (b+1) n).eval x)^2) := by
    funext x
    rw [jacobi.Jacobi.shiftedPolynomial_derivative ha,Polynomial.eval_mul,Polynomial.eval_C]
    dsimp [jacobi.Jacobi.fluxWeight,jacobi.Jacobi.weight,l]
    ring
  rw [hid,intervalIntegral.integral_const_mul] at he
  have hlit : ((n+1:ℕ):ℝ)*(((n+1:ℕ):ℝ)+a+b+1)=l := by dsimp [l]; push_cast; ring
  rw [hlit] at he
  change (l/(a+1))^2*jacobiNorm (a+1) (b+1) n=l*jacobiNorm a b (n+1) at he
  change jacobiNorm a b (n+1)=l/(a+1)^2*jacobiNorm (a+1) (b+1) n
  apply (mul_left_cancel₀ hl.ne')
  field_simp [hA] at he ⊢
  nlinarith [he]

end
end jacobi.Reference
