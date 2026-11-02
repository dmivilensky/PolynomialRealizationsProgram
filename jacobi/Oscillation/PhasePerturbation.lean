import jacobi.Oscillation.PhaseZeros
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
Article: jacobi, Proposition B.1.
A linear barrier bounds the difference of two genuine inverse-square
phases under a small bounded perturbation. Starting beyond a fixed
radius makes the inverse-square Lipschitz contribution smaller than the
barrier slope. Thus the estimate grows linearly, without an exponential
loss on intervals whose length grows with the Jacobi degree.
Use: controls the actual inverse-square phase perturbation in the uniform Jacobi zero proof.
-/
namespace jacobi.Oscillation
noncomputable section
open Real Set
set_option backward.isDefEq.respectTransparency false

/-- Squared sine is globally Lipschitz with the explicit constant two.
Use: controls the actual inverse-square phase perturbation in the uniform Jacobi zero proof.
Article: jacobi, Proposition B.1.
Proof: factor the difference of squares, bound the sine sum by two, and use the community sine Lipschitz inequality. -/
theorem abs_sin_sq_sub_le (u v : ℝ) : |sin u^2-sin v^2|≤2*|u-v| := by
  rw [show sin u^2-sin v^2=(sin u-sin v)*(sin u+sin v) by ring,abs_mul]
  have hh : |sin u+sin v|≤2 := (abs_add_le _ _).trans (by linarith [Real.abs_sin_le_one u,Real.abs_sin_le_one v])
  nlinarith [mul_le_mul (Real.abs_sin_sub_sin_le u v) hh (abs_nonneg _) (abs_nonneg _)]

/-- A small bounded potential perturbation changes the genuine ordinary phase by at most a linear barrier, uniformly on arbitrarily long intervals.
Use: supplies the no-logarithm quantitative phase control for Proposition B.1, without assuming an asymptotic phase estimate.
Article: jacobi, Proposition B.1.
Proof: subtract the two true phase equations and use the global sine-square
Lipschitz bound. At contact with B*epsilon*x the inverse-square contribution
is at most B*epsilon/2; the perturbation is strictly smaller than the
remaining barrier slope. Apply the community continuous fencing theorem. -/
theorem phase_linear_perturbation {f g e : ℝ → ℝ} {c epsilon B a b : ℝ}
    (ha : 0<a) (hlarge : 4*|c|≤a) (heps : 0<epsilon) (hB : 2<B)
    (hf : ∀ x∈Icc a b,HasDerivAt f (1+(c/x^2+e x)*sin (f x)^2) x)
    (hg : ∀ x∈Icc a b,HasDerivAt g (1+c/x^2*sin (g x)^2) x)
    (he : ∀ x∈Icc a b,|e x|≤epsilon)
    (hinit : |f a-g a|≤B*epsilon*a) :
    ∀ x∈Icc a b,|f x-g x|≤B*epsilon*x := by
  -- A growing linear comparison function controls the actual phase difference; a constant-coefficient Gronwall estimate would lose uniformity here.
  let d := fun x => f x-g x
  let d' := fun x => (c/x^2)*(sin (f x)^2-sin (g x)^2)+e x*sin (f x)^2
  have hd : ∀ x∈Icc a b,HasDerivAt d (d' x) x := by
    intro x hx
    convert (hf x hx).sub (hg x hx) using 1
    dsimp [d']
    ring
  have hcont : ContinuousOn d (Icc a b) := fun x hx => (hd x hx).continuousAt.continuousWithinAt
  have hbder : ∀ x : ℝ,HasDerivAt (fun t => B*epsilon*t) (B*epsilon) x :=
    fun x => by simpa only [id_eq,mul_one] using (hasDerivAt_id x).const_mul (B*epsilon)
  have h := image_norm_le_of_norm_deriv_right_lt_deriv_boundary' hcont
    (fun x hx => (hd x ⟨hx.1,hx.2.le⟩).hasDerivWithinAt)
    (B := fun x => B*epsilon*x) (B' := fun _ => B*epsilon)
    (by simpa only [Real.norm_eq_abs] using hinit)
    (fun x _ => (hbder x).continuousAt.continuousWithinAt)
    (fun x _ => (hbder x).hasDerivWithinAt) (by
      intro x hx hcontact
      have hx' : x∈Icc a b := ⟨hx.1,hx.2.le⟩
      have hxp : 0<x := ha.trans_le hx.1
      have hcx : 4*|c|≤x := hlarge.trans hx.1
      have hsin : sin (f x)^2≤1 := by nlinarith [Real.sin_sq_add_cos_sq (f x),sq_nonneg (cos (f x))]
      have hdf : |d' x|≤(|c|/x^2)*(2*|d x|)+epsilon := by
        dsimp only [d']
        calc
          _ ≤ |c/x^2*(sin (f x)^2-sin (g x)^2)|+|e x*sin (f x)^2| := abs_add_le _ _
          _ ≤ (|c|/x^2)*(2*|d x|)+epsilon := by
            rw [abs_mul,abs_div,abs_of_pos (by positivity : 0<x^2),abs_mul,
              abs_of_nonneg (sq_nonneg (sin (f x)))]
            exact add_le_add (mul_le_mul_of_nonneg_left (abs_sin_sq_sub_le _ _) (by positivity))
              ((mul_le_mul (he x hx') hsin (sq_nonneg _) (by positivity)).trans_eq (mul_one _))
      rw [Real.norm_eq_abs] at hcontact ⊢
      rw [hcontact] at hdf
      have hh : (|c|/x^2)*(2*(B*epsilon*x))≤B*epsilon/2 := by
        apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
        field_simp [hxp.ne']
        nlinarith [mul_nonneg (show 0≤B*epsilon by positivity) (show 0≤x-4*|c| by linarith)]
      linarith [mul_lt_mul_of_pos_right hB heps])
  intro x hx
  simpa only [Real.norm_eq_abs] using h hx

end
end jacobi.Oscillation
