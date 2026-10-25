import polyak.ModeLocking.TwoLag.Contact
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! The local calculus behind the double-contact curvature criterion. -/
noncomputable section
namespace polyak.ModeLocking.TwoLag
open Filter
open scoped Topology

theorem second_mul_at_double_zero {f g : ℝ→ℝ} {u : ℝ}
    (hf : ContDiffAt ℝ 2 f u) (hg : ContDiffAt ℝ 2 g u)
    (h0 : g u=0) (h1 : deriv g u=0) :
    deriv^[2] (fun x=>f x*g x) u=f u*deriv^[2] g u := by
  have h := iteratedDeriv_fun_mul hf hg
  norm_num [Finset.sum_range_succ, h0, h1, iteratedDeriv_zero, iteratedDeriv_one,
    iteratedDeriv_eq_iterate] at h
  exact h

theorem second_cos_comp_at_stationary {g : ℝ→ℝ} {u : ℝ}
    (hg : ContDiffAt ℝ 2 g (Real.cos u)) (h1 : deriv g (Real.cos u)=0) :
    deriv^[2] (fun x=>g (Real.cos x)) u=deriv^[2] g (Real.cos u)*Real.sin u^2 := by
  have h := iteratedDeriv_comp_two hg (Real.contDiff_cos.contDiffAt : ContDiffAt ℝ 2 Real.cos u)
  simpa only [iteratedDeriv_eq_iterate, Real.deriv_cos, h1, zero_mul, add_zero,
    neg_sq, Function.comp_def] using h

/-- The second derivative of a positive factor times a cosine-coordinate
contact has exactly the same sign as the contact's second derivative. -/
theorem second_contact_sign {f g : ℝ→ℝ} {u : ℝ}
    (hf : ContDiffAt ℝ 2 f u) (hg : ContDiffAt ℝ 2 g (Real.cos u))
    (h0 : g (Real.cos u)=0) (h1 : deriv g (Real.cos u)=0)
    (hpos : 0<f u) (hsin : Real.sin u≠0) :
    (deriv^[2] (fun x=>f x*g (Real.cos x)) u<0 ↔ deriv^[2] g (Real.cos u)<0) := by
  have hgcomp : ContDiffAt ℝ 2 (fun x=>g (Real.cos x)) u :=
    hg.comp u Real.contDiff_cos.contDiffAt
  have hfirst : deriv (fun x=>g (Real.cos x)) u=0 := by
    rw [show (fun x=>g (Real.cos x))=g ∘ Real.cos by rfl,
      deriv_comp u (hg.differentiableAt (by norm_num)) Real.differentiableAt_cos, h1, zero_mul]
  rw [second_mul_at_double_zero hf hgcomp h0 hfirst, second_cos_comp_at_stationary hg h1]
  have hp : 0<f u*Real.sin u^2 := mul_pos hpos (sq_pos_of_ne_zero hsin)
  constructor
  · intro h
    have he : f u*(deriv^[2] g (Real.cos u)*Real.sin u^2)=
        (f u*Real.sin u^2)*deriv^[2] g (Real.cos u) := by ring
    rw [he] at h
    exact neg_of_mul_neg_right h hp.le
  · intro h
    have h' := mul_neg_of_pos_of_neg hp h
    nlinarith only [h']

end polyak.ModeLocking.TwoLag
