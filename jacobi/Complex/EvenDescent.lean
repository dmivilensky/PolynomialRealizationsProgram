import jacobi.Reference.Solutions
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.SqrtDeriv

/-!
Article: jacobi, Appendix C.2 (exact parity splitting).
An even entire frequency function descends to an entire energy function.
The square-root branch causes no singularity: away from zero the square
map is locally invertible, and at zero its apparent singularity is removable.
Source: the analytic inverse function and removable singularity theorems.
Use: eliminates every choice of square-root branch in even_entire_descent and the actual Gamma characteristic below.
-/
namespace jacobi.Complex
noncomputable section
open _root_.Complex Set Filter
open scoped Topology

/-- Equal complex squares have equal values under an even function.
Use: eliminates every choice of square-root branch in even_entire_descent and the actual Gamma characteristic below.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: factor the difference of squares; the roots are equal or opposite. -/
theorem even_eq_of_square_eq {f : ℂ → ℂ} (he : ∀ w,f (-w)=f w)
    {u v : ℂ} (h : u^2=v^2) : f u=f v := by
  have hp : (u-v)*(u+v)=0 := by linear_combination h
  rcases mul_eq_zero.mp hp with h | h
  · rw [sub_eq_zero.mp h]
  · rw [eq_neg_of_add_eq_zero_left h,he]

/-- The actual square-root composition of an even entire function is entire, including its branch point.
Use: proves entire energy dependence of the literal reciprocal-Gamma characteristic without postulating a continuation or excluding z=c_0.
Article: jacobi, Appendix C.2 (norming ratios).
Proof: composing the descended function with w^2 gives the original
entire function. The analytic inverse function theorem therefore applies
at every nonzero root. At zero the square root is continuous and the
removable singularity theorem applies to this same actual function. -/
theorem even_entire_descent {f : ℂ → ℂ} (hf : ∀ w,AnalyticAt ℂ f w)
    (he : ∀ w,f (-w)=f w) (z : ℂ) :
    AnalyticAt ℂ (fun z => f (_root_.Complex.sqrt z)) z := by
  -- Local invertibility avoids differentiating the globally discontinuous square-root branch.
  have hcomp : (fun w : ℂ => f (_root_.Complex.sqrt (w^2)))=f :=
    funext fun w => even_eq_of_square_eq he (jacobi.Reference.frequency_square (w^2))
  have haway (z : ℂ) (hz : z≠0) : AnalyticAt ℂ (fun z => f (_root_.Complex.sqrt z)) z := by
    let w := _root_.Complex.sqrt z
    have hw : w≠0 := by
      intro h
      have hs := jacobi.Reference.frequency_square z
      change w^2=z at hs
      rw [h,zero_pow (by norm_num : (2:ℕ)≠0)] at hs
      exact hz hs.symm
    have hs : HasDerivAt (fun u : ℂ => u^2) (2*w) w := by
      convert! (hasDerivAt_id w).pow 2 using 1
      norm_num
    have ha : AnalyticAt ℂ (fun u : ℂ => u^2) w := analyticAt_id.pow 2
    have hc : AnalyticAt ℂ ((fun z => f (_root_.Complex.sqrt z)) ∘ fun u : ℂ => u^2) w := by
      change AnalyticAt ℂ (fun u : ℂ => f (_root_.Complex.sqrt (u^2))) w
      rw [hcomp]
      exact hf w
    have hh := (analyticAt_comp_iff_of_deriv_ne_zero ha
      (by rw [hs.deriv]; exact mul_ne_zero (by norm_num) hw)).mp hc
    change AnalyticAt ℂ (fun z => f (_root_.Complex.sqrt z)) ((_root_.Complex.sqrt z)^2) at hh
    rwa [jacobi.Reference.frequency_square] at hh
  by_cases hz : z=0
  · subst z
    apply _root_.Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    · filter_upwards [self_mem_nhdsWithin] with w hw using (haway w hw).differentiableAt
    · exact (hf (_root_.Complex.sqrt 0)).continuousAt.comp
        (_root_.Complex.continuousAt_sqrt (Or.inl (by norm_num)))
  · exact haway z hz

end
end jacobi.Complex
