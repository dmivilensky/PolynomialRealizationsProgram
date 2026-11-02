import krylov.OneGradient.RelativeUniformMinimax
import krylov.Correction.SharpConstant
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(c), arbitrary-method known-base obstruction.
Use: derive the original c*w' second-order lower bound on actual one-gradient
methods, allowing their policies to depend on the shrinking known-prior radius.
Source: the proved exact whole-relative-prior physical minimax and genuine
constant-prefix matrix scenarios; no CG-consistency or smooth policy premise.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix Filter Topology krylov.Reference krylov.Methods krylov.Secant
variable {n : ℕ}

/-- Every genuine uniform second-order guarantee over the shrinking known
relative-base prior must have coefficient at least c times the output weight.
Use: this applies to every source-span-restricted one-gradient method,
including policies calibrated separately for each known radius.
Article: main_krylov, thm:local(c), arbitrary dimension lower bound.
Proof: the actual complete prior-wide minimax on constant physical prefixes
is exactly (c*t)*(w'*t). Cancel the genuine positive t-squared scale. -/
theorem known_base_second_order_lower
    (center : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hcenter : center.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues center hcenter.1 g).card=n+1)
    (c weight t v : ℝ) (hc0 : 0≤c) (hw : 0≤weight) (ht : 0<t)
    (hsmall : c*t<1) (hout : weight*t≤1)
    (method : OneGradientMethod (EuclideanSpace ℝ (Fin (n+1)))) (hm : OneGradientSpanRestricted method)
    (hbound : relativePriorGuarantee center (c*t) g (weight*t) method (v*t^2)) : c*weight≤v := by
  have h := (relative_prior_exact_uniform_minimax center hcenter g hg hc
    (mul_nonneg hc0 ht.le) hsmall (mul_nonneg hw ht.le) hout).2 ⟨method,hm,hbound⟩
  have he : (c*t)*(weight*t)=c*weight*t^2 := by ring
  rw [he] at h
  exact (mul_le_mul_iff_left₀ (sq_pos_of_pos ht)).mp (by simpa only [mul_comm] using h)

/-- Every coefficient below c*w' fails on the original actual physical
scenario class for every genuine one-gradient method.
Use: the obstruction is a true matrix-prior failure, not an inequality
postulated for abstract scalar errors.
Article: main_krylov, thm:local(c).
Proof: otherwise the original genuine prior guarantee would contradict the
proved exact arbitrary-method coefficient lower bound. -/
theorem known_base_smaller_coefficient_impossible
    (center : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hcenter : center.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues center hcenter.1 g).card=n+1)
    (c weight t v : ℝ) (hc0 : 0≤c) (hw : 0≤weight) (ht : 0<t)
    (hsmall : c*t<1) (hout : weight*t≤1) (hv : v<c*weight)
    (method : OneGradientMethod (EuclideanSpace ℝ (Fin (n+1)))) (hm : OneGradientSpanRestricted method) :
    ¬ relativePriorGuarantee center (c*t) g (weight*t) method (v*t^2) := by
  intro hbound
  exact not_le_of_gt hv (known_base_second_order_lower center hcenter g hg hc c weight t v hc0 hw ht
    hsmall hout method hm hbound)

/-- Every coefficient below c*w' has a genuine positive physical
constant-prefix matrix counterexample for each actual source method.
Use: the lower obstruction is witnessed in the original known-base and
unobserved-output budgets, not only in a scalar guarantee predicate.
Article: main_krylov, thm:local(c).
Proof: negate the true full physical prior guarantee at the forbidden
coefficient; the actual relative ball and its strict radius prove positivity
of the resulting real completion through the genuine Schur criterion. -/
theorem known_base_physical_adversary
    (center : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hcenter : center.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues center hcenter.1 g).card=n+1)
    (c weight t v : ℝ) (hc0 : 0≤c) (hw : 0≤weight) (ht : 0<t)
    (hsmall : c*t<1) (hout : weight*t≤1) (hv : v<c*weight)
    (method : OneGradientMethod (EuclideanSpace ℝ (Fin (n+1)))) (hm : OneGradientSpanRestricted method) :
    ∃ (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef) (hga : g≠0)
      (hca : (activeSpectralValues A hA.1 g).card=n+1) (b : ℝ)
      (B : Matrix (Fin (n+1)) (Fin (n+1)) ℝ),
      (lanczosCompletion A hA g hga hca b).PosDef ∧
        relativeBudget center (lanczosCompletion A hA g hga hca b-center)≤c*t ∧ B.IsSymm ∧
          relativeBudget (lanczosCompletion A hA g hga hca b) (B-lanczosCompletion A hA g hga hca b)≤weight*t ∧
            v*t^2<fibreScenarioError A hA g hga hca method b B := by
  have hnot := known_base_smaller_coefficient_impossible center hcenter g hg hc c weight t v
    hc0 hw ht hsmall hout hv method hm
  unfold relativePriorGuarantee at hnot
  push Not at hnot
  obtain ⟨A,hA,hga,hca,b,hprior,B,hB,hbudget,herror⟩ := hnot
  refine ⟨A,hA,hga,hca,b,B,?_,hprior,hB,hbudget,herror⟩
  exact (lanczos_completion_positive_iff A hA g hga hca b).mpr
    (relative_ball_fibre_positive A hA g hga hca center hcenter (mul_nonneg hc0 ht.le) hsmall b hprior)

/-- Above the original RFC sharp-constant threshold, that RFC leading
coefficient cannot be a uniform guarantee of any genuine one-gradient method
on the original shrinking known-base physical scenario class.
Use: gives the source strict large-c leading-coefficient comparison using
RFC's already proved genuine sharp constant, rather than an unspecified bound.
Article: main_krylov, thm:local(c).
Proof: the threshold makes the exact arbitrary-method obstruction strictly
larger than the original RFC coefficient; invoke the proved physical impossibility. -/
theorem known_base_large_radius_obstruction
    (center : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hcenter : center.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues center hcenter.1 g).card=n+1)
    (c W weight t : ℝ) (hc0 : 0≤c) (hw : 0<weight) (ht : 0<t)
    (hsmall : c*t<1) (hout : weight*t≤1)
    (hlarge : krylov.Correction.sharpConstant W weight/weight<c)
    (method : OneGradientMethod (EuclideanSpace ℝ (Fin (n+1)))) (hm : OneGradientSpanRestricted method) :
    ¬ relativePriorGuarantee center (c*t) g (weight*t) method
      (krylov.Correction.sharpConstant W weight*t^2) :=
  known_base_smaller_coefficient_impossible center hcenter g hg hc c weight t _ hc0 hw.le ht hsmall hout
    ((div_lt_iff₀ hw).mp hlarge) method hm

/-- A true asymptotic second-order upper coefficient for any sequence of
actual calibrated one-gradient methods is at least c*w', even with arbitrary
vanishing normalized remainder and changing policies.
Use: the original worst limiting known-base comparison follows from actual
source matrix scenarios, with no consistency or policy regularity restriction.
Article: main_krylov, thm:local(c).
Proof: exact physical prior minimax bounds every actual method at each true
positive scale. Divide by that real scale squared and pass through the
supplied genuine vanishing normalized remainder. -/
theorem known_base_asymptotic_lower
    (center : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hcenter : center.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues center hcenter.1 g).card=n+1)
    (c weight v : ℝ) (hc0 : 0≤c) (hw : 0≤weight)
    (scale remainder : ℕ → ℝ) (ht : ∀ j,0<scale j)
    (hsmall : ∀ j,c*scale j<1) (hout : ∀ j,weight*scale j≤1)
    (method : ℕ → OneGradientMethod (EuclideanSpace ℝ (Fin (n+1))))
    (hm : ∀ j,OneGradientSpanRestricted (method j))
    (hbound : ∀ j,relativePriorGuarantee center (c*scale j) g (weight*scale j) (method j)
      (v*(scale j)^2+remainder j))
    (hrem : Tendsto (fun j => remainder j/(scale j)^2) atTop (𝓝 0)) : c*weight≤v := by
  have hlower (j : ℕ) : c*weight≤v+remainder j/(scale j)^2 := by
    have h := (relative_prior_exact_uniform_minimax center hcenter g hg hc
      (mul_nonneg hc0 (ht j).le) (hsmall j) (mul_nonneg hw (ht j).le) (hout j)).2
        ⟨method j,hm j,hbound j⟩
    have he : (c*scale j)*(weight*scale j)=c*weight*(scale j)^2 := by ring
    rw [he] at h
    have hdiv := (le_div_iff₀ (sq_pos_of_pos (ht j))).mpr h
    rwa [add_div,mul_div_cancel_right₀ _ (sq_pos_of_pos (ht j)).ne'] at hdiv
  have hconv : Tendsto (fun j => v+remainder j/(scale j)^2) atTop (𝓝 v) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := v)).add hrem
  exact ge_of_tendsto hconv (Eventually.of_forall hlower)

end
end krylov.OneGradient
