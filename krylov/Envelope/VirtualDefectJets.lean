import krylov.Envelope.ZeroDefectJet
import krylov.Methods.VirtualBalance
import krylov.Stability.VirtualCoefficientRegularity
set_option autoImplicit false
/-!
Article: main_krylov, thm:E1, genuine explicit virtual and output injection jets.
Use: identify actual differentiated injection sums and semantic output-segment defects with original reference weights, genuine stored steps and primitive physical operator derivatives.
Source: native observed coefficient regularity and the actual zero-reference operator-defect product rule.
-/

namespace krylov.Envelope
noncomputable section
open Matrix krylov.Methods krylov.Stability
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual effective-gradient injection sum has exactly its genuine reference-weighted primitive segment-operator first derivative.
Use: The actual effective-gradient injection sum has exactly its genuine reference-weighted primitive segment-operator first derivative.
Article: main_krylov, thm:E1, genuine explicit virtual and output injection jets.
Proof: The real operator defects vanish at the original quadratic reference, so genuine moving-step and computed-coefficient derivative terms vanish in the actual product rule. -/
theorem virtualInjectionSum_hasDeriv (m : OneGradientMethod E) (A : ℝ → ℕ → E →L[ℝ] E)
    (Q : E →L[ℝ] E) (g : E) (k : ℕ) (hA0 : A 0=fun _ => Q)
    (hA : ∀ j<k,ContDiffAt ℝ 1 (fun t => A t j) 0)
    (hs : ∀ j<k,ContDiffAt ℝ 1 (fun t => oneGradientStep m (A t) g j) 0)
    (hG : ContDiffAt ℝ 1 (fun t => oneGradientGradient m (A t) g k) 0)
    (hM : (pairModel
      (fun i : Fin k => oneGradientStep m (A 0) g (k-1-i.val))
      (fun i : Fin k => A 0 (k-1-i.val) (oneGradientStep m (A 0) g (k-1-i.val)))).det≠0) :
    HasDerivAt (fun t => virtualInjectionSum m (A t) Q g k)
      (∑ i : Fin k,(1+oneGradientVirtualCoefficients m (fun _ => Q) g k i) •
        deriv (fun t => A t i.val) 0 (oneGradientStep m (fun _ => Q) g i.val)) 0 := by
  -- Native actual solve regularity justifies differentiating the genuine weights before their true zero-defect terms vanish.
  have hw := oneGradient_virtualCoefficients_contDiffAt m A (fun _ => g) 0 k hA hs hG hM
  have h := weighted_zero_defect_jet (fun i : Fin k => fun t => A t i.val-Q)
    (fun i t => oneGradientStep m (A t) g i.val)
    (fun i t => 1+oneGradientVirtualCoefficients m (A t) g k i)
    (fun i => deriv (fun t => A t i.val) 0)
    (fun i => deriv (fun t => oneGradientStep m (A t) g i.val) 0)
    (fun i => deriv (fun t => oneGradientVirtualCoefficients m (A t) g k i) 0)
    (fun i => ((hA i.val i.isLt).differentiableAt (by norm_num)).hasDerivAt.sub_const Q)
    (fun i => ((hs i.val i.isLt).differentiableAt (by norm_num)).hasDerivAt)
    (fun i => ((hw i).differentiableAt (by norm_num)).hasDerivAt.const_add 1)
    (fun i => by rw [hA0];exact sub_self Q)
  simpa only [hA0,virtualInjectionSum] using h

/-- The actual unevaluated output defect has exactly its genuine reference-weighted output-minus-segment primitive operator derivative.
Use: The actual unevaluated output defect has exactly its genuine reference-weighted output-minus-segment primitive operator derivative.
Article: main_krylov, thm:E1, genuine explicit virtual and output injection jets.
Proof: Differentiate the true output defect action with real native coefficients; only the actual zero-reference operator derivative survives. -/
theorem virtualOutputDefect_hasDeriv (m : OneGradientMethod E) (A : ℝ → ℕ → E →L[ℝ] E)
    (B : ℝ → E →L[ℝ] E) (Q : E →L[ℝ] E) (g : E) (k : ℕ)
    (hA0 : A 0=fun _ => Q) (hB0 : B 0=Q)
    (hA : ∀ j<k,ContDiffAt ℝ 1 (fun t => A t j) 0) (hB : ContDiffAt ℝ 1 B 0)
    (hs : ∀ j<k,ContDiffAt ℝ 1 (fun t => oneGradientStep m (A t) g j) 0)
    (hG : ContDiffAt ℝ 1 (fun t => oneGradientGradient m (A t) g k) 0)
    (hM : (pairModel
      (fun i : Fin k => oneGradientStep m (A 0) g (k-1-i.val))
      (fun i : Fin k => A 0 (k-1-i.val) (oneGradientStep m (A 0) g (k-1-i.val)))).det≠0) :
    HasDerivAt (fun t => virtualOutputDefect m (A t) (B t) g k)
      (∑ i : Fin k,oneGradientVirtualCoefficients m (fun _ => Q) g k i •
        (deriv B 0-deriv (fun t => A t i.val) 0) (oneGradientStep m (fun _ => Q) g i.val)) 0 := by
  have hw := oneGradient_virtualCoefficients_contDiffAt m A (fun _ => g) 0 k hA hs hG hM
  -- The semantic output defect uses the true output derivative minus each actual segment derivative.
  have h := weighted_zero_defect_jet (fun i : Fin k => fun t => B t-A t i.val)
    (fun i t => oneGradientStep m (A t) g i.val)
    (fun i t => oneGradientVirtualCoefficients m (A t) g k i)
    (fun i => deriv B 0-deriv (fun t => A t i.val) 0)
    (fun i => deriv (fun t => oneGradientStep m (A t) g i.val) 0)
    (fun i => deriv (fun t => oneGradientVirtualCoefficients m (A t) g k i) 0)
    (fun i => (hB.differentiableAt (by norm_num)).hasDerivAt.sub
      ((hA i.val i.isLt).differentiableAt (by norm_num)).hasDerivAt)
    (fun i => ((hs i.val i.isLt).differentiableAt (by norm_num)).hasDerivAt)
    (fun i => ((hw i).differentiableAt (by norm_num)).hasDerivAt)
    (fun i => by rw [hB0,hA0];exact sub_self Q)
  simpa only [hA0,virtualOutputDefect] using h
end
end krylov.Envelope
