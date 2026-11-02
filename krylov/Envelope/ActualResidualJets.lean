import krylov.Envelope.ActualFrozenStep
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false
/-!
Article: main_krylov, apB:eq:tilt and apB:eq:nu, actual observed residual derivatives.
Use: differentiate true recorded step-gradient residuals and identify their
real common frozen-step contribution for every genuine smooth admissible
globally CG-consistent raw method, including its exhausted endpoint.
Source: genuine actual frozen-step congruence, true CG Galerkin
orthogonality and the actual scalar inner-product derivative rule.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Methods krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every actual recorded step-gradient residual derivative is its genuine reference-step pairing with the true gradient derivative plus the real common frozen displacement-increment pairing with the actual reference gradient.
Use: Every actual recorded step-gradient residual derivative is its genuine reference-step pairing with the true gradient derivative plus the real common frozen displacement-increment pairing with the actual reference gradient.
Article: main_krylov, apB:eq:tilt and apB:eq:nu, actual observed residual derivatives.
Proof: Differentiate the true executed observed pairing. Genuine quadratic consistency identifies the actual reference step and gradient; the proved real frozen-step congruence and true CG Galerkin orthogonality remove exactly the actual Krylov step-derivative remainder. -/
theorem actual_residual_jet_coordinates (memory : ℕ → ℕ) (m : ProbedMethod E)
    (hm : CGConsistent m) (hspan : ProbedSpanRestricted memory m)
    (A B : ℝ → ℕ → E →L[ℝ] E) (g : E) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (hA0 : A 0=fun _ => Q) (hB0 : B 0=fun _ => Q) (N : ℕ)
    (hA : ∀ i<N, ContDiffAt ℝ 2 (fun t => A t i) 0)
    (hB : ∀ i<N, ContDiffAt ℝ 2 (fun t => B t i) 0)
    (hpre : ∀ i<N, CG.gradient Q g i≠0) (hsmooth : SmoothProbedCycleAt m 2 Q g N)
    (i : ℕ) (hi : i<N) :
    let ξ := frozenDisplacement Q (CG.length Q g) (CG.beta Q g) (referenceInjection Q g A)
    deriv (fun t => inner ℝ (probedStep m (A t) (B t) g i) (probedGradient m (A t) (B t) g N)) 0=
      inner ℝ (referenceStep Q g i) (deriv (fun t => probedGradient m (A t) (B t) g N) 0)+
        inner ℝ (ξ (i+1)-ξ i) (CG.gradient Q g N) := by
  -- The true observed residual is differentiated on the actual raw trajectory and compared with its genuine frozen displacement.
  let ξ := frozenDisplacement Q (CG.length Q g) (CG.beta Q g) (referenceInjection Q g A)
  let s := fun t => probedStep m (A t) (B t) g i
  let G := fun t => probedGradient m (A t) (B t) g N
  have hG := smoothProbed_gradient_regular m hm A B (fun _ => g) 0 N hA hB contDiffAt_const
    Q hA0 hB0 hQ hpos hpre hsmooth
  have hs := (smoothProbed_fields_regular m hm A B (fun _ => g) 0 N hA hB contDiffAt_const
    Q hA0 hB0 hQ hpos hpre hsmooth i hi).2.2.1
  have hs0 : s 0=referenceStep Q g i := by
    dsimp only [s]
    rw [hA0,hB0]
    exact quadratic_probedStep_eq_cg m hm Q hQ hpos g i
  have hG0 : G 0=CG.gradient Q g N := by
    dsimp only [G,probedGradient]
    rw [hA0,hB0]
    exact quadratic_gradient_eq_cg m hm Q hQ hpos g N
  -- The real Krylov step-derivative remainder pairs to zero with the actual later reference CG gradient.
  have hfiltered := actual_frozen_step memory m hm hspan A B g Q hQ hpos hA0 hB0 N hA hB hpre hsmooth i hi
  have ho := CG.gradient_orthogonal_krylov Q hQ hpos g N hpre
    ((krylovSpace_mono Q g (show i+1≤N by omega)) hfiltered)
  change inner ℝ (deriv s 0-(ξ (i+1)-ξ i)) (CG.gradient Q g N)=0 at ho
  rw [inner_sub_left] at ho
  have he := sub_eq_zero.mp ho
  have hpair := ((hs.differentiableAt (by norm_num)).hasDerivAt.inner ℝ
    (hG.differentiableAt (by norm_num)).hasDerivAt).deriv
  change deriv (fun t => inner ℝ (s t) (G t)) 0=inner ℝ (s 0) (deriv G 0)+inner ℝ (deriv s 0) (G 0) at hpair
  rw [hs0,hG0,he] at hpair
  exact hpair
end
end krylov.Envelope
