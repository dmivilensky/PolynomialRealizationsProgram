import polyak.ModeLocking.Continuation.Implicit
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! Derivative of a finite linear combination when both its argument and
its coefficients vary. -/
noncomputable section
namespace polyak.ModeLocking.Continuation
open scoped BigOperators
variable {d : ℕ}

def weightedDerivative (a da w : Fin d → ℝ) :
    (ℝ × (Fin d → ℝ)) →L[ℝ] ℝ :=
  ∑ i, ((a i) • ((ContinuousLinearMap.proj (R := ℝ) i : (Fin d → ℝ) →L[ℝ] ℝ).comp
    (ContinuousLinearMap.snd ℝ ℝ (Fin d → ℝ))) +
    (w i * da i) • ContinuousLinearMap.fst ℝ ℝ (Fin d → ℝ))

theorem weightedDerivative_apply (a da w : Fin d → ℝ) (z : ℝ × (Fin d → ℝ)) :
    weightedDerivative a da w z = (∑ i, a i * z.2 i) + z.1 * ∑ i, w i * da i := by
  simp [weightedDerivative, Finset.sum_add_distrib, Finset.mul_sum, mul_comm]

theorem hasFDerivAt_weighted_sum (a : Fin d → ℝ → ℝ) (da w : Fin d → ℝ) (s : ℝ)
    (ha : ∀ i, HasDerivAt (a i) (da i) s) :
    HasFDerivAt (fun z : ℝ × (Fin d → ℝ) => ∑ i, z.2 i * a i z.1)
      (weightedDerivative (fun i => a i s) da w) (s, w) := by
  have hterm (i : Fin d) : HasFDerivAt
      (fun z : ℝ × (Fin d → ℝ) => z.2 i * a i z.1)
      ((a i s) • ((ContinuousLinearMap.proj (R := ℝ) i : (Fin d → ℝ) →L[ℝ] ℝ).comp
        (ContinuousLinearMap.snd ℝ ℝ (Fin d → ℝ))) +
        (w i * da i) • ContinuousLinearMap.fst ℝ ℝ (Fin d → ℝ)) (s, w) := by
    have hw := ((ContinuousLinearMap.proj (R := ℝ) i : (Fin d → ℝ) →L[ℝ] ℝ).comp
      (ContinuousLinearMap.snd ℝ ℝ (Fin d → ℝ))).hasFDerivAt (x := (s, w))
    have hh := (ha i).hasFDerivAt.comp (s, w)
      (ContinuousLinearMap.fst ℝ ℝ (Fin d → ℝ)).hasFDerivAt
    convert hw.mul hh using 1 <;> first
    | rfl
    | (apply ContinuousLinearMap.ext; intro z
       change a i s * z.2 i + (w i * da i) * z.1 = w i * (z.1 * da i) + a i s * z.2 i
       ring)
  exact HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => hterm i)

end polyak.ModeLocking.Continuation
