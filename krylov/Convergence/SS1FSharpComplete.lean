import krylov.Convergence.SS1FSharpError
import krylov.Convergence.SS1FScalarSharp
import krylov.Convergence.SS1FContinuousOldest

/-!
Article: Theorem 6.1 [thm:ss1F] of krylov.tex.
Use: combine the scalar current-Hessian cancellation with the higher-dimensional
oldest/adjacent leading-matrix proof. The actual C3,1 execution gives a literal
1+o(1) factor, with the original T3 spectral norm and all zero-weight cases.
The imported continuous-D3 result proves the remaining oldest-product branch;
SS1FOriginalRegularity proves the printed characteristic R-order.
Source: genuine observed values/gradients and the original (S) and gain hypotheses.
-/

namespace krylov.Convergence
noncomputable section
open Matrix Set Filter Topology Asymptotics krylov.Functions krylov.LinearAlgebra
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {n : ℕ}

/-- The original exact SS1-F error bound, including dimension one, for
the literal genuine recursive execution. The auxiliary local derivative
budgets, all matrix remainders and actual inverse domains are proved. -/
theorem ss1FSequence_printed_sharp_asymptotic
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (H : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+1)))
    (T : EuclideanSpace ℝ (Fin (n+1)) → SymmetricCubic (EuclideanSpace ℝ (Fin (n+1))))
    (S : Set (EuclideanSpace ℝ (Fin (n+1)))) (hS : Convex ℝ S)
    (h₀ : (0:EuclideanSpace ℝ (Fin (n+1)))∈S) (hnbhd : S∈𝓝 0)
    {R : ℝ} (hR : 0≤R) (hbounded : ∀ z∈S,‖z‖≤R) {L₃ : ℝ≥0} (hH₀ : H 0=ContinuousLinearMap.id ℝ _)
    (hf : ∀ z∈S,HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z∈S,HasFDerivAt G (H z) z) (hG₀ : G 0=0)
    (hT : ∀ z∈S,HasFDerivAt (gradientHessian H) (T z).form z)
    (hLip : ∀ z∈S,∀ w∈S,∀ h,‖h‖=1 →
      |(T z).form h h h-(T w).form h h h|≤(L₃:ℝ)*‖z-w‖)
    (split : (Fin (n+2) → EuclideanSpace ℝ (Fin (n+1))) → Fin (n+1) → ℝ)
    (seed : Fin (n+2) → EuclideanSpace ℝ (Fin (n+1)))
    (hconv : Tendsto (ss1FSequence f G split seed) atTop (𝓝 0))
    {Cw σ : ℝ} (hCw : 0≤Cw) (hσ : 0<σ)
    (hw : ∀ᶠ k in atTop,∀ i : Fin (n+1),
      ‖splitRemainder (ss1FSequence f G split seed (k+i.val))
        (windowStep (ss1FSequence f G split seed) k i)
        (ss1FSequence f G split seed (k+n+1))
        (split (fun j=>ss1FSequence f G split seed (k+j.val)) i)‖≤
      Cw*‖ss1FSequence f G split seed (k+n+1)-ss1FSequence f G split seed (k+i.val+1)‖)
    (hind : ∀ᶠ k in atTop,
      IsUnit (windowMatrix (unitWindow (windowStep (ss1FSequence f G split seed) k))).det ∧
      σ≤leastGain (windowMatrix (unitWindow (windowStep (ss1FSequence f G split seed) k)))) :
    let B := ‖canonicalVariation (T 0)‖
    let x := ss1FSequence f G split seed
    ∃ θ : ℕ → ℝ,Tendsto θ atTop (𝓝 0) ∧∀ᶠ k in atTop,
      ‖x (k+n+2)‖≤(1+θ k)*
        (((Cw+1/2)*B/σ^2)*‖x (k+1)‖+((L₃:ℝ)/(12*σ^2))*‖x k‖^2)*‖x (k+n+1)‖ := by
  cases n with
  | zero =>
    exact ss1FSequence_scalar_printed_asymptotic f G H T S hS h₀ hnbhd hR hbounded
      hH₀ hf hG hG₀ hT hLip split seed hconv hCw hσ hw hind
  | succ n =>
    exact ss1FSequence_sharp_error_asymptotic f G H T S hS h₀ hnbhd hR hbounded
      hH₀ hf hG hG₀ hT hLip split seed hconv hCw hσ hw hind

end
end krylov.Convergence
