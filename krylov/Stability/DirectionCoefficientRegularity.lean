import krylov.Stability.ContDiffXRFCD
import krylov.Methods.DirectionImageError
set_option autoImplicit false
/-!
Article: main_krylov, thm:I and lem:U(d), actual direction virtual coefficient calculus.
Use: derive C-r native coefficients and true image-error regularity from
primitive original trial charts and actual quadratic reference domains.
Source: the reused genuine direction-replay query induction and native
finite inverse-model coefficient calculus, including the terminal solve.
-/

namespace krylov.Stability
noncomputable section
open Matrix krylov.Methods krylov.Reference
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Every actual native XRFC-D virtual coefficient is C-r from primitive data
at the genuine quadratic reference, including the terminal output coefficients.
Use: differentiate the true replay recursion with its actual native weights.
Article: main_krylov, thm:I and lem:U(d).
Proof: the actual replay induction gives each true direction, observed image
and returned gradient. Their genuine pair-model entries are smooth inner
products; actual positive reference domains and the reused inverse-coefficient
calculus give the original computed coefficient regularity. -/
theorem quadraticXRFCD_coefficients_contDiffAt {r : WithTop ℕ∞} (trial : History E → ℝ)
    (A : X → ℕ → E →L[ℝ] E) (g : X → E) (x : X)
    (hA : ∀ i,ContDiffAt ℝ r (fun z => A z i) x) (hg : ContDiffAt ℝ r g x)
    (Q : E →L[ℝ] E) (hAx : A x=fun _ => Q) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (N : ℕ)
    (hpre : ∀ i<N,CG.gradient Q (g x) i≠0)
    (ht : ∀ i<N,trial (oneGradientRun (xrfcDMethod fullMemory trial) (fun _ => Q) (g x) i)≠0)
    (hT : ∀ k<N,ContDiffAt ℝ r (trialCoordinate trial k)
      (oneGradientData (xrfcDMethod fullMemory trial) (A x) (g x) k))
    (k : ℕ) (hk : k≤N) (i : Fin k) :
    ContDiffAt ℝ r (fun z => xrfcDArrayCoefficients trial (A z) (g z) k i) x := by
  have hreg := quadraticXRFCD_prefix_contDiffAt trial A g x hA hg Q hAx hQ hpos N hpre ht hT
  let D := fun z (j : Fin k) => xrfcDExecutedDirection trial (A z) (g z) (k-1-j.val)
  let Y := fun z (j : Fin k) => xrfcDExecutedImage trial (A z) (g z) (k-1-j.val)
  have hD (j : Fin k) : ContDiffAt ℝ r (fun z => D z j) x := hreg.2.2.1 _ (by omega)
  have hY (j : Fin k) : ContDiffAt ℝ r (fun z => Y z j) x := hreg.2.2.2 _ (by omega)
  have hdom : (pairModel (D x) (Y x)).det≠0 := by
    dsimp only [D,Y]
    rw [hAx]
    exact (xrfcD_full_array_domains trial Q hQ hpos (g x) N hpre ht k hk).2
  exact contDiff_modelCoefficients D (fun z => pairModel (D z) (Y z))
    (fun z => oneGradientGradient (xrfcDMethod fullMemory trial) (A z) (g z) k) x hD
    (fun j l => (hD (max j l)).inner ℝ (hY (min j l))) (hreg.1 k hk) hdom i

end
end krylov.Stability
