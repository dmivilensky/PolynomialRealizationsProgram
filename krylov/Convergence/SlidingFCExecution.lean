import krylov.Convergence.SS1Execution
import krylov.Functions.SearchTrajectory

/-!
Article: main_krylov, thm:G, actual sliding full conjugacy.
Use: execute the original observed-data FC solve with a chronological
window and genuine objective line minimization. Both measured conjugacy
and the local search properties are derived from the actual executor.
Source: the FC block solve and the already proved genuine exact-search API.
-/

namespace krylov.Convergence
noncomputable section
open Matrix Set Filter Topology krylov.Functions krylov.Methods
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The exact observed FC direction on its actual chronological window. -/
def slidingFCWindowDirection (G : E → E) (q : Fin (n+2) → E) : E :=
  conjugacyDirection (fun i : Fin (n+1)=>q i.succ-q i.castSucc)
    (fun i=>G (q i.succ)-G (q i.castSucc)) (G (q (Fin.last (n+1))))

/-- The next genuine function query minimizes the actual objective on the
real local chord along the direction computed from stored observations. -/
def slidingFCWindowRule (f : E → ℝ) (G : E → E) (r : ℝ) (q : Fin (n+2) → E) : E :=
  localExactPoint f (q (Fin.last (n+1))) (slidingFCWindowDirection G q) r

/-- Literal sliding FC from an initial finite observed point history. -/
def slidingFCSequence (f : E → ℝ) (G : E → E) (r : ℝ) (seed : Fin (n+2) → E) : ℕ → E :=
  slidingSequence (slidingFCWindowRule f G r) seed

/-- The actual solve matrix of the window beginning at the given old step. -/
def slidingFCSolveMatrix (G : E → E) (x : ℕ → E) (k : ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  crossGram (windowImage G x k) (windowStep x k)

/-- The actual direction used after the last point of that old window. -/
def slidingFCDirection (G : E → E) (x : ℕ → E) (k : ℕ) : E :=
  conjugacyDirection (windowStep (n:=n+1) x k) (windowImage G x k) (G (x (k+n+1)))

theorem slidingFCSequence_step (f : E → ℝ) (G : E → E) (r : ℝ) (seed : Fin (n+2) → E) (k : ℕ) :
    slidingFCSequence f G r seed (k+n+2)=localExactPoint f
      (slidingFCSequence f G r seed (k+n+1)) (slidingFCDirection (n:=n) G (slidingFCSequence f G r seed) k) r := by
  rw [slidingFCSequence,slidingSequence_step]
  rfl

/-- Defined observed conjugacy solves exclude zero stored steps; this fact
does not require any independent conditioning premise. -/
theorem observed_solve_step_ne_zero (s y : Fin (n+1) → E)
    (hsolve : IsUnit (crossGram y s).det) (i : Fin (n+1)) : s i≠0 := by
  have hi := Matrix.linearIndependent_cols_of_det_ne_zero (isUnit_iff_ne_zero.mp hsolve)
  intro hz
  apply hi.ne_zero i
  funext j
  change inner ℝ (y j) (s i)=0
  rw [hz,inner_zero_right]

/-- Exact stored-image conjugacy is a conclusion of the computed inverse. -/
theorem slidingFC_direction_conjugate (G : E → E) (x : ℕ → E) (k : ℕ)
    (hsolve : IsUnit (slidingFCSolveMatrix (n:=n) G x k).det) (i : Fin (n+1)) :
    inner ℝ (windowImage G x k i) (slidingFCDirection (n:=n) G x k)=0 := by
  exact congrFun (conjugacyDirection_conjugate (windowStep (n:=n+1) x k)
    (windowImage G x k) (G (x (k+n+1))) hsolve) i

/-- A genuine searched new step is conjugate to every retained observed
image. No orthogonality or Gram conditioning is assumed. -/
theorem slidingFC_searched_step_conjugate (f : E → ℝ) (G : E → E)
    (x : ℕ → E) (r : ℝ) (k : ℕ)
    (hsolve : IsUnit (slidingFCSolveMatrix (n:=n) G x k).det)
    (hsearch : IsChordMinimum f (x (k+n+1)) (slidingFCDirection (n:=n) G x k) r (x (k+n+2)))
    (i : Fin (n+1)) :
    inner ℝ (windowImage G x k i) (x (k+n+2)-x (k+n+1))=0 := by
  obtain ⟨α,hα⟩ := hsearch.2.1
  rw [hα,add_sub_cancel_left,real_inner_smul_right,slidingFC_direction_conjugate G x k hsolve,mul_zero]

/-- On a genuine local source, every sufficiently late executed FC search
is the true chord minimum. This uses only convergence of its actual points,
as in (A2), and original function derivatives. -/
theorem slidingFCSequence_eventually_chord
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    {r : ℝ} (hr : 0<r) (hH₀ : H 0=ContinuousLinearMap.id ℝ E)
    {L : ℝ≥0} (hLr : (L:ℝ)*r≤1/2)
    (hH : LipschitzOnWith L H (Metric.closedBall 0 r))
    (hf : ∀ z∈Metric.closedBall (0:E) r,HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z∈Metric.closedBall (0:E) r,HasFDerivAt G (H z) z)
    (seed : Fin (n+2) → E) (hconv : Tendsto (slidingFCSequence f G r seed) atTop (𝓝 0)) :
    ∀ᶠ k in atTop,IsChordMinimum f (slidingFCSequence f G r seed (k+n+1))
      (slidingFCDirection (n:=n) G (slidingFCSequence f G r seed) k) r
      (slidingFCSequence f G r seed (k+n+2)) := by
  have hc : Tendsto (fun k=>slidingFCSequence f G r seed (k+n+1)) atTop (𝓝 0) := by
    simpa only [Nat.add_assoc,Function.comp_def] using hconv.comp (tendsto_add_atTop_nat (n+1))
  have hmem : ∀ᶠ k in atTop,slidingFCSequence f G r seed (k+n+1)∈Metric.closedBall (0:E) r :=
    hc.eventually (Metric.closedBall_mem_nhds 0 hr)
  filter_upwards [hmem] with k hk
  rw [slidingFCSequence_step]
  exact localExactPoint_spec f _ _ r
    (existsUnique_local_chord_minimum f G H hr hH₀ hLr hH hf hG _ _ hk)

end
end krylov.Convergence
