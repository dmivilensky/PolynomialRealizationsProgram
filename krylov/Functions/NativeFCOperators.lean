import krylov.Functions.NativeFCSearch
import krylov.Functions.ExactSearchOperator
import krylov.Methods.ExecutedFC

/-!
Article: main_krylov, lem:cycle-transfer and thm:Htransfer, native FC/operator identification.
Use: reconstruct the complete actual FC observed history from genuine function
queries, identify its direction with the existing implementation, and couple
its exact searches to the true averaged-Hessian operator execution.
Source: Algorithm FC, the actual search/operator bridge, and the segment FTC.
-/

namespace krylov.Functions
noncomputable section
open Set Metric krylov.Methods chebyshev1.Nonlinear
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every native function history contains exactly the initial point and the executed queries.
Article: main_krylov, alg:fc, genuine query clock. -/
theorem fcFunctionHistory_length (f : E → ℝ) (G : E → E) (memory : ℕ → ℕ)
    (r : ℝ) (x₀ : E) (k : ℕ) : (fcFunctionHistory f G memory r x₀ k).length = k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (fcFunctionHistory f G memory r x₀ k).length + 1 = k + 1 + 1
    rw [ih]

/-- The actual next function point is prepended to the whole previous query history.
Article: main_krylov, alg:fc. -/
theorem fcFunctionHistory_succ (f : E → ℝ) (G : E → E) (memory : ℕ → ℕ)
    (r : ℝ) (x₀ : E) (k : ℕ) :
    fcFunctionHistory f G memory r x₀ (k + 1) =
      fcFunctionPoint f G memory r x₀ (k + 1) :: fcFunctionHistory f G memory r x₀ k := rfl

omit [InnerProductSpace ℝ E] in
/-- Actual adjacent points produce precisely the new stored step and gradient secant.
Article: main_krylov, alg:fc, the exact observed dictionary. -/
theorem fcFunctionPairs_cons (G : E → E) (x y₀ : E) (hist : List E) (hhist : hist ≠ []) :
    fcFunctionPairs G (x :: hist) =
      (x - hist.headD y₀, G x - G (hist.headD y₀)) :: fcFunctionPairs G hist := by
  cases hist with
  | nil => exact False.elim (hhist rfl)
  | cons y rest => rfl

/-- The real segment operator is the average of the actual Hessian on the actual FC segment.
Article: main_krylov, lem:cycle-transfer. -/
def fcFunctionOperator (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    (memory : ℕ → ℕ) (r : ℝ) (x₀ : E) (k : ℕ) : E →L[ℝ] E :=
  averagedDerivative H (fcFunctionPoint f G memory r x₀ k)
    (fcFunctionPoint f G memory r x₀ (k + 1) - fcFunctionPoint f G memory r x₀ k)

/-- The complete actual function observations in the repository's existing policy-history type.
Article: main_krylov, alg:fc, true direction, probe, step and next gradient. -/
def fcFunctionObservedHistory (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    (memory : ℕ → ℕ) (r : ℝ) (x₀ : E) : ℕ → History E
  | 0 => ⟨G x₀, []⟩
  | k + 1 =>
      let prev := fcFunctionObservedHistory f G H memory r x₀ k
      let d := fcFunctionDirection G memory x₀ (fcFunctionHistory f G memory r x₀ k)
      ⟨G x₀, ⟨d, fcFunctionOperator f G H memory r x₀ k d,
        fcFunctionPoint f G memory r x₀ (k + 1) - fcFunctionPoint f G memory r x₀ k,
        G (fcFunctionPoint f G memory r x₀ (k + 1)), []⟩ :: prev.records⟩

/-- The actual observed policy history has the true current nonlinear gradient.
Article: main_krylov, lem:cycle-transfer, exact native dictionary. -/
theorem fcFunctionObservedHistory_gradient (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    (memory : ℕ → ℕ) (r : ℝ) (x₀ : E) (k : ℕ) :
    (fcFunctionObservedHistory f G H memory r x₀ k).gradient = G (fcFunctionPoint f G memory r x₀ k) := by
  cases k <;> rfl

/-- The complete actual policy history retains exactly its original observed gradient.
Article: main_krylov, alg:fc, the initial observation. -/
theorem fcFunctionObservedHistory_initial (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    (memory : ℕ → ℕ) (r : ℝ) (x₀ : E) (k : ℕ) :
    (fcFunctionObservedHistory f G H memory r x₀ k).initial = G x₀ := by
  cases k <;> rfl

/-- The actual observed iteration count equals the real function-query count.
Article: main_krylov, lem:cycle-transfer, exact native dictionary. -/
theorem fcFunctionObservedHistory_length (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    (memory : ℕ → ℕ) (r : ℝ) (x₀ : E) (k : ℕ) :
    (fcFunctionObservedHistory f G H memory r x₀ k).records.length = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (fcFunctionObservedHistory f G H memory r x₀ k).records.length + 1 = k + 1
    rw [ih]

/-- Both true native observation encodings contain exactly the same measured step/secant pairs.
Article: main_krylov, alg:fc and lem:cycle-transfer. -/
theorem fcFunctionObservedHistory_pairs (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    (memory : ℕ → ℕ) (r : ℝ) (x₀ : E) (k : ℕ) :
    (fcFunctionObservedHistory f G H memory r x₀ k).pairs =
      fcFunctionPairs G (fcFunctionHistory f G memory r x₀ k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hne : fcFunctionHistory f G memory r x₀ k ≠ [] := by
      intro h
      have hl := fcFunctionHistory_length f G memory r x₀ k
      rw [h] at hl
      simp at hl
    rw [fcFunctionHistory_succ, fcFunctionPairs_cons G _ x₀ _ hne]
    have hinit := fcFunctionObservedHistory_initial f G H memory r x₀ k
    conv_lhs => rw [fcFunctionObservedHistory]
    rw [← hinit]
    change (fcFunctionPoint f G memory r x₀ (k + 1) - fcFunctionPoint f G memory r x₀ k,
      G (fcFunctionPoint f G memory r x₀ (k + 1)) -
        (fcFunctionObservedHistory f G H memory r x₀ k).gradient) ::
          (fcFunctionObservedHistory f G H memory r x₀ k).pairs = _
    rw [fcFunctionObservedHistory_gradient, ih]
    rfl

/-- The native function direction is exactly the existing FC policy's direction on its true observations.
Article: main_krylov, alg:fc, implementation-level dictionary. -/
theorem fcFunctionObservedHistory_direction (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    (memory : ℕ → ℕ) (r : ℝ) (x₀ : E) (k : ℕ) :
    (fcMethod memory).direction (fcFunctionObservedHistory f G H memory r x₀ k) =
      fcFunctionDirection G memory x₀ (fcFunctionHistory f G memory r x₀ k) := by
  simp only [fcMethod, retainedMethod, selectedWindow, fcFunctionObservedHistory_length,
    fcFunctionObservedHistory_gradient, fcFunctionObservedHistory_pairs,
    fcFunctionDirection, fcFunctionHistory_length, Nat.add_sub_cancel]
  rfl

end
end krylov.Functions
