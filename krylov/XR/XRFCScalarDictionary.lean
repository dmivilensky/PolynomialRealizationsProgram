import krylov.XR.XRFCChronological
import krylov.XR.LocalPrescribedTrial
import krylov.Convergence.OneGradientFunctions

/-!
Article: main_krylov, lem:xr-local, actual ordinary XRFC scalar dictionary.
Use: the literal chronological native full-memory execution is the genuine
one-gradient scalar XRFC executor with precisely its actually computed
trial vector. This is an exact execution identity; no reference trajectory,
gradient bound or desired output expansion is assumed.
Source: the real list-reversal solve dictionary and one actual gradient
query per native accepted/full-virtual update.
-/

namespace krylov.XR
noncomputable section
open Matrix krylov.Methods krylov.Convergence
open scoped InnerProductSpace
variable {n : ℕ}

/-- The actual finite vector of trial scalars computed by the native
full-memory executor. Extracting these numbers makes no new oracle query. -/
def fullVirtualTrialVector (P : Parameters)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x₀ : EuclideanSpace ℝ (Fin n)) (bounds : SpectralBounds) (N : ℕ) : Fin N → ℝ :=
  fun i => algorithmTrialParameter P (fullVirtualRun P (algorithmTrialParameter P) f G x₀ bounds i.val)

/-- The true observed chronological secants append exactly one genuine
new pair. Anchor transport changes none of their step/image coordinates. -/
theorem xrfcNewestPairs_fullVirtualAdvance (P : Parameters)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (S : State (EuclideanSpace ℝ (Fin n))) :
    xrfcNewestPairs (fullVirtualAdvance P (algorithmTrialParameter P) f G S).pairs =
      (fullVirtualStep P (algorithmTrialParameter P) S,
        G (S.point + fullVirtualStep P (algorithmTrialParameter P) S) - S.gradient) :: xrfcNewestPairs S.pairs := by
  simp only [xrfcNewestPairs, fullVirtualAdvance, secantPairs, List.map_map, List.map_append,
    List.map_cons, List.map_nil, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append]
  rfl

/-- Actual scalar execution contributes one real observed gradient record
per step; the prescribed-trial selector therefore uses its true index. -/
theorem xrfcScalarFunctionRun_length {E : Type*} [NormedAddCommGroup E]
    (m : OneGradientMethod E) (G : E → E) (x₀ : E) (k : ℕ) :
    (oneGradientFunctionRun m G x₀ k).records.length = k := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg Nat.succ ih

theorem xrfcScalarFunctionAdvance_pairs {E : Type*} [NormedAddCommGroup E]
    (m : OneGradientMethod E) (G : E → E) (x₀ : E) (H : History E) :
    (oneGradientFunctionAdvance m G x₀ H).pairs =
      (m.step H, G (x₀ + H.displacement + m.step H) - H.gradient) :: H.pairs := rfl

/-- The genuine scalar XRFC executor and the native full-memory run
observe exactly the same points, gradients and secant history, when their
prescribed vector is the native rule's actual computed vector. The vector
is a mathematical extraction from an already defined data-only execution,
not an additional input or oracle available to that native algorithm. -/
theorem fullVirtualRun_oneGradient_dictionary (P : Parameters) (hoff : P.valuesEnabled = false)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x₀ : EuclideanSpace ℝ (Fin n)) (bounds : SpectralBounds) (N : ℕ) :
    let tau := fullVirtualTrialVector P f G x₀ bounds N
    let m := xrfcMethod fullMemory (prescribedTrial tau) (E := EuclideanSpace ℝ (Fin n))
    ∀ k ≤ N,
      oneGradientFunctionPoint m G x₀ k = (fullVirtualRun P (algorithmTrialParameter P) f G x₀ bounds k).point ∧
      (oneGradientFunctionRun m G x₀ k).gradient = (fullVirtualRun P (algorithmTrialParameter P) f G x₀ bounds k).gradient ∧
      (oneGradientFunctionRun m G x₀ k).pairs =
        xrfcNewestPairs (fullVirtualRun P (algorithmTrialParameter P) f G x₀ bounds k).pairs := by
  let tau := fullVirtualTrialVector P f G x₀ bounds N
  let m := xrfcMethod fullMemory (prescribedTrial tau) (E := EuclideanSpace ℝ (Fin n))
  dsimp only
  intro k hk
  induction k with
  | zero =>
    refine ⟨?_, rfl, rfl⟩
    simp only [oneGradientFunctionPoint, oneGradientFunctionRun, History.displacement,
      List.map_nil, List.sum_nil, add_zero]
    rfl
  | succ k ih =>
    have hkn : k < N := by omega
    have hi := ih hkn.le
    let H := oneGradientFunctionRun m G x₀ k
    let S := fullVirtualRun P (algorithmTrialParameter P) f G x₀ bounds k
    have ht : prescribedTrial tau H = algorithmTrialParameter P S := by
      unfold prescribedTrial
      rw [xrfcScalarFunctionRun_length, dite_eq_left hkn]
      rfl
    have hstep : fullVirtualStep P (algorithmTrialParameter P) S = m.step H :=
      fullVirtualStep_eq_xrfcStep P hoff S H (prescribedTrial tau) hi.2.2 hi.2.1 ht
    have hpoint : oneGradientFunctionPoint m G x₀ (k + 1) =
        (fullVirtualRun P (algorithmTrialParameter P) f G x₀ bounds (k + 1)).point := by
      rw [oneGradientFunctionPoint_succ, hi.1, ← hstep]
      rfl
    refine ⟨hpoint, ?_, ?_⟩
    · rw [oneGradientFunctionRun_gradient, hpoint]
      exact (fullVirtualRun_cache P (algorithmTrialParameter P) f G x₀ bounds (k + 1)).2.symm
    · change (oneGradientFunctionAdvance m G x₀ H).pairs =
        xrfcNewestPairs (fullVirtualAdvance P (algorithmTrialParameter P) f G S).pairs
      rw [xrfcScalarFunctionAdvance_pairs, xrfcNewestPairs_fullVirtualAdvance]
      change (m.step H, G (oneGradientFunctionPoint m G x₀ k + m.step H) - H.gradient) :: H.pairs = _
      rw [hi.1, hi.2.1, hi.2.2, ← hstep]

/-- The actual unevaluated native XRFC output is exactly the original
scalar one-gradient output with the same actually computed trial vector. -/
theorem fullVirtualOutput_oneGradient_dictionary (P : Parameters) (hoff : P.valuesEnabled = false)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x₀ : EuclideanSpace ℝ (Fin n)) (bounds : SpectralBounds) (N : ℕ) :
    fullVirtualOutput P (algorithmTrialParameter P) f G x₀ bounds N =
      oneGradientFunctionOutput (xrfcMethod fullMemory
        (prescribedTrial (fullVirtualTrialVector P f G x₀ bounds N))) G x₀ N := by
  let tau := fullVirtualTrialVector P f G x₀ bounds N
  let m := xrfcMethod fullMemory (prescribedTrial tau) (E := EuclideanSpace ℝ (Fin n))
  let H := oneGradientFunctionRun m G x₀ N
  let S := fullVirtualRun P (algorithmTrialParameter P) f G x₀ bounds N
  have hi := fullVirtualRun_oneGradient_dictionary P hoff f G x₀ bounds N N le_rfl
  have hc : m.output H = fullVirtualCorrection P S := by
    change virtualCorrection (selectedWindow fullMemory H) H.gradient = _
    rw [selectedWindow_full, hi.2.1, hi.2.2, (xrfcNewestPairs_virtual S.pairs S.gradient).1]
    unfold fullVirtualCorrection fullVirtualSelectedModel
    simp only [hoff, Bool.false_eq_true, ite_false]
  change S.point + fullVirtualCorrection P S = oneGradientFunctionPoint m G x₀ N + m.output H
  rw [hi.1, hc]

end
end krylov.XR
