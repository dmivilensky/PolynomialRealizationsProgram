import krylov.XR.LocalNativeOperatorTrial

/-!
Article: main_krylov, lem:xr-local, exact native operator/source dictionary.
Use: identify the native finite operator-input program with its genuine
function execution. The segment identities are the fundamental theorem of
calculus, discharged below from actual Hessian derivatives. Auxiliary
quadratic scalar slots do not enter ordinary XR's computations.
-/
namespace krylov.XR
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Functions Filter Topology
open chebyshev1.Nonlinear
open scoped InnerProductSpace
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The ordinary endpoint query ignores scalar slots once actual points
and gradients have been fixed. -/
theorem endpointVirtualQuery_value_congr (P : Parameters) (hoff : P.valuesEnabled = false)
    (bounds : SpectralBounds) {k : ℕ} (C D : EndpointChart E k)
    (hp : C.1 = D.1) (hg : C.2.2 = D.2.2) :
    endpointVirtualQuery P.valuesEnabled (endpointComputedTrial P bounds k) C =
      endpointVirtualQuery P.valuesEnabled (endpointComputedTrial P bounds k) D := by
  have ht := endpointComputedTrial_value_congr P hoff bounds C D hp hg
  have hs : endpointStep C = endpointStep D := by funext i; simp only [endpointStep, hp]
  have hy : endpointImage C = endpointImage D := by funext i; simp only [endpointImage, hg]
  simp only [endpointVirtualQuery, endpointVirtualModel, hoff, Bool.false_eq_true, ite_false,
    hs, hy, hp, hg, ht]

/-- The real operator-driven query points and gradients coincide with
actual function observations whenever its observed secants satisfy their
true segment identity. Scalar observation differences are irrelevant. -/
theorem endpointOperatorRun_actual (P : Parameters) (hoff : P.valuesEnabled = false)
    (bounds : SpectralBounds) (Q : E →L[ℝ] E) (g : E) (constant : ℝ)
    (f : E → ℝ) (G : E → E) (hg₀ : G 0 = g) (A : ℕ → E →L[ℝ] E) (N : ℕ)
    (hsec : ∀ k < N,
      let C := endpointFunctionRun P.valuesEnabled (endpointComputedTrial P bounds) f G 0 k
      let x := endpointVirtualQuery P.valuesEnabled (endpointComputedTrial P bounds k) C
      G x = C.2.2 (Fin.last k) + A k (x-C.1 (Fin.last k))) :
    ∀ k ≤ N,
      (endpointOperatorRun P.valuesEnabled (endpointComputedTrial P bounds) Q g constant A k).1 =
        (endpointFunctionRun P.valuesEnabled (endpointComputedTrial P bounds) f G 0 k).1 ∧
      (endpointOperatorRun P.valuesEnabled (endpointComputedTrial P bounds) Q g constant A k).2.2 =
        (endpointFunctionRun P.valuesEnabled (endpointComputedTrial P bounds) f G 0 k).2.2 := by
  intro k hk
  induction k with
  | zero => exact ⟨rfl, by simp only [endpointOperatorRun, endpointFunctionRun, hg₀]⟩
  | succ k ih =>
    have hkN : k < N := by omega
    have hi := ih hkN.le
    let C := endpointOperatorRun P.valuesEnabled (endpointComputedTrial P bounds) Q g constant A k
    let D := endpointFunctionRun P.valuesEnabled (endpointComputedTrial P bounds) f G 0 k
    have hq := endpointVirtualQuery_value_congr P hoff bounds C D hi.1 hi.2
    have hs := hsec k hkN
    dsimp only at hs
    constructor
    · change Fin.snoc (α := fun _ : Fin (k+2) => E) C.1 _ = Fin.snoc D.1 _
      rw [hi.1, hq]
    · change Fin.snoc (α := fun _ : Fin (k+2) => E) C.2.2 _ = Fin.snoc D.2.2 _
      rw [hi.2, hq, hi.1]
      congr 1
      change D.2.2 (Fin.last k) + A k
        (endpointVirtualQuery P.valuesEnabled (endpointComputedTrial P bounds k) D-D.1 (Fin.last k)) = _
      exact hs.symm

/-- The actual Hessian average on each genuine native endpoint step. -/
def endpointFunctionOperator (P : Parameters) (bounds : SpectralBounds)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E) (k : ℕ) : E →L[ℝ] E :=
  let C := endpointFunctionRun P.valuesEnabled (endpointComputedTrial P bounds) f G 0 k
  let x := endpointVirtualQuery P.valuesEnabled (endpointComputedTrial P bounds k) C
  averagedDerivative H (C.1 (Fin.last k)) (x-C.1 (Fin.last k))

/-- A genuine segment FTC supplies the operator-program identity from
actual Hessian derivatives, with no assumed gradient recurrence field. -/
theorem endpointFunctionOperator_secant (P : Parameters) (bounds : SpectralBounds)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E) (k : ℕ)
    (hH : let C := endpointFunctionRun P.valuesEnabled (endpointComputedTrial P bounds) f G 0 k
      let s := endpointVirtualQuery P.valuesEnabled (endpointComputedTrial P bounds k) C-C.1 (Fin.last k)
      ContinuousOn (fun t : ℝ => H (C.1 (Fin.last k)+t • s)) (Set.Icc 0 1))
    (hG : let C := endpointFunctionRun P.valuesEnabled (endpointComputedTrial P bounds) f G 0 k
      let s := endpointVirtualQuery P.valuesEnabled (endpointComputedTrial P bounds k) C-C.1 (Fin.last k)
      ∀ t ∈ Set.Icc (0:ℝ) 1, HasFDerivAt G (H (C.1 (Fin.last k)+t • s))
        (C.1 (Fin.last k)+t • s)) :
    let C := endpointFunctionRun P.valuesEnabled (endpointComputedTrial P bounds) f G 0 k
    let x := endpointVirtualQuery P.valuesEnabled (endpointComputedTrial P bounds k) C
    G x = C.2.2 (Fin.last k) + endpointFunctionOperator P bounds f G H k (x-C.1 (Fin.last k)) := by
  let C := endpointFunctionRun P.valuesEnabled (endpointComputedTrial P bounds) f G 0 k
  let x := endpointVirtualQuery P.valuesEnabled (endpointComputedTrial P bounds k) C
  have ht := averagedDerivative_apply G H (C.1 (Fin.last k)) (x-C.1 (Fin.last k)) hH hG
  rw [add_sub_cancel] at ht
  have hc := (endpointFunctionRun_cache P.valuesEnabled (endpointComputedTrial P bounds) f G 0 k (Fin.last k)).2
  dsimp only
  change G x = C.2.2 (Fin.last k) + _
  rw [hc, endpointFunctionOperator, ht]
  abel

/-- The native operator trial vector is exactly the actual native trial
vector on its true observed segment operators. -/
theorem nativeOperatorTrialVector_actual (P : Parameters) (hoff : P.valuesEnabled = false)
    (bounds : SpectralBounds) (hinit : P.initialCapacity = n) (hmax : P.maximumCapacity = n)
    (N : ℕ) (hN : N ≤ n)
    (Q : E →L[ℝ] E) (g : E) (constant : ℝ) (f : E → ℝ) (G : E → E) (hg₀ : G 0 = g)
    (e : Fin (N+1) → E →L[ℝ] E)
    (hsec : ∀ (k : ℕ) (hk : k < N),
      let C := endpointFunctionRun P.valuesEnabled (endpointComputedTrial P bounds) f G 0 k
      let x := endpointVirtualQuery P.valuesEnabled (endpointComputedTrial P bounds k) C
      G x = C.2.2 (Fin.last k) + (Q+e ⟨k, Nat.lt_succ_of_lt hk⟩) (x-C.1 (Fin.last k))) :
    nativeOperatorTrialVector P bounds Q g constant N e = fullVirtualTrialVector P f G 0 bounds N := by
  have he := endpointOperatorRun_actual P hoff bounds Q g constant f G hg₀
    (prescribedOperatorPath Q e) N (by
      intro k hk
      simpa only [prescribedOperatorPath, dite_eq_left hk] using hsec k hk)
  funext i
  unfold nativeOperatorTrialVector fullVirtualTrialVector
  rw [endpointComputedTrial_value_congr P hoff bounds _ _ (he i.val i.isLt.le).1 (he i.val i.isLt.le).2]
  exact (fullVirtualRun_trial_endpoint P bounds hinit hmax f G 0 i.val (i.isLt.le.trans hN)).symm

end
end krylov.XR
