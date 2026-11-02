import krylov.XR.LocalOperatorDictionary
import krylov.XR.LocalVirtualEquivalence

/-!
Article: main_krylov, lem:xr-local, native semantic output/operator identity.
Use: identify the actual ordinary native virtual output with the finite
operator-input response whose trial vector was proved C² from primitives.
True Hessian segment FTC supplies the observed operator dictionary; no
execution smoothness, desired output jet or convergence rate is assumed.
-/
namespace krylov.XR
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Convergence
open scoped InnerProductSpace
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Real one-gradient observations are the operator protocol whenever
the actual returned gradients satisfy their observed secant identity. -/
theorem oneGradientFunctionRun_eq_of_secants (m : OneGradientMethod E) (G : E → E)
    (A : ℕ → E →L[ℝ] E) (g : E) (hg : G 0 = g) (N : ℕ)
    (hsec : ∀ i < N, let H := oneGradientFunctionRun m G 0 i
      G (oneGradientFunctionPoint m G 0 i+m.step H) = H.gradient+A i (m.step H)) :
    oneGradientFunctionRun m G 0 N = oneGradientRun m A g N := by
  induction N with
  | zero => exact congrArg (fun v => (⟨v,[]⟩ : History E)) hg
  | succ k ih =>
    have he := ih (fun i hi => hsec i (by omega))
    have hs := hsec k (by omega)
    rw [oneGradientFunctionRun, oneGradientRun, ←he]
    unfold oneGradientFunctionAdvance oneGradientAdvance
    change (⟨_, ⟨0,0,_,_,[]⟩::_⟩ : History E) = _
    rw [show G (0+(oneGradientFunctionRun m G 0 k).displacement+m.step (oneGradientFunctionRun m G 0 k)) =
      (oneGradientFunctionRun m G 0 k).gradient+A k (m.step (oneGradientFunctionRun m G 0 k)) from hs]

/-- Exact point and gradient chart for every real prefix with the native
trial vector; the endpoint chart uses only genuine function samples. -/
theorem fullVirtual_prescribed_endpoint_point (P : Parameters) (hoff : P.valuesEnabled = false)
    (bounds : SpectralBounds) (hinit : P.initialCapacity = n) (hmax : P.maximumCapacity = n)
    (f : E → ℝ) (G : E → E) (N : ℕ) (hN : N ≤ n) :
    let m := xrfcMethod fullMemory (prescribedTrial (fullVirtualTrialVector P f G 0 bounds N))
    ∀ k ≤ N,
      oneGradientFunctionPoint m G 0 k =
        (endpointFunctionRun P.valuesEnabled (endpointComputedTrial P bounds) f G 0 k).1 (Fin.last k) := by
  dsimp only
  intro k hk
  rw [(fullVirtualRun_oneGradient_dictionary P hoff f G 0 bounds N k hk).1]
  rw [fullVirtualRun_eq_endpointNativeState P bounds hinit hmax f G 0 k (hk.trans hN)]
  rfl

/-- Genuine observed segment identities identify the native function
output with its true finite operator response, including its actual
computed (rather than prescribed externally) trial vector. -/
theorem fullVirtualOutput_native_operator_dictionary (P : Parameters) (hoff : P.valuesEnabled = false)
    (bounds : SpectralBounds) (hinit : P.initialCapacity = n) (hmax : P.maximumCapacity = n)
    (Q : E →L[ℝ] E) (g : E) (constant : ℝ) (f : E → ℝ) (G : E → E) (hg : G 0 = g)
    (N : ℕ) (hN : N ≤ n) (e : Fin (N+1) → E →L[ℝ] E)
    (hsec : ∀ (k : ℕ) (hk : k < N),
      let C := endpointFunctionRun P.valuesEnabled (endpointComputedTrial P bounds) f G 0 k
      let x := endpointVirtualQuery P.valuesEnabled (endpointComputedTrial P bounds k) C
      G x = C.2.2 (Fin.last k) + (Q+e ⟨k, Nat.lt_succ_of_lt hk⟩) (x-C.1 (Fin.last k))) :
    let tau := nativeOperatorTrialVector P bounds Q g constant N e
    (prescribedXRFCOutput Q g N (e,tau)).1 = fullVirtualOutput P (algorithmTrialParameter P) f G 0 bounds N ∧
    let m : OneGradientMethod E := xrfcMethod fullMemory (prescribedTrial tau)
    (prescribedXRFCOutput Q g N (e,tau)).2 =
      m.outputGradient (Q+e (Fin.last N)) (oneGradientFunctionRun m G 0 N) := by
  have ht := nativeOperatorTrialVector_actual P hoff bounds hinit hmax N hN Q g constant f G hg e hsec
  dsimp only
  rw [ht]
  let tau := fullVirtualTrialVector P f G 0 bounds N
  let m : OneGradientMethod E := xrfcMethod fullMemory (prescribedTrial tau)
  let A := prescribedOperatorPath Q e
  have hp := fullVirtual_prescribed_endpoint_point P hoff bounds hinit hmax f G N hN
  have hrun : oneGradientFunctionRun m G 0 N = oneGradientRun m A g N := by
    apply oneGradientFunctionRun_eq_of_secants m G A g hg N
    intro i hi
    let C := endpointFunctionRun P.valuesEnabled (endpointComputedTrial P bounds) f G 0 i
    let x := endpointVirtualQuery P.valuesEnabled (endpointComputedTrial P bounds i) C
    have hpoint := hp i hi.le
    have hquery : oneGradientFunctionPoint m G 0 (i+1) = x := by
      rw [hp (i+1) (by omega)]
      simp only [endpointFunctionRun, extendEndpointChart, Fin.snoc_last]
      rfl
    have hstep : m.step (oneGradientFunctionRun m G 0 i) = x-C.1 (Fin.last i) := by
      have hs := oneGradientFunctionPoint_succ m G 0 i
      rw [hpoint, hquery] at hs
      exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using hs.symm)
    have hc := (endpointFunctionRun_cache P.valuesEnabled (endpointComputedTrial P bounds) f G 0 i (Fin.last i)).2
    have hs := hsec i hi
    dsimp only at hs ⊢
    rw [oneGradientFunctionRun_gradient, hpoint, hstep]
    simp only [A, prescribedOperatorPath, dite_eq_left hi]
    change G (C.1 (Fin.last i)+(x-C.1 (Fin.last i))) =
      G (C.1 (Fin.last i))+(Q+e ⟨i, Nat.lt_succ_of_lt hi⟩) (x-C.1 (Fin.last i))
    rw [add_sub_cancel, ←hc]
    exact hs
  constructor
  · rw [fullVirtualOutput_oneGradient_dictionary P hoff f G 0 bounds N]
    change _ = (0+(oneGradientFunctionRun m G 0 N).displacement)+m.output (oneGradientFunctionRun m G 0 N)
    rw [zero_add, hrun]
    rfl
  · change m.outputGradient (Q+e (Fin.last N)) (oneGradientRun m A g N) = _
    rw [hrun]

end
end krylov.XR
