import krylov.XR.LocalNativeOperatorVariation

/-!
Article: main_krylov, lem:xr-local, true native scalar-source output.
Use: every input coordinate of the assembled native operator response is
constructed from the genuine Hessian average of its actual query/output
segment. The function gradient at the output follows from the real FTC;
no desired output expansion or an abstract gradient model is an input.
-/
namespace krylov.XR
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Convergence chebyshev1.Nonlinear
open scoped InnerProductSpace
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Real evaluated segment averages plus the genuine semantic output
segment average, centered at the fixed reference Hessian. -/
def nativeFunctionErrorInputs (P : Parameters) (bounds : SpectralBounds)
    (Q : E →L[ℝ] E) (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    (N : ℕ) : Fin (N+1) → E →L[ℝ] E := fun i =>
  if i.val < N then endpointFunctionOperator P bounds f G H i.val-Q else
    let S := fullVirtualRun P (algorithmTrialParameter P) f G 0 bounds N
    averagedDerivative H S.point (fullVirtualCorrection P S)-Q

/-- The assembled native response equals the genuine function's actual
unevaluated output and its true gradient. All operator coordinates are
actual Hessian averages, and all required secant identities are proved. -/
theorem nativeOperatorOutput_actual_gradient (P : Parameters) (hoff : P.valuesEnabled = false)
    (bounds : SpectralBounds) (hinit : P.initialCapacity = n) (hmax : P.maximumCapacity = n)
    (Q : E →L[ℝ] E) (g : E) (constant : ℝ) (f : E → ℝ) (G : E → E)
    (H : E → E →L[ℝ] E) (hg : G 0 = g) (N : ℕ) (hN : N ≤ n)
    (hH : ∀ k<N,
      let C := endpointFunctionRun P.valuesEnabled (endpointComputedTrial P bounds) f G 0 k
      let s := endpointVirtualQuery P.valuesEnabled (endpointComputedTrial P bounds k) C-C.1 (Fin.last k)
      ContinuousOn (fun t : ℝ => H (C.1 (Fin.last k)+t • s)) (Set.Icc 0 1))
    (hG : ∀ k<N,
      let C := endpointFunctionRun P.valuesEnabled (endpointComputedTrial P bounds) f G 0 k
      let s := endpointVirtualQuery P.valuesEnabled (endpointComputedTrial P bounds k) C-C.1 (Fin.last k)
      ∀ t ∈ Set.Icc (0:ℝ) 1, HasFDerivAt G (H (C.1 (Fin.last k)+t • s)) (C.1 (Fin.last k)+t • s))
    (hHo : let S := fullVirtualRun P (algorithmTrialParameter P) f G 0 bounds N
      ContinuousOn (fun t : ℝ => H (S.point+t • fullVirtualCorrection P S)) (Set.Icc 0 1))
    (hGo : let S := fullVirtualRun P (algorithmTrialParameter P) f G 0 bounds N
      ∀ t ∈ Set.Icc (0:ℝ) 1, HasFDerivAt G (H (S.point+t • fullVirtualCorrection P S))
        (S.point+t • fullVirtualCorrection P S)) :
    nativeOperatorOutput P bounds Q g constant N (nativeFunctionErrorInputs P bounds Q f G H N) =
      (fullVirtualOutput P (algorithmTrialParameter P) f G 0 bounds N,
        G (fullVirtualOutput P (algorithmTrialParameter P) f G 0 bounds N)) := by
  let e := nativeFunctionErrorInputs P bounds Q f G H N
  have hsec (k : ℕ) (hk : k<N) := endpointFunctionOperator_secant P bounds f G H k (hH k hk) (hG k hk)
  have hs (k : ℕ) (hk : k<N) : Q+e ⟨k,Nat.lt_succ_of_lt hk⟩ = endpointFunctionOperator P bounds f G H k := by
    simp only [e, nativeFunctionErrorInputs, ite_eq_left hk]
    abel
  have hdict := fullVirtualOutput_native_operator_dictionary P hoff bounds hinit hmax Q g constant f G hg N hN e
    (fun k hk => by simpa only [hs k hk] using hsec k hk)
  have ht := nativeOperatorTrialVector_actual P hoff bounds hinit hmax N hN Q g constant f G hg e
    (fun k hk => by simpa only [hs k hk] using hsec k hk)
  apply Prod.ext
  · exact hdict.1
  · unfold nativeOperatorOutput
    rw [hdict.2, ht]
    let tau := fullVirtualTrialVector P f G 0 bounds N
    let m : OneGradientMethod E := xrfcMethod fullMemory (prescribedTrial tau)
    let S := fullVirtualRun P (algorithmTrialParameter P) f G 0 bounds N
    let Hq := oneGradientFunctionRun m G 0 N
    have hi := fullVirtualRun_oneGradient_dictionary P hoff f G 0 bounds N N le_rfl
    have hc : m.output Hq = fullVirtualCorrection P S := by
      change virtualCorrection (selectedWindow fullMemory Hq) Hq.gradient = _
      rw [selectedWindow_full, hi.2.1, hi.2.2, (xrfcNewestPairs_virtual S.pairs S.gradient).1]
      unfold fullVirtualCorrection fullVirtualSelectedModel
      simp only [hoff, Bool.false_eq_true, ite_false]
    have hb : Q+e (Fin.last N) = averagedDerivative H S.point (fullVirtualCorrection P S) := by
      simp only [e, nativeFunctionErrorInputs, Fin.val_last, lt_self_iff_false, ite_false]
      abel
    have hf := averagedDerivative_apply G H S.point (fullVirtualCorrection P S) hHo hGo
    change Hq.gradient+(Q+e (Fin.last N)) (m.output Hq) = _
    rw [hc, hb, hi.2.1, (fullVirtualRun_cache P (algorithmTrialParameter P) f G 0 bounds N).2, hf]
    change G S.point + (G (S.point+fullVirtualCorrection P S)-G S.point) = _
    rw [add_sub_cancel]
    rfl

end
end krylov.XR
