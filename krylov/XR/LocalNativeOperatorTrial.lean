import krylov.XR.LocalOperatorProgram
import krylov.XR.LocalRegularTrialTransfer

/-!
Article: main_krylov, lem:xr-local, native operator-input trial vector.
Use: derive C² of XR's own actual trial vector in segment-operator
coordinates from the original primitive endpoint hypotheses. The native
trial function is not replaced by a fixed or externally supplied policy.
The ordinary branch's scalar-value independence is proved in the executor.
-/
namespace krylov.XR
noncomputable section
open Matrix krylov.Methods krylov.Reference Filter Topology Asymptotics
open scoped InnerProductSpace
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- XR's actual computed trial vector evaluated by the finite real
operator-input endpoint executor. -/
def nativeOperatorTrialVector (P : Parameters) (bounds : SpectralBounds)
    (Q : E →L[ℝ] E) (g : E) (constant : ℝ) (N : ℕ)
    (e : Fin (N+1) → E →L[ℝ] E) : Fin N → ℝ :=
  fun i => endpointComputedTrial P bounds i.val
    (endpointOperatorRun P.valuesEnabled (endpointComputedTrial P bounds) Q g constant
      (prescribedOperatorPath Q e) i.val)

/-- Primitive C² endpoint trial hypotheses imply C² of the native trial
vector in actual segment-operator variables; no such regularity is an input. -/
theorem nativeOperatorTrialVector_contDiffAt (P : Parameters) (bounds : SpectralBounds)
    (hinit : P.initialCapacity = n) (hmax : P.maximumCapacity = n)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v, v ≠ 0 → 0 < inner ℝ v (Q v)) (g : E) (constant : ℝ)
    (hg : ∀ i < n, CG.gradient Q g i ≠ 0)
    (htrial : ∀ k < n,
      let C := endpointFunctionRun P.valuesEnabled (endpointComputedTrial P bounds)
        (quadraticObjective Q g constant) (quadraticGradient Q g) 0 k
      0 < endpointComputedTrial P bounds k C ∧ ContDiffAt ℝ 2 (endpointComputedTrial P bounds k) C) :
    ContDiffAt ℝ 2 (nativeOperatorTrialVector P bounds Q g constant n) 0 := by
  have hdomains := quadratic_endpointProgram_domains P bounds hinit hmax Q hQ hpos g constant hg htrial
  have hcharts := endpointOperatorRun_contDiffAt P.valuesEnabled (endpointComputedTrial P bounds)
    Q g constant n hdomains
  apply contDiffAt_pi.mpr
  intro i
  have hc := hcharts i.val i.isLt.le
  have ht := (htrial i.val i.isLt).2
  have hz : endpointOperatorRun P.valuesEnabled (endpointComputedTrial P bounds) Q g constant
      (prescribedOperatorPath Q (0 : Fin (n+1) → E →L[ℝ] E)) i.val =
      endpointFunctionRun P.valuesEnabled (endpointComputedTrial P bounds)
        (quadraticObjective Q g constant) (quadraticGradient Q g) 0 i.val := by
    rw [prescribedOperatorPath_zero, endpointOperatorRun_quadratic]
  rw [←hz] at ht
  exact ht.comp 0 hc

/-- Every actual native reference trial is strictly positive; positivity
is read from the primitive reference assumption, not from a desired jet. -/
theorem nativeOperatorTrialVector_zero_pos (P : Parameters) (bounds : SpectralBounds)
    (Q : E →L[ℝ] E) (g : E) (constant : ℝ) (N : ℕ)
    (htrial : ∀ k < N,
      0 < endpointComputedTrial P bounds k
        (endpointFunctionRun P.valuesEnabled (endpointComputedTrial P bounds)
          (quadraticObjective Q g constant) (quadraticGradient Q g) 0 k)) :
    ∀ i, 0 < nativeOperatorTrialVector P bounds Q g constant N 0 i := by
  intro i
  unfold nativeOperatorTrialVector
  rw [prescribedOperatorPath_zero, endpointOperatorRun_quadratic]
  exact htrial i.val i.isLt

/-- The actual native ordinary trial rule gives the same first response
as its fixed reference trials, with a proved quadratic remainder. Both
operator regularity and first-order trial drift are derived internally. -/
theorem nativeOperatorTrialVector_quadratic_transfer (P : Parameters) (bounds : SpectralBounds)
    (hinit : P.initialCapacity = n) (hmax : P.maximumCapacity = n)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v, v ≠ 0 → 0 < inner ℝ v (Q v)) (g : E) (constant : ℝ)
    (hg : ∀ i < n, CG.gradient Q g i ≠ 0)
    (htrial : ∀ k < n,
      let C := endpointFunctionRun P.valuesEnabled (endpointComputedTrial P bounds)
        (quadraticObjective Q g constant) (quadraticGradient Q g) 0 k
      0 < endpointComputedTrial P bounds k C ∧ ContDiffAt ℝ 2 (endpointComputedTrial P bounds k) C) :
    let tau := nativeOperatorTrialVector P bounds Q g constant n
    (fun e => prescribedXRFCOutput Q g n (e,tau e)-prescribedXRFCOutput Q g n (e,tau 0))
      =O[𝓝 0] (fun e : Fin (n+1) → E →L[ℝ] E => ‖e‖^2) := by
  let tau := nativeOperatorTrialVector P bounds Q g constant n
  exact prescribedXRFC_regular_trial_transfer Q hQ hpos g n hg (tau 0)
    (fun i => (nativeOperatorTrialVector_zero_pos P bounds Q g constant n
      (fun k hk => (htrial k hk).1) i).ne') tau
    ((nativeOperatorTrialVector_contDiffAt P bounds hinit hmax Q hQ hpos g constant hg htrial).differentiableAt
      (by norm_num)) rfl

/-- Primitive C² endpoint trial hypotheses imply C² of the native trial
vector in actual segment-operator variables; no such regularity is an input. -/
theorem nativeOperatorTrialVector_prefix_contDiffAt (P : Parameters) (bounds : SpectralBounds)
    (hinit : P.initialCapacity = n) (hmax : P.maximumCapacity = n) (N : ℕ) (hN : N ≤ n)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v, v ≠ 0 → 0 < inner ℝ v (Q v)) (g : E) (constant : ℝ)
    (hg : ∀ i < n, CG.gradient Q g i ≠ 0)
    (htrial : ∀ k < n,
      let C := endpointFunctionRun P.valuesEnabled (endpointComputedTrial P bounds)
        (quadraticObjective Q g constant) (quadraticGradient Q g) 0 k
      0 < endpointComputedTrial P bounds k C ∧ ContDiffAt ℝ 2 (endpointComputedTrial P bounds k) C) :
    ContDiffAt ℝ 2 (nativeOperatorTrialVector P bounds Q g constant N) 0 := by
  have hdomains := quadratic_endpointProgram_domains P bounds hinit hmax Q hQ hpos g constant hg htrial
  have hcharts := endpointOperatorRun_contDiffAt P.valuesEnabled (endpointComputedTrial P bounds)
    Q g constant N (fun k hk => hdomains k (hk.trans_le hN))
  apply contDiffAt_pi.mpr
  intro i
  have hc := hcharts i.val i.isLt.le
  have ht := (htrial i.val (i.isLt.trans_le hN)).2
  have hz : endpointOperatorRun P.valuesEnabled (endpointComputedTrial P bounds) Q g constant
      (prescribedOperatorPath Q (0 : Fin (N+1) → E →L[ℝ] E)) i.val =
      endpointFunctionRun P.valuesEnabled (endpointComputedTrial P bounds)
        (quadraticObjective Q g constant) (quadraticGradient Q g) 0 i.val := by
    rw [prescribedOperatorPath_zero, endpointOperatorRun_quadratic]
  rw [←hz] at ht
  exact ht.comp 0 hc


end
end krylov.XR
