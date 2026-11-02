import krylov.XR.LocalNativePrefixResponse
import krylov.XR.LocalNativeFunctionOutput

/-!
Article: main_krylov, lem:xr-local, full operator-tube quadratic remainder.
Use: the native adaptive trial has the actual fixed-reference first response
with one genuine radius and quadratic constant valid for every small
operator array, at every partial cycle. This is a norm-tube statement,
not only a directional path derivative or an assumed output expansion.
-/
namespace krylov.XR
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Stability
open Set
open scoped InnerProductSpace
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The assembled native I/E1 first variation has a true quadratic
remainder uniformly over all segment-operator perturbations in one ball.
Only the source's primitive endpoint trial C² assumptions enter. -/
theorem native_operator_prefix_quadratic_remainder (P : Parameters) (bounds : SpectralBounds)
    (hinit : P.initialCapacity = n) (hmax : P.maximumCapacity = n)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v, v ≠ 0 → 0 < inner ℝ v (Q v)) (g : E) (constant : ℝ)
    (hg : ∀ i < n, CG.gradient Q g i ≠ 0)
    (htrial : ∀ k < n,
      let C := endpointFunctionRun P.valuesEnabled (endpointComputedTrial P bounds)
        (quadraticObjective Q g constant) (quadraticGradient Q g) 0 k
      0 < endpointComputedTrial P bounds k C ∧ ContDiffAt ℝ 2 (endpointComputedTrial P bounds k) C)
    (N : ℕ) (hN : N ≤ n) :
    let tau₀ := nativeOperatorTrialVector P bounds Q g constant N 0
    let L := fderiv ℝ (fun e => prescribedXRFCOutput Q g N (e,tau₀)) 0
    ∃ delta C : ℝ, 0 < delta ∧ 0 ≤ C ∧
      ∀ e : Fin (N+1) → E →L[ℝ] E, ‖e‖ ≤ delta →
        ‖nativeOperatorOutput P bounds Q g constant N e-
          nativeOperatorOutput P bounds Q g constant N 0-L e‖ ≤ C*‖e‖^2 := by
  let F := nativeOperatorOutput P bounds Q g constant N
  have hF := nativeOperatorOutput_contDiffAt P bounds hinit hmax Q hQ hpos g constant hg htrial N hN
  have hD := native_operator_prefix_first_variation P bounds hinit hmax Q hQ hpos g constant hg htrial N hN
  dsimp only at hD
  obtain ⟨delta,C,hd,hC,hbound⟩ := compact_smooth_taylor F 2 ({0} : Set (Fin (N+1) → E →L[ℝ] E))
    isCompact_singleton (by intro x hx; rw [Set.mem_singleton_iff.mp hx]; exact hF)
  refine ⟨delta,C,hd,hC,?_⟩
  intro e he
  have hb := hbound 0 (Set.mem_singleton 0) e he 2 (by decide) le_rfl
  have hT : taylorPolynomial F 2 0 e = F 0+fderiv ℝ F 0 e := by
    simp only [taylorPolynomial,Finset.sum_range_succ,Finset.sum_range_zero,
      iteratedFDeriv_zero_apply,iteratedFDeriv_one_apply,Nat.factorial_zero,Nat.factorial_one,
      Nat.cast_one,inv_one,one_smul,zero_add]
  rw [hT, hD.fderiv] at hb
  simpa only [zero_add,sub_add_eq_sub_sub] using hb

end
end krylov.XR
