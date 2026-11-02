import krylov.XR.LocalNativeRemainder

/-!
Article: main_krylov, lem:xr-local and thm:I, printed native full response.
Use: assemble the genuine native step-basis first variation with an actual
quadratic remainder. All native trial regularity is derived from primitive
positive C² endpoint rules, and actual scalar-source outputs are identified
by LocalNativeFunctionOutput and LocalNativeSourceRemainder.
-/
namespace krylov.XR
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Stability krylov.OneGradient krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The full native adaptive operator output has the printed thm:I
step-basis response with a genuine quadratic error estimate. -/
theorem native_XR_operator_full_quadratic_remainder (P : Parameters) (bounds : SpectralBounds)
    (hinit : P.initialCapacity = n) (hmax : P.maximumCapacity = n)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : E) (constant : ℝ) (hatoms : referenceAtomCount base hb g = n) (hn : 0 < n)
    (htrial : ∀ k < n,
      let C := endpointFunctionRun P.valuesEnabled (endpointComputedTrial P bounds)
        (quadraticObjective (cgOperator base) g constant) (quadraticGradient (cgOperator base) g) 0 k
      0 < endpointComputedTrial P bounds k C ∧ ContDiffAt ℝ 2 (endpointComputedTrial P bounds k) C)
    (A : ℝ → ℕ → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ k, ContDiffAt ℝ 2 (fun t => A t k) 0)
    (hsym : ∀ t k, (A t k).IsSymm) (hA₀ : ∀ k, A 0 k = base) :
    let Q := cgOperator base
    let tau₀ := nativeOperatorTrialVector P bounds Q g constant n 0
    let R := cgOperator (metricRoot base)⁻¹
    let errors := fun t (i : Fin (n+1)) => cgOperator (A t i.val)-Q
    ∃ delta C : ℝ, 0 < delta ∧ 0 ≤ C ∧ ∀ t : ℝ, |t| ≤ delta →
      ‖R (nativeOperatorOutput P bounds Q g constant n (errors t)).2-
        t • xrfcStepResponse (prescribedTrial tau₀) base g
          (fun l => R*(deriv (fun t => cgOperator (A t (l+1))) 0-
            deriv (fun t => cgOperator (A t l)) 0)*R)‖ ≤ C*t^2 := by
  let Q := cgOperator base
  let tau₀ := nativeOperatorTrialVector P bounds Q g constant n 0
  let R := cgOperator (metricRoot base)⁻¹
  let errors := fun t (i : Fin (n+1)) => cgOperator (A t i.val)-Q
  let F := fun t => R (nativeOperatorOutput P bounds Q g constant n (errors t)).2
  have hp := cgOperator_positive base hb
  have hg : ∀ i<n, CG.gradient Q g i ≠ 0 := by simpa only [hatoms] using cg_nonstagnation base hb g
  have herrors : ContDiffAt ℝ 2 errors 0 := by
    apply contDiffAt_pi.mpr
    intro i
    exact (matrixOperator_contDiffAt _ 0 (hA i.val)).sub contDiffAt_const
  have he₀ : errors 0 = 0 := by funext i; simp only [errors,hA₀,Q,sub_self,Pi.zero_apply]
  have houter : ContDiffAt ℝ 2 (nativeOperatorOutput P bounds Q g constant n) (errors 0) := by
    rw [he₀]
    exact nativeOperatorOutput_contDiffAt P bounds hinit hmax Q hp.1 hp.2 g constant hg htrial n le_rfl
  have hF : ContDiffAt ℝ 2 F 0 := R.contDiff.contDiffAt.comp (0:ℝ) ((houter.comp (0:ℝ) herrors).snd)
  have hj := native_XR_operator_full_response P bounds hinit hmax base hb g constant hatoms hn htrial A hA hsym hA₀
  obtain ⟨delta,C,hd,hC,hbound⟩ := c2_first_order_remainder F _ hF hj
  have hposTau := nativeOperatorTrialVector_zero_pos P bounds Q g constant n (fun k hk => (htrial k hk).1)
  have hz := prescribedXRFCOutput_zero Q hp.1 hp.2 g n hg tau₀ (fun i => (hposTau i).ne')
  have hcg : CG.gradient Q g n = 0 := by simpa only [hatoms] using cg_terminates base hb g
  have hzero : F 0 = 0 := by
    change R (nativeOperatorOutput P bounds Q g constant n (errors 0)).2 = 0
    rw [he₀]
    change R (prescribedXRFCOutput Q g n (0,tau₀)).2 = 0
    rw [hz,hcg,map_zero]
  refine ⟨delta,C,hd,hC,?_⟩
  intro t ht
  simpa only [hzero,sub_zero] using hbound t ht

end
end krylov.XR
