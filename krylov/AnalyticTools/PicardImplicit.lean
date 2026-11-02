import krylov.AnalyticTools.Implicit
import krylov.AnalyticTools.PathIntegral
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
Article: main_krylov, apC:prop:LV, analytic ODE background.
Use: solve the actual rescaled Picard equation analytically in the time
parameter, in the Banach space of continuous paths. Local uniqueness is part
of the result, so the constructed family can be identified with existing flows.
Source: the analytic implicit theorem; the derivative in the path variable at
zero time is the identity. Analyticity of the lifted field is checked separately.
-/

namespace krylov.AnalyticTools
noncomputable section
open Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- An analytic path field has an analytic, locally unique rescaled Picard
family. The integral operator is the genuine compact-path primitive. -/
theorem exists_analytic_picard_family (P : C(PathDomain, E) → C(PathDomain, E))
    (a : E) (hP : AnalyticAt ℝ P (ContinuousMap.const PathDomain a)) :
    ∃ w : ℝ → C(PathDomain, E), AnalyticAt ℝ w 0 ∧
      w 0 = ContinuousMap.const PathDomain a ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), w t = ContinuousMap.const PathDomain a +
        t • pathIntegralCLM (P (w t))) ∧
      ∀ᶠ z in 𝓝 ((0 : ℝ), ContinuousMap.const PathDomain a),
        z.2 = ContinuousMap.const PathDomain a + z.1 • pathIntegralCLM (P z.2) →
          z.2 = w z.1 := by
  let c : C(PathDomain, E) := ContinuousMap.const PathDomain a
  let Q : ℝ × C(PathDomain, E) → C(PathDomain, E) :=
    fun z ↦ z.2 - c - z.1 • pathIntegralCLM (P z.2)
  have hPsnd : AnalyticAt ℝ (fun z : ℝ × C(PathDomain, E) ↦ P z.2) (0, c) :=
    hP.comp (f := Prod.snd) analyticAt_snd
  have hI : AnalyticAt ℝ (fun z : ℝ × C(PathDomain, E) ↦
      pathIntegralCLM (P z.2)) (0, c) :=
    (pathIntegralCLM (E := E)).analyticAt _ |>.comp hPsnd
  have hQ : AnalyticAt ℝ Q (0, c) :=
    (analyticAt_snd.sub analyticAt_const).sub (analyticAt_fst.smul hI)
  let A : ℝ →L[ℝ] C(PathDomain, E) :=
    -ContinuousLinearMap.toSpanSingleton ℝ (pathIntegralCLM (P c))
  have hd : HasFDerivAt Q
      (A.coprod (ContinuousLinearMap.id ℝ C(PathDomain, E))) (0, c) := by
    have h := ((hasFDerivAt_snd (𝕜 := ℝ) (p := ((0 : ℝ), c))).sub
      (hasFDerivAt_const c ((0 : ℝ), c))).sub
        ((hasFDerivAt_fst (𝕜 := ℝ) (p := ((0 : ℝ), c))).smul
          hI.differentiableAt.hasFDerivAt)
    convert h using 1
    apply ContinuousLinearMap.ext
    intro z
    simp [A, ContinuousLinearMap.coprod_apply, sub_eq_add_neg, add_comm]
  obtain ⟨w, hw, hw₀, heq, huniq⟩ := exists_analytic_implicit hQ (by simp [Q])
    A (ContinuousLinearEquiv.refl ℝ C(PathDomain, E)) hd
  refine ⟨w, hw, hw₀, ?_, ?_⟩
  · filter_upwards [heq] with t ht
    exact (sub_eq_iff_eq_add.mp (sub_eq_zero.mp ht)).trans (add_comm _ _)
  · filter_upwards [huniq] with z hz hfix
    apply hz
    change z.2 - c - z.1 • pathIntegralCLM (P z.2) = 0
    apply sub_eq_zero.mpr
    apply sub_eq_iff_eq_add.mpr
    exact hfix.trans (add_comm _ _)

end
end krylov.AnalyticTools
