import polyak.ModeLocking.Continuation.Implicit
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Analytic solution of an actual nonsingular finite linear system. This
applies to the pinning matrix and its slope moments. -/
noncomputable section
namespace polyak.ModeLocking.Continuation
open Filter
open scoped BigOperators Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {d : ℕ}

theorem analytic_linear_solution (A : E → Matrix (Fin d) (Fin d) ℝ)
    (b : E → (Fin d → ℝ)) (x₀ : E) (v₀ : Fin d → ℝ)
    (hA : ∀ r i, AnalyticAt ℝ (fun x => A x r i) x₀)
    (hb : AnalyticAt ℝ b x₀) (hdet : (A x₀).det ≠ 0)
    (hbase : (A x₀).mulVec v₀ = b x₀) :
    ∃ v : E → (Fin d → ℝ), AnalyticAt ℝ v x₀ ∧ v x₀ = v₀ ∧
      ∀ᶠ x in 𝓝 x₀, (A x).mulVec (v x) = b x := by
  let C : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ) :=
    (LinearEquiv.ofBijective (A x₀).mulVecLin
      ⟨Matrix.mulVec_injective_of_det_ne_zero hdet,
        LinearMap.surjective_of_injective (Matrix.mulVec_injective_of_det_ne_zero hdet)⟩).toContinuousLinearEquiv
  let f : E × (Fin d → ℝ) → (Fin d → ℝ) := fun z => (A z.1).mulVec z.2 - b z.1
  have hfst : AnalyticAt ℝ (fun z : E × (Fin d → ℝ) => z.1) (x₀, v₀) := analyticAt_fst
  have hsnd : AnalyticAt ℝ (fun z : E × (Fin d → ℝ) => z.2) (x₀, v₀) := analyticAt_snd
  have ha : AnalyticAt ℝ f (x₀, v₀) := by
    apply AnalyticAt.pi
    intro r
    have hcoord (i : Fin d) : AnalyticAt ℝ (fun z : E × (Fin d → ℝ) => z.2 i) (x₀, v₀) := by
      have hc : AnalyticAt ℝ (fun v : Fin d → ℝ => v i) v₀ :=
        (ContinuousLinearMap.proj (R := ℝ) i : (Fin d → ℝ) →L[ℝ] ℝ).analyticAt v₀
      exact hc.comp (f := fun z : E × (Fin d → ℝ) => z.2) hsnd
    have hmul : AnalyticAt ℝ (fun z : E × (Fin d → ℝ) =>
        ∑ i, A z.1 r i * z.2 i) (x₀, v₀) :=
      Finset.analyticAt_fun_sum Finset.univ (fun i _ => by
        have hentry : AnalyticAt ℝ (fun z : E × (Fin d → ℝ) => A z.1 r i) (x₀, v₀) :=
          (hA r i).comp (g := fun x : E => A x r i) hfst
        exact hentry.mul (hcoord i))
    have hbr : AnalyticAt ℝ (fun z : E × (Fin d → ℝ) => b z.1 r) (x₀, v₀) := by
      have hc : AnalyticAt ℝ (fun v : Fin d → ℝ => v r) (b x₀) :=
        (ContinuousLinearMap.proj (R := ℝ) r : (Fin d → ℝ) →L[ℝ] ℝ).analyticAt (b x₀)
      exact (hc.comp hb).comp (f := fun z : E × (Fin d → ℝ) => z.1) hfst
    exact hmul.sub hbr
  have hin : HasFDerivAt (fun v : Fin d → ℝ => (x₀, v))
      (ContinuousLinearMap.inr ℝ E (Fin d → ℝ)) v₀ :=
    (hasFDerivAt_const x₀ v₀).prodMk (hasFDerivAt_id _)
  have hp : HasFDerivAt (fun v => f (x₀, v)) C.toContinuousLinearMap v₀ :=
    C.toContinuousLinearMap.hasFDerivAt.sub_const (b x₀)
  have he := (ha.differentiableAt.hasFDerivAt.comp v₀ hin).unique hp
  have hinv : (fderiv ℝ f (x₀, v₀) ∘L ContinuousLinearMap.inr ℝ E (Fin d → ℝ)).IsInvertible := by
    rw [he]
    exact ContinuousLinearMap.isInvertible_equiv
  obtain ⟨v, hv, hval, hsol⟩ := analytic_implicit_function ha hinv
  dsimp only at hv hval hsol
  refine ⟨v, hv, hval, ?_⟩
  have hfbase : f (x₀, v₀) = 0 := by change (A x₀).mulVec v₀ - b x₀ = 0; rw [hbase, sub_self]
  filter_upwards [hsol] with x hx
  rw [hfbase] at hx
  exact sub_eq_zero.mp hx

end polyak.ModeLocking.Continuation
