import polyak.ModeLocking.Continuation.DualSystem

/-! Analytic continuation of the actual positive class masses. -/
noncomputable section
namespace polyak.ModeLocking.RegularData
open General Levels Filter
open scoped BigOperators Topology
variable {q : Tuning} {s : ℝ} {L : ℕ} (D : RegularData q s L)

def continuedMatrix (ψ : Continuation.Parameters → (ℝ × (Fin D.d → ℝ)))
    (p : Continuation.Parameters) : Matrix (Fin D.d) (Fin D.d) ℝ :=
  Continuation.tightMatrix D.reps D.atoms ![p 0, p 1, p 2, (ψ p).1]

theorem continuedMatrix_base (ψ : Continuation.Parameters → (ℝ × (Fin D.d → ℝ)))
    (hψ : ψ (Continuation.parameters q) = (s, fun i => (D.primal i : ℝ))) :
    D.continuedMatrix ψ (Continuation.parameters q) = D.matrix := by
  ext r i
  change Continuation.ambientLag (D.reps r) (D.atoms i)
    ![q.kappa, q.y, q.beta, (ψ (Continuation.parameters q)).1] = _
  rw [hψ]
  exact Continuation.ambientLag_actual q s (D.reps r) (D.atoms i)

theorem analyticAt_continuedMatrix (ψ : Continuation.Parameters → (ℝ × (Fin D.d → ℝ)))
    (hψ : AnalyticAt ℝ ψ (Continuation.parameters q))
    (hbase : ψ (Continuation.parameters q) = (s, fun i => (D.primal i : ℝ)))
    (r i : Fin D.d) : AnalyticAt ℝ (fun p => D.continuedMatrix ψ p r i) (Continuation.parameters q) := by
  have hp : AnalyticAt ℝ (fun p : Continuation.Parameters => ![p 0, p 1, p 2, (ψ p).1])
      (Continuation.parameters q) := by
    apply AnalyticAt.pi
    intro j
    fin_cases j
    · exact (ContinuousLinearMap.proj (R := ℝ) (0 : Fin 3) : Continuation.Parameters →L[ℝ] ℝ).analyticAt _
    · exact (ContinuousLinearMap.proj (R := ℝ) (1 : Fin 3) : Continuation.Parameters →L[ℝ] ℝ).analyticAt _
    · exact (ContinuousLinearMap.proj (R := ℝ) (2 : Fin 3) : Continuation.Parameters →L[ℝ] ℝ).analyticAt _
    · exact analyticAt_fst.comp hψ
  have hout : AnalyticAt ℝ (Continuation.ambientLag (D.reps r) (D.atoms i))
      ![(Continuation.parameters q) 0, (Continuation.parameters q) 1,
        (Continuation.parameters q) 2, (ψ (Continuation.parameters q)).1] := by
    rw [hbase]
    exact Continuation.analyticAt_ambientLag q s (D.reps r) (D.atoms i)
  exact hout.comp (f := fun p : Continuation.Parameters => ![p 0, p 1, p 2, (ψ p).1]) hp

theorem analytic_left_continuation (ψ : Continuation.Parameters → (ℝ × (Fin D.d → ℝ)))
    (hψ : AnalyticAt ℝ ψ (Continuation.parameters q))
    (hbase : ψ (Continuation.parameters q) = (s, fun i => (D.primal i : ℝ))) :
    ∃ μ : Continuation.Parameters → (Fin D.d → ℝ), AnalyticAt ℝ μ (Continuation.parameters q) ∧
      μ (Continuation.parameters q) = D.classWeight ∧
      (∀ᶠ p in 𝓝 (Continuation.parameters q),
        Continuation.leftSystem (D.continuedMatrix ψ) D.normalizationIndex
          (∑ r, D.classWeight r) (p, μ p) = 0 ∧ ∀ r, 0 < μ p r) := by
  let f := Continuation.leftSystem (D.continuedMatrix ψ) D.normalizationIndex (∑ r, D.classWeight r)
  have ha : AnalyticAt ℝ f (Continuation.parameters q, D.classWeight) :=
    Continuation.analyticAt_leftSystem _ _ _ _ _ (D.analyticAt_continuedMatrix ψ hψ hbase)
  have hin : HasFDerivAt (fun v : Fin D.d → ℝ => (Continuation.parameters q, v))
      (ContinuousLinearMap.inr ℝ Continuation.Parameters (Fin D.d → ℝ)) D.classWeight :=
    (hasFDerivAt_const (Continuation.parameters q) D.classWeight).prodMk (hasFDerivAt_id _)
  have hcomp := ha.differentiableAt.hasFDerivAt.comp D.classWeight hin
  have he := hcomp.unique (D.hasFDerivAt_leftSystem_partial _ (D.continuedMatrix_base ψ hbase))
  have hinv : (fderiv ℝ f (Continuation.parameters q, D.classWeight) ∘L
      ContinuousLinearMap.inr ℝ Continuation.Parameters (Fin D.d → ℝ)).IsInvertible := by
    rw [he]
    exact ContinuousLinearMap.isInvertible_equiv
  obtain ⟨μ, hμ, hμbase, hμzero⟩ := Continuation.analytic_implicit_function ha hinv
  dsimp only at hμ hμbase hμzero
  refine ⟨μ, hμ, hμbase, ?_⟩
  have hpos (r : Fin D.d) : ∀ᶠ p in 𝓝 (Continuation.parameters q), 0 < μ p r := by
    have hc : ContinuousAt (fun p => μ p r) (Continuation.parameters q) :=
      (continuous_apply r).continuousAt.comp hμ.continuousAt
    apply hc.eventually
    apply eventually_gt_nhds
    change 0 < μ (Continuation.parameters q) r
    rw [hμbase]
    exact D.classWeight_pos r
  have hall := Filter.eventually_all.mpr hpos
  filter_upwards [hμzero, hall] with p hp hpr
  dsimp only [f] at hp
  rw [D.leftSystem_base (D.continuedMatrix_base ψ hbase)] at hp
  exact ⟨hp, hpr⟩

end polyak.ModeLocking.RegularData
