import polyak.ModeLocking.Continuation.PrimalDerivative

/-! Analytic continuation of the actual shift and positive normalized right
kernel, derived from the primary regularity conditions by the analytic IFT. -/
noncomputable section
namespace polyak.ModeLocking.RegularData
open General Levels Filter
open scoped BigOperators Topology
variable {q : Tuning} {s : ℝ} {L : ℕ} (D : RegularData q s L)

theorem primalSystem_partial_invertible :
    (fderiv ℝ (Continuation.primalSystem D.reps D.atoms)
      (Continuation.parameters q, s, fun i => (D.primal i : ℝ)) ∘L
        ContinuousLinearMap.inr ℝ Continuation.Parameters (ℝ × (Fin D.d → ℝ))).IsInvertible := by
  have hf := Continuation.analyticAt_primalSystem q s D.reps D.atoms (fun i => (D.primal i : ℝ))
  have hin : HasFDerivAt
      (fun z : ℝ × (Fin D.d → ℝ) => (Continuation.parameters q, z))
      (ContinuousLinearMap.inr ℝ Continuation.Parameters (ℝ × (Fin D.d → ℝ)))
      (s, fun i => (D.primal i : ℝ)) :=
    (hasFDerivAt_const (Continuation.parameters q) (s, fun i => (D.primal i : ℝ))).prodMk (hasFDerivAt_id _)
  have hcomp := hf.differentiableAt.hasFDerivAt.comp (s, fun i => (D.primal i : ℝ)) hin
  have he := hcomp.unique D.hasFDerivAt_primalSystem_partial
  rw [he]
  exact ContinuousLinearMap.isInvertible_equiv

theorem analytic_primal_continuation :
    ∃ ψ : Continuation.Parameters → (ℝ × (Fin D.d → ℝ)),
      AnalyticAt ℝ ψ (Continuation.parameters q) ∧
      ψ (Continuation.parameters q) = (s, fun i => (D.primal i : ℝ)) ∧
      (∀ᶠ p in 𝓝 (Continuation.parameters q),
        Continuation.primalSystem D.reps D.atoms (p, ψ p) = 0 ∧
          ∀ i, 0 < (ψ p).2 i) := by
  obtain ⟨ψ, ha, hbase, hzero⟩ := Continuation.analytic_implicit_function
    (Continuation.analyticAt_primalSystem q s D.reps D.atoms (fun i => (D.primal i : ℝ)))
    D.primalSystem_partial_invertible
  dsimp only at ha hbase hzero
  refine ⟨ψ, ha, hbase, ?_⟩
  have hpos (i : Fin D.d) : ∀ᶠ p in 𝓝 (Continuation.parameters q), 0 < (ψ p).2 i := by
    have hc : ContinuousAt (fun p => (ψ p).2 i) (Continuation.parameters q) :=
      (continuous_apply i).continuousAt.comp ha.continuousAt.snd
    apply hc.eventually
    apply eventually_gt_nhds
    change 0 < (ψ (Continuation.parameters q)).2 i
    rw [hbase]
    exact_mod_cast D.primal_pos i
  have hposall : ∀ᶠ p in 𝓝 (Continuation.parameters q), ∀ i, 0 < (ψ p).2 i :=
    Filter.eventually_all.mpr hpos
  filter_upwards [hzero, hposall] with p hp hweights
  rw [D.primalSystem_base] at hp
  exact ⟨hp, hweights⟩

end polyak.ModeLocking.RegularData
