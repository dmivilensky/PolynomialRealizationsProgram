import krylov.Functions.FCReferenceFields

/-!
Article: main_krylov, lem:cycle-transfer and thm:Htransfer, original varying A₀ references.
Use: obtain true compact-uniform reference control jointly in the original
positive base operator and initial gradient. This includes the actual first
segment secant, rather than freezing the reference at the minimizer Hessian.
Source: genuine joint FC analyticity and the compact derivative tube.
-/

namespace krylov.Functions
noncomputable section
open Set krylov.Methods krylov.Reference krylov.Stability
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- One genuine common tube controls all FC steps around compact varying positive quadratic references.
Article: main_krylov, lem:cycle-transfer, the original base/gradient reference set.
Proof: every real finite input operator is jointly analytic in its original
base and perturbation. The actual quadratic FC domains and true CG prefix
nonstagnation imply actual field analyticity, hence a genuine compact tube. -/
theorem compact_fc_own_reference_step_changes (N : ℕ) (K : Set ((E →L[ℝ] E) × E)) (hK : IsCompact K)
    (hquad : ∀ z ∈ K, z.1.toLinearMap.IsSymmetric ∧
      (∀ v : E, v ≠ 0 → 0 < inner ℝ v (z.1 v)) ∧ ∀ i < N, CG.gradient z.1 z.2 i ≠ 0) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ z ∈ K,
      ∀ Θ : Fin N → E →L[ℝ] E, ‖Θ‖ ≤ δ → ∀ i < N,
      ‖fcStep fullMemory (fcFiniteOperatorPath z.1 N Θ) z.2 i - referenceStep z.1 z.2 i‖ ≤ C * ‖Θ‖ := by
  let F := fun p : ((E →L[ℝ] E) × E) × (Fin N → E →L[ℝ] E) =>
    fun i : Fin N => fcStep fullMemory (fcFiniteOperatorPath p.1.1 N p.2) p.1.2 i.val
  have hF z (hz : z ∈ K) : AnalyticAt ℝ F (z, 0) := by
    have hA i : AnalyticAt ℝ
        (fun p : ((E →L[ℝ] E) × E) × (Fin N → E →L[ℝ] E) => fcFiniteOperatorPath p.1.1 N p.2 i) (z, 0) := by
      by_cases hi : i < N
      · simp only [fcFiniteOperatorPath, dite_eq_left hi]
        let ev := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => E →L[ℝ] E) ⟨i, hi⟩).comp
          (ContinuousLinearMap.snd ℝ ((E →L[ℝ] E) × E) (Fin N → E →L[ℝ] E))
        have hev : AnalyticAt ℝ (fun p : ((E →L[ℝ] E) × E) × (Fin N → E →L[ℝ] E) => p.2 ⟨i, hi⟩) (z, 0) :=
          ev.analyticAt (z, 0)
        exact (analyticAt_fst.comp analyticAt_fst).add hev
      · simp only [fcFiniteOperatorPath, dite_eq_right hi]
        exact analyticAt_fst.comp analyticAt_fst
    have h := quadraticFC_prefix_analytic
      (fun p : ((E →L[ℝ] E) × E) × (Fin N → E →L[ℝ] E) => fcFiniteOperatorPath p.1.1 N p.2)
      (fun p => p.1.2) (z, 0) hA (analyticAt_snd.comp analyticAt_fst) z.1 (fcFiniteOperatorPath_zero z.1 N)
      (hquad z hz).1 (hquad z hz).2.1 N (hquad z hz).2.2
    exact AnalyticAt.pi (fun i => (h.2 i.val i.isLt).2)
  obtain ⟨δ, C, hδ, hC, hbound⟩ := compact_reference_full_first_order F K hK hF
  refine ⟨δ, C, hδ, hC, ?_⟩
  intro z hz Θ hΘ i hi
  have hin : ‖((0 : (E →L[ℝ] E) × E), Θ)‖ = ‖Θ‖ := by simp only [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)]
  have hb := (norm_le_pi_norm (F (z, Θ) - F (z, 0)) (⟨i, hi⟩ : Fin N)).trans
    (by simpa only [add_zero, hin] using hbound z hz 0 Θ (hin ▸ hΘ))
  simpa only [F, Pi.sub_apply, fcFiniteOperatorPath_zero,
    (fullFC_reference_step z.1 (hquad z hz).1 (hquad z hz).2.1 z.2 i).2.2] using hb

end
end krylov.Functions
