import krylov.Functions.FCOwnReferenceFields
import krylov.Functions.FCLeadingCoordinates

/-!
Article: main_krylov, lem:cycle-transfer and thm:Htransfer, original varying-base FC response.
Use: provide a genuine common Taylor tube for the terminal FC map with the
actual first secant as its varying positive base. The leading coefficient
is the previously identified true FC derivative, not an assumed response.
Source: actual joint FC analyticity and the proved compact Taylor theorem.
-/

namespace krylov.Functions
noncomputable section
open Set Metric krylov.Methods krylov.Reference krylov.Stability
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- The actual finite terminal FC map with its original base operator as a genuine reference coordinate.
Article: main_krylov, lem:cycle-transfer, original own-base operator map. -/
def fcOwnFiniteTerminal (N : ℕ)
    (p : ((E →L[ℝ] E) × E) × (Fin N → E →L[ℝ] E)) : E :=
  fcFiniteTerminal p.1.1 N (p.1.2, p.2)

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- The actual own-base finite FC map is jointly analytic at its genuine nondegenerate quadratic references.
Article: main_krylov, lem:U and thm:Htransfer. -/
theorem fcOwnFiniteTerminal_analytic (N : ℕ) (z : (E →L[ℝ] E) × E)
    (hQ : z.1.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v ≠ 0 → 0 < inner ℝ v (z.1 v))
    (hpre : ∀ i < N, CG.gradient z.1 z.2 i ≠ 0) :
    AnalyticAt ℝ (fcOwnFiniteTerminal N) (z, 0) := by
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
  exact (quadraticFC_prefix_analytic
    (fun p : ((E →L[ℝ] E) × E) × (Fin N → E →L[ℝ] E) => fcFiniteOperatorPath p.1.1 N p.2)
    (fun p => p.1.2) (z, 0) hA (analyticAt_snd.comp analyticAt_fst) z.1
    (fcFiniteOperatorPath_zero z.1 N) hQ hpos N hpre).1

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- The true source derivative of the varying-base map is exactly the established actual fixed-base FC derivative.
Article: main_krylov, thm:Htransfer, genuine original-base coefficient. -/
theorem fcOwnFiniteTerminal_fderiv_source (N : ℕ) (z : (E →L[ℝ] E) × E)
    (hQ : z.1.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v ≠ 0 → 0 < inner ℝ v (z.1 v))
    (hpre : ∀ i < N, CG.gradient z.1 z.2 i ≠ 0) (Θ : Fin N → E →L[ℝ] E) :
    fderiv ℝ (fcOwnFiniteTerminal N) (z, 0) (0, Θ) = fcLeadingOperator z.1 N z.2 Θ := by
  have hin : HasFDerivAt (fun θ : Fin N → E →L[ℝ] E => (z, θ))
      (ContinuousLinearMap.inr ℝ ((E →L[ℝ] E) × E) (Fin N → E →L[ℝ] E)) 0 := by
    simpa only [Prod.mk_add_mk, add_zero, zero_add, ContinuousLinearMap.inr_apply] using
      ((ContinuousLinearMap.inr ℝ ((E →L[ℝ] E) × E) (Fin N → E →L[ℝ] E)).hasFDerivAt
        (x := (0 : Fin N → E →L[ℝ] E))).const_add (z, 0)
  have hfixed : HasFDerivAt (fun θ : Fin N → E →L[ℝ] E => (z.2, θ))
      (ContinuousLinearMap.inr ℝ E (Fin N → E →L[ℝ] E)) 0 := by
    simpa only [Prod.mk_add_mk, add_zero, zero_add, ContinuousLinearMap.inr_apply] using
      ((ContinuousLinearMap.inr ℝ E (Fin N → E →L[ℝ] E)).hasFDerivAt
        (x := (0 : Fin N → E →L[ℝ] E))).const_add (z.2, 0)
  have hd₁ := (fcOwnFiniteTerminal_analytic N z hQ hpos hpre).differentiableAt.hasFDerivAt.comp 0 hin
  have hd₂ := (fcFiniteTerminal_analytic z.1 hQ hpos N z.2 hpre).differentiableAt.hasFDerivAt.comp 0 hfixed
  have he := congrArg (fun A : (Fin N → E →L[ℝ] E) →L[ℝ] E => A Θ) (hd₁.unique hd₂)
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, fcLeadingOperator] using he

/-- The genuine actual FC leading response and quadratic remainder are uniform over compact varying original bases and gradients.
Article: main_krylov, lem:cycle-transfer, own-A₀ response tube.
Proof: apply the compact Taylor and derivative tubes on the true analytic
domain. Actual finite-dimensional CG termination cancels the quadratic
reference value; actual partial differentiation identifies its true first jet. -/
theorem compact_fc_own_leading_operator (K : Set ((E →L[ℝ] E) × E)) (hK : IsCompact K)
    (hquad : ∀ z ∈ K, z.1.toLinearMap.IsSymmetric ∧
      (∀ v : E, v ≠ 0 → 0 < inner ℝ v (z.1 v)) ∧
      ∀ i < Module.finrank ℝ E, CG.gradient z.1 z.2 i ≠ 0) :
    ∃ δ C M : ℝ, 0 < δ ∧ 0 ≤ C ∧ 0 ≤ M ∧
      (∀ z ∈ K, ∀ Θ : Fin (Module.finrank ℝ E) → E →L[ℝ] E,
        ‖fcLeadingOperator z.1 (Module.finrank ℝ E) z.2 Θ‖ ≤ M * ‖Θ‖) ∧
      ∀ z ∈ K, ∀ Θ : Fin (Module.finrank ℝ E) → E →L[ℝ] E, ‖Θ‖ ≤ δ →
      ‖fcOwnFiniteTerminal (Module.finrank ℝ E) (z, Θ) -
        fcLeadingOperator z.1 (Module.finrank ℝ E) z.2 Θ‖ ≤ C * ‖Θ‖ ^ 2 := by
  let N := Module.finrank ℝ E
  let F := fcOwnFiniteTerminal (E := E) N
  let U := {p | AnalyticAt ℝ F p}
  let K₀ : Set (((E →L[ℝ] E) × E) × (Fin N → E →L[ℝ] E)) := K ×ˢ {0}
  have hK₀ : IsCompact K₀ := hK.prod isCompact_singleton
  have hsub : K₀ ⊆ U := by
    rintro ⟨z, θ⟩ ⟨hz, hθ⟩
    rw [Set.mem_singleton_iff] at hθ
    change θ = 0 at hθ
    subst θ
    exact fcOwnFiniteTerminal_analytic N z (hquad z hz).1 (hquad z hz).2.1 (hquad z hz).2.2
  have hF : ContDiffOn ℝ 2 F U := fun _ hp => hp.contDiffAt.contDiffWithinAt
  obtain ⟨δ, C, hδ, hC, hbound⟩ := compact_taylor_remainders F 2 U K₀ (isOpen_analyticAt ℝ F) hK₀ hsub hF
  obtain ⟨ρ, M, _, hM, _, hD⟩ := compact_derivative_tube F 2 U K₀ (isOpen_analyticAt ℝ F) hK₀ hsub hF
  refine ⟨δ, C, M, hδ, hC, hM, ?_, ?_⟩
  · intro z hz Θ
    have hmem : (z, (0 : Fin N → E →L[ℝ] E)) ∈ cthickening ρ K₀ := self_subset_cthickening K₀ ⟨hz, rfl⟩
    have hb := hD 1 (by decide) (z, 0) hmem
    rw [norm_iteratedFDeriv_one] at hb
    have ha := (fderiv ℝ F (z, 0)).le_opNorm ((0 : (E →L[ℝ] E) × E), Θ)
    rw [fcOwnFiniteTerminal_fderiv_source N z (hquad z hz).1 (hquad z hz).2.1 (hquad z hz).2.2] at ha
    simp only [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)] at ha
    exact ha.trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
  · intro z hz Θ hΘ
    have hin : ‖((0 : (E →L[ℝ] E) × E), Θ)‖ = ‖Θ‖ := by simp only [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)]
    have hzero : F (z, 0) = 0 := fcFiniteTerminal_reference_zero z.1 (hquad z hz).1 (hquad z hz).2.1 z.2
    have hlin := fcOwnFiniteTerminal_fderiv_source N z (hquad z hz).1 (hquad z hz).2.1 (hquad z hz).2.2 Θ
    have ht : taylorPolynomial F 2 (z, 0) (0, Θ) = fcLeadingOperator z.1 N z.2 Θ := by
      simp only [taylorPolynomial, Finset.sum_range_succ, Finset.sum_range_zero,
        iteratedFDeriv_zero_apply, iteratedFDeriv_one_apply, Nat.factorial_zero, Nat.factorial_one,
        Nat.cast_one, inv_one, one_smul, zero_add, hzero]
      exact hlin
    have hb := hbound (z, 0) ⟨hz, rfl⟩ (0, Θ) (hin ▸ hΘ) 2 (by decide) le_rfl
    rw [ht] at hb
    simpa only [Prod.mk_add_mk, add_zero, zero_add, hin] using hb

end
end krylov.Functions
