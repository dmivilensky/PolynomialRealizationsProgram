import krylov.Stability.AnalyticFC
import krylov.Stability.CompactFirstOrder
import krylov.Methods.HomogeneousFC
import krylov.Methods.FiniteOracleCharts

/-!
Article: main_krylov, lem:cycle-transfer, compact native quadratic-reference stability.
Use: derive a common first-order bound for every actual FC direction and line
step from the existing genuine analytic policy execution near the complete
compact family of nondegenerate quadratic references.
Source: lem:U, the proved analytic FC induction and compact Taylor tube.
-/

namespace krylov.Functions
noncomputable section
open Set krylov.Methods krylov.Reference krylov.Stability
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A finite genuine additive operator perturbation, extended by the original quadratic after the cycle.
Article: main_krylov, lem:cycle-transfer, finite operator input coordinates. -/
def fcFiniteOperatorPath (Q : E →L[ℝ] E) (N : ℕ) (Θ : Fin N → E →L[ℝ] E) (i : ℕ) : E →L[ℝ] E :=
  if h : i < N then Q + Θ ⟨i, h⟩ else Q

/-- The finite operator path is exactly the quadratic reference at zero input.
Article: main_krylov, lem:cycle-transfer. -/
theorem fcFiniteOperatorPath_zero (Q : E →L[ℝ] E) (N : ℕ) :
    fcFiniteOperatorPath Q N 0 = fun _ => Q := by
  ext i
  simp [fcFiniteOperatorPath]

/-- Every genuine finite operator input map is analytic, including the fixed tail.
Article: main_krylov, lem:cycle-transfer, primitive reference input regularity. -/
theorem fcFiniteOperatorPath_analytic (Q : E →L[ℝ] E) (N i : ℕ)
    (z : E × (Fin N → E →L[ℝ] E)) :
    AnalyticAt ℝ (fun z : E × (Fin N → E →L[ℝ] E) => fcFiniteOperatorPath Q N z.2 i) z := by
  by_cases hi : i < N
  · simp only [fcFiniteOperatorPath, dite_eq_left hi]
    exact analyticAt_const.add
      (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => E →L[ℝ] E) ⟨i, hi⟩).analyticAt z.2).comp analyticAt_snd)
  · simp only [fcFiniteOperatorPath, dite_eq_right hi]
    exact analyticAt_const

/-- The actual FC step reads only its true finite operator prefix, including its current search operator.
Article: main_krylov, lem:cycle-transfer, exact finite oracle coordinates. -/
theorem fcStep_congr_operator_prefix (A B : ℕ → E →L[ℝ] E) (g : E)
    (N i : ℕ) (hi : i < N) (hAB : ∀ j < N, A j = B j) :
    fcStep fullMemory A g i = fcStep fullMemory B g i := by
  have hh := methodRun_congr_prefix (fcMethod fullMemory) A A B B g i
    (fun j hj => hAB j (hj.trans hi)) (fun j hj => hAB j (hj.trans hi))
  simp only [fcStep, fcGradient, fcDirection, fcHistory]
  rw [hh, hAB i hi]

variable [CompleteSpace E] [FiniteDimensional ℝ E]

/-- One common actual compact-reference neighborhood controls all FC directions and line steps.
Article: main_krylov, lem:cycle-transfer, native quadratic-reference stability.
Proof: the actual FC analytic theorem discharges every solve and search
denominator from true nondegenerate CG data; apply the existing compact
first-order theorem to the finite product of genuine executed fields. -/
theorem compact_fc_reference_field_changes (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v ≠ 0 → 0 < inner ℝ v (Q v))
    (N : ℕ) (K : Set E) (hK : IsCompact K)
    (hpre : ∀ g ∈ K, ∀ i < N, CG.gradient Q g i ≠ 0) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ g ∈ K, ∀ v : E,
      ∀ Θ : Fin N → E →L[ℝ] E, ‖(v, Θ)‖ ≤ δ → ∀ i < N,
      ‖fcDirection fullMemory (fcFiniteOperatorPath Q N Θ) (g + v) i - CG.direction Q g i‖ ≤ C * ‖(v, Θ)‖ ∧
      ‖fcStep fullMemory (fcFiniteOperatorPath Q N Θ) (g + v) i - referenceStep Q g i‖ ≤ C * ‖(v, Θ)‖ := by
  let F := fun z : E × (Fin N → E →L[ℝ] E) => fun i : Fin N =>
    (fcDirection fullMemory (fcFiniteOperatorPath Q N z.2) z.1 i.val,
      fcStep fullMemory (fcFiniteOperatorPath Q N z.2) z.1 i.val)
  have hF g (hg : g ∈ K) : AnalyticAt ℝ F (g, 0) := by
    have h := quadraticFC_prefix_analytic
      (fun z : E × (Fin N → E →L[ℝ] E) => fcFiniteOperatorPath Q N z.2) Prod.fst (g, 0)
      (fun i => fcFiniteOperatorPath_analytic Q N i (g, 0)) analyticAt_fst Q
      (fcFiniteOperatorPath_zero Q N) hQ hpos N (hpre g hg)
    apply AnalyticAt.pi
    intro i
    exact (h.2 i.val i.isLt).1.prod (h.2 i.val i.isLt).2
  obtain ⟨δ, C, hδ, hC, hbound⟩ := compact_reference_full_first_order F K hK hF
  refine ⟨δ, C, hδ, hC, ?_⟩
  intro g hg v Θ hΘ i hi
  have hb := (norm_le_pi_norm (F (g + v, Θ) - F (g, 0)) (⟨i, hi⟩ : Fin N)).trans
    (hbound g hg v Θ hΘ)
  have hd := (norm_fst_le ((F (g + v, Θ) - F (g, 0)) ⟨i, hi⟩)).trans hb
  have hs := (norm_snd_le ((F (g + v, Θ) - F (g, 0)) ⟨i, hi⟩)).trans hb
  dsimp only [F, Pi.sub_apply, Prod.mk_sub_mk] at hd hs
  rw [fcFiniteOperatorPath_zero, (fullFC_reference_step Q hQ hpos g i).2.1] at hd
  rw [fcFiniteOperatorPath_zero, (fullFC_reference_step Q hQ hpos g i).2.2] at hs
  exact ⟨hd, hs⟩

end
end krylov.Functions
