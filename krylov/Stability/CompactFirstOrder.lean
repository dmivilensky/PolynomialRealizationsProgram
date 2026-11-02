import krylov.Stability.CompactZeroQuadratic

/-!
Article: main_krylov, thm:RFCS, uniform actual compact-reference first-order control.
Use: Bound actual field changes under simultaneous reference and source
perturbations by one common constant chosen before the compact family.
Source: the proved compact derivative/Taylor tube and its first Taylor polynomial.
-/

namespace krylov.Stability
noncomputable section
open Set Filter Asymptotics Topology Metric
variable {R P F : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R] [ProperSpace R]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [ProperSpace P]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Every actual jointly analytic map has one uniform first-order increment bound on a full tube around a compact reference family.
Use: Control real nonlinear RFC-S line-step and correction changes after the genuine queries have been localized.
Article: main_krylov, thm:RFCS, compact actual field perturbations.
Proof: Apply the proved compact first-order Taylor remainder on the genuine open analytic locus; its zeroth Taylor polynomial is exactly the original reference value.
-/
theorem compact_reference_full_first_order (f : R × P → F) (K : Set R) (hK : IsCompact K)
    (ha : ∀ x∈K, AnalyticAt ℝ f (x,0)) :
    ∃ δ C : ℝ, 0<δ ∧ 0<C ∧ ∀ x∈K, ∀ v : R, ∀ θ : P, ‖(v,θ)‖≤δ →
      ‖f (x+v,θ)-f (x,0)‖≤C*‖(v,θ)‖ := by
  let U := {z | AnalyticAt ℝ f z}
  let K₀ : Set (R × P) := K×ˢ{(0 : P)}
  have hK₀ : IsCompact K₀ := hK.prod isCompact_singleton
  have hsub : K₀⊆U := by
    rintro ⟨x,θ⟩ ⟨hx,hθ⟩
    rw [Set.mem_singleton_iff] at hθ
    change θ=(0 : P) at hθ
    subst θ
    exact ha x hx
  have hf : ContDiffOn ℝ 1 f U := fun _ hz => hz.contDiffAt.contDiffWithinAt
  obtain ⟨δ,C,hδ,hC,hbound⟩ := compact_taylor_remainders f 1 U K₀ (isOpen_analyticAt ℝ f) hK₀ hsub hf
  refine ⟨δ,C+1,hδ,by linarith,?_⟩
  intro x hx v θ hθ
  have hh := hbound (x,0) ⟨hx,rfl⟩ (v,θ) hθ 1 (by decide) le_rfl
  have hT : taylorPolynomial f 1 (x,0) (v,θ)=f (x,0) := by
    simp only [taylorPolynomial,Finset.sum_range_succ,Finset.sum_range_zero,
      iteratedFDeriv_zero_apply,Nat.factorial_zero,Nat.cast_one,inv_one,one_smul,zero_add]
  rw [hT] at hh
  simp only [Prod.mk_add_mk,zero_add,pow_one] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (by linarith : C≤C+1) (norm_nonneg _))

end
end krylov.Stability
