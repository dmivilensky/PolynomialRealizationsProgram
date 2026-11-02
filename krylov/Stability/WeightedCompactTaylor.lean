import krylov.Stability.CompactTaylor
import Mathlib.Topology.Order.Compact

/-!
Article: main_krylov, lem:U(a), the initial-error factor and reference/perturbation split.
Use: obtain the printed compact Taylor estimate with a genuine positive
continuous error weight, and specialize it to perturbations that fix the reference.
Source: the proved compact Taylor tube and the extreme-value theorem on the actual reference compact.
-/

namespace krylov.Stability
noncomputable section
open Set
open scoped Topology
variable {Z F : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [ProperSpace Z]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The compact Taylor remainder admits any genuine positive continuous reference-error weight.
Use: absorb the source's actual nonzero initial energy norm into the compact constant.
Article: main_krylov, lem:U(a), C_K‖Θ‖^k‖e₀‖_A.
Proof: the genuine compact reference-error weight attains a strictly positive
minimum; divide the proved common Taylor constant by that minimum. An empty
reference compact is handled without selecting a fictitious minimizing point. -/
theorem compact_weighted_taylor (f : Z → F) (e : Z → ℝ) (r : ℕ) (U K : Set Z)
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K⊆U) (hf : ContDiffOn ℝ r f U)
    (he : ContinuousOn e K) (hepos : ∀ x∈K, 0<e x) :
    ∃ δ C : ℝ, 0<δ ∧ 0≤C ∧ ∀ x∈K, ∀ h : Z, ‖h‖≤δ →
      ∀ k : ℕ, 1≤k → k≤r → ‖f (x+h)-taylorPolynomial f k x h‖≤C*‖h‖^k*e x := by
  -- A compact minimum is used only after proving that the actual reference set is nonempty.
  by_cases hn : K.Nonempty
  · obtain ⟨δ,M,hδ,hM,hrem⟩ := compact_taylor_remainders f r U K hU hK hKU hf
    obtain ⟨x₀,hx₀,hmin⟩ := hK.exists_isMinOn hn he
    have hp := hepos x₀ hx₀
    refine ⟨δ,M/(e x₀),hδ,div_nonneg hM hp.le,?_⟩
    intro x hx h hh k hk hkr
    have hM' : M≤M/e x₀*e x := by
      calc
        M = M/e x₀*e x₀ := (div_mul_cancel₀ M hp.ne').symm
        _ ≤ _ := mul_le_mul_of_nonneg_left (hmin hx) (div_nonneg hM hp.le)
    exact (hrem x hx h hh k hk hkr).trans
      ((mul_le_mul_of_nonneg_right hM' (pow_nonneg (norm_nonneg _) k)).trans_eq (by ring))
  · refine ⟨1,0,zero_lt_one,le_refl 0,?_⟩
    intro x hx
    exact (hn ⟨x,hx⟩).elim

variable {R P : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R] [ProperSpace R]
variable [NormedAddCommGroup P] [NormedSpace ℝ P] [ProperSpace P]

omit [NormedAddCommGroup Z] [NormedSpace ℝ Z] [ProperSpace Z] in
/-- The compact weighted Taylor theorem applies uniformly to the true perturbation variables while fixing the reference parameters.
Use: this is the actual reference/primitive-perturbation geometry of the source's cycle maps.
Article: main_krylov, lem:U(a), ζ∈K and Θ near zero.
Proof: embed the actual compact reference set as K×{0}, apply the proved
weighted common-tube theorem there, and use the exact norm identity ‖(0,Θ)‖=‖Θ‖. -/
theorem compact_reference_taylor (f : R × P → F) (e : R → ℝ) (r : ℕ)
    (U : Set (R × P)) (K : Set R) (hU : IsOpen U) (hK : IsCompact K)
    (hKU : ∀ x∈K, (x,(0 : P))∈U) (hf : ContDiffOn ℝ r f U)
    (he : ContinuousOn e K) (hepos : ∀ x∈K, 0<e x) :
    ∃ δ C : ℝ, 0<δ ∧ 0≤C ∧ ∀ x∈K, ∀ θ : P, ‖θ‖≤δ → ∀ k : ℕ, 1≤k → k≤r →
      ‖f (x,θ)-taylorPolynomial f k (x,0) (0,θ)‖≤C*‖θ‖^k*e x := by
  -- The compact set contains only true unperturbed references, while its tube includes all nearby primitives.
  let K₀ : Set (R × P) := K×ˢ{0}
  have hK₀ : IsCompact K₀ := hK.prod isCompact_singleton
  have hsub : K₀⊆U := by
    rintro ⟨x,θ⟩ ⟨hx,hθ⟩
    rw [mem_singleton_iff] at hθ
    change θ=0 at hθ
    subst θ
    exact hKU x hx
  have he₀ : ContinuousOn (fun z : R × P => e z.1) K₀ :=
    he.comp continuous_fst.continuousOn (fun _ hz => hz.1)
  obtain ⟨δ,C,hδ,hC,hrem⟩ := compact_weighted_taylor f (fun z => e z.1) r U K₀ hU hK₀ hsub hf he₀
    (fun z hz => hepos z.1 hz.1)
  refine ⟨δ,C,hδ,hC,?_⟩
  intro x hx θ hθ k hk hkr
  have hn : ‖((0 : R),θ)‖=‖θ‖ := by simp only [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)]
  simpa only [Prod.mk_add_mk, add_zero, zero_add, hn] using
    hrem (x,0) ⟨hx,rfl⟩ (0,θ) (hn ▸ hθ) k hk hkr

end
end krylov.Stability
