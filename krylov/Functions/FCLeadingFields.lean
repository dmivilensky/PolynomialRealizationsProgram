import krylov.Functions.FCReferenceFields
import krylov.Reference.Stopping

/-!
Article: main_krylov, lem:cycle-transfer and thm:Htransfer, the actual FC first jet.
Use: obtain the leading operator response directly from the genuine executed
finite FC map. The initial-gradient first derivative vanishes because CG
solves every quadratic in the ambient dimension.
Source: standard finite-dimensional CG orthogonality and the proved compact
Taylor theorem on the actual analytic FC domain.
-/

namespace krylov.Functions
noncomputable section
open Set Metric krylov.Methods krylov.Reference krylov.Stability
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

omit [CompleteSpace E] in
/-- Positive quadratic CG terminates by the ambient dimension, with no spectral representation hypothesis.
Article: main_krylov, lem:cycle-transfer, the identically zero reference output.
Proof: otherwise one obtains dimension plus one nonzero mutually orthogonal
actual CG residuals, contradicting finite-dimensional linear independence. -/
theorem cg_gradient_finrank_zero (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v ≠ 0 → 0 < inner ℝ v (Q v))
    (g : E) : CG.gradient Q g (Module.finrank ℝ E) = 0 := by
  let N := Module.finrank ℝ E
  by_contra hn
  have hne (i : Fin (N + 1)) : CG.gradient Q g i.val ≠ 0 := by
    intro hz
    exact hn (CG.gradient_eq_zero_of_le Q g hz (by omega))
  have hli : LinearIndependent ℝ (fun i : Fin (N + 1) => CG.gradient Q g i.val) := by
    apply linearIndependent_of_ne_zero_of_inner_eq_zero
    · exact hne
    · intro i j hij
      have ho (a b : Fin (N + 1)) (hab : a.val < b.val) :
          inner ℝ (CG.gradient Q g a.val) (CG.gradient Q g b.val) = 0 :=
        (CG.invariant Q hQ hpos g b.val (fun k hk => hne ⟨k, by omega⟩)).old_gradient a.val hab
      rcases lt_or_gt_of_ne (show i.val ≠ j.val from fun h => hij (Fin.ext h)) with h | h
      · exact ho i j h
      · rw [real_inner_comm]
        exact ho j i h
  have hc := hli.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hc
  change N + 1 ≤ N at hc
  omega

/-- The actual finite terminal FC map in genuine initial-gradient and segment-operator coordinates.
Article: main_krylov, lem:cycle-transfer, finite operator response map. -/
def fcFiniteTerminal (Q : E →L[ℝ] E) (N : ℕ)
    (z : E × (Fin N → E →L[ℝ] E)) : E :=
  fcGradient fullMemory (fcFiniteOperatorPath Q N z.2) z.1 N

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- The real terminal FC gradient reads only the finite operator prefix that it executes.
Article: main_krylov, lem:cycle-transfer, exact finite input dictionary. -/
theorem fcGradient_congr_operator_prefix (A B : ℕ → E →L[ℝ] E) (g : E)
    (N : ℕ) (hAB : ∀ j < N, A j = B j) :
    fcGradient fullMemory A g N = fcGradient fullMemory B g N := by
  have hh := methodRun_congr_prefix (fcMethod fullMemory) A A B B g N hAB hAB
  exact congrArg History.gradient hh

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- The genuine terminal FC map is analytic at every actual nondegenerate quadratic reference.
Article: main_krylov, lem:U and thm:Htransfer. -/
theorem fcFiniteTerminal_analytic (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v ≠ 0 → 0 < inner ℝ v (Q v))
    (N : ℕ) (g : E) (hpre : ∀ i < N, CG.gradient Q g i ≠ 0) :
    AnalyticAt ℝ (fcFiniteTerminal Q N) (g, 0) :=
  (quadraticFC_prefix_analytic
    (fun z : E × (Fin N → E →L[ℝ] E) => fcFiniteOperatorPath Q N z.2)
    Prod.fst (g, 0) (fun i => fcFiniteOperatorPath_analytic Q N i (g, 0)) analyticAt_fst Q
    (fcFiniteOperatorPath_zero Q N) hQ hpos N hpre).1

omit [CompleteSpace E] in
/-- The actual full-dimensional quadratic FC terminal slice is identically zero for every initial gradient.
Article: main_krylov, lem:cycle-transfer, cancellation of initial-gradient drift. -/
theorem fcFiniteTerminal_reference_zero (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v ≠ 0 → 0 < inner ℝ v (Q v))
    (g : E) : fcFiniteTerminal Q (Module.finrank ℝ E) (g, 0) = 0 := by
  rw [fcFiniteTerminal, fcFiniteOperatorPath_zero,
    (fullFC_reference_step Q hQ hpos g (Module.finrank ℝ E)).1]
  exact cg_gradient_finrank_zero Q hQ hpos g

/-- The actual linear FC operator response, with the true derivative and no prescribed response coefficient.
Article: main_krylov, thm:Htransfer, the degree-one operator coefficient. -/
def fcLeadingOperator (Q : E →L[ℝ] E) (N : ℕ) (g : E)
    (Θ : Fin N → E →L[ℝ] E) : E :=
  fderiv ℝ (fcFiniteTerminal Q N) (g, 0) (0, Θ)

omit [CompleteSpace E] in
/-- The actual first terminal derivative kills every initial-gradient direction.
Article: main_krylov, lem:cycle-transfer, genuine reference-slice cancellation. -/
theorem fcFiniteTerminal_fderiv_initial_zero (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v ≠ 0 → 0 < inner ℝ v (Q v))
    (g : E) (hpre : ∀ i < Module.finrank ℝ E, CG.gradient Q g i ≠ 0) (v : E) :
    fderiv ℝ (fcFiniteTerminal Q (Module.finrank ℝ E)) (g, 0) (v, 0) = 0 := by
  have hz : (fun y : E => fcFiniteTerminal Q (Module.finrank ℝ E) (y, 0)) = fun _ => 0 :=
    funext (fcFiniteTerminal_reference_zero Q hQ hpos)
  have hd0 : HasFDerivAt (fun y : E => fcFiniteTerminal Q (Module.finrank ℝ E) (y, 0))
      (0 : E →L[ℝ] E) g := by
    rw [hz]
    exact hasFDerivAt_const (0 : E) g
  have hin : HasFDerivAt (fun y : E => (y, (0 : Fin (Module.finrank ℝ E) → E →L[ℝ] E)))
      (ContinuousLinearMap.inl ℝ E (Fin (Module.finrank ℝ E) → E →L[ℝ] E)) g :=
    (ContinuousLinearMap.inl ℝ E (Fin (Module.finrank ℝ E) → E →L[ℝ] E)).hasFDerivAt
  have hd1 := (fcFiniteTerminal_analytic Q hQ hpos _ g hpre).differentiableAt.hasFDerivAt.comp g hin
  have hd := hd1.unique hd0
  have he := congrArg (fun A : E →L[ℝ] E => A v) hd
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply, _root_.zero_apply] using he

/-- The real FC first jet has a compact-uniform quadratic remainder, including nonlinear initial-gradient drift.
Article: main_krylov, lem:cycle-transfer, the genuine degree-one operator response.
Proof: apply compact Taylor to the actual finite FC map; actual CG termination
kills its value and its entire initial-gradient derivative. The same compact
derivative tube uniformly bounds the remaining genuine response coefficient. -/
theorem compact_fc_leading_operator (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v ≠ 0 → 0 < inner ℝ v (Q v))
    (K : Set E) (hK : IsCompact K)
    (hpre : ∀ g ∈ K, ∀ i < Module.finrank ℝ E, CG.gradient Q g i ≠ 0) :
    ∃ δ C M : ℝ, 0 < δ ∧ 0 ≤ C ∧ 0 ≤ M ∧
      (∀ g ∈ K, ∀ Θ : Fin (Module.finrank ℝ E) → E →L[ℝ] E,
        ‖fcLeadingOperator Q (Module.finrank ℝ E) g Θ‖ ≤ M * ‖Θ‖) ∧
      ∀ g ∈ K, ∀ v : E, ∀ Θ : Fin (Module.finrank ℝ E) → E →L[ℝ] E,
        ‖(v, Θ)‖ ≤ δ →
        ‖fcFiniteTerminal Q (Module.finrank ℝ E) (g + v, Θ) -
          fcLeadingOperator Q (Module.finrank ℝ E) g Θ‖ ≤ C * ‖(v, Θ)‖ ^ 2 := by
  let N := Module.finrank ℝ E
  let F := fcFiniteTerminal Q N
  let U := {z | AnalyticAt ℝ F z}
  let K₀ : Set (E × (Fin N → E →L[ℝ] E)) := K ×ˢ {0}
  have hK₀ : IsCompact K₀ := hK.prod isCompact_singleton
  have hsub : K₀ ⊆ U := by
    rintro ⟨g, θ⟩ ⟨hg, hθ⟩
    rw [Set.mem_singleton_iff] at hθ
    change θ = 0 at hθ
    subst θ
    exact fcFiniteTerminal_analytic Q hQ hpos N g (hpre g hg)
  have hF : ContDiffOn ℝ 2 F U := fun _ hz => hz.contDiffAt.contDiffWithinAt
  obtain ⟨δ, C, hδ, hC, hbound⟩ := compact_taylor_remainders F 2 U K₀
    (isOpen_analyticAt ℝ F) hK₀ hsub hF
  obtain ⟨ρ, M, hρ, hM, _, hD⟩ := compact_derivative_tube F 2 U K₀
    (isOpen_analyticAt ℝ F) hK₀ hsub hF
  refine ⟨δ, C, M, hδ, hC, hM, ?_, ?_⟩
  · intro g hg Θ
    have hz : (g, (0 : Fin N → E →L[ℝ] E)) ∈ cthickening ρ K₀ :=
      mem_cthickening_of_dist_le (g, 0) (g, 0) ρ K₀ ⟨hg, rfl⟩ (by simpa using hρ.le)
    have hb := hD 1 (by decide) (g, 0) hz
    rw [norm_iteratedFDeriv_one] at hb
    have ha := (fderiv ℝ F (g, 0)).le_opNorm ((0 : E), Θ)
    simp only [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)] at ha
    exact ha.trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
  · intro g hg v Θ hΘ
    have hv := fcFiniteTerminal_fderiv_initial_zero Q hQ hpos g (hpre g hg) v
    have hlin : fderiv ℝ F (g, 0) (v, Θ) = fcLeadingOperator Q N g Θ := by
      rw [show (v, Θ) = (v, 0) + (0, Θ) by ext <;> simp, map_add, hv, zero_add]
      rfl
    have ht : taylorPolynomial F 2 (g, 0) (v, Θ) = fcLeadingOperator Q N g Θ := by
      simp only [taylorPolynomial, Finset.sum_range_succ, Finset.sum_range_zero,
        iteratedFDeriv_zero_apply, iteratedFDeriv_one_apply, Nat.factorial_zero, Nat.factorial_one,
        Nat.cast_one, inv_one, one_smul, zero_add, hlin,
        show F (g, 0) = 0 from fcFiniteTerminal_reference_zero Q hQ hpos g]
    have hb := hbound (g, 0) ⟨hg, rfl⟩ (v, Θ) hΘ 2 (by decide) le_rfl
    rw [ht] at hb
    simpa only [Prod.mk_add_mk, zero_add] using hb

end
end krylov.Functions
