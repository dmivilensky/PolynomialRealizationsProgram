import krylov.Information.TwinBudgets
import krylov.Information.CorrectionCompletion
import krylov.Information.PhysicalReplay

/-!
Article: main_krylov, thm:centre, an admissible twin on the actual information fibre.
Use: assemble the joint H1--H4 construction, with genuine physical spectral
budgets and complete one-correction method histories.
Source: the proved flag-metric bounds, physical congruence invariance,
symmetric single-action completion and actual nonanticipating replay.
-/

namespace krylov.Information
noncomputable section
open Matrix Finset krylov.Secant krylov.Reference krylov.Methods krylov.LinearAlgebra
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
variable {p : ℕ}

/-- Actual finite-horizon scenario admissibility in one physical reference ball and budget profile.
Use: the twin theorem returns all original spectral constraints together.
Article: main_krylov, s4:C and thm:centre, Ξ^♯∈𝒮. -/
def Scenario.Admissible (S : Scenario p) (N : ℕ) (A : Matrix (Fin p) (Fin p) ℝ)
    (r : ℝ) (ω : ℕ → ℝ) (w τ : ℝ) : Prop :=
  S.base.PosDef ∧ relativeBudget A (S.base-A)≤r ∧
    (∀ l<N, (S.increment l).IsSymm ∧ relativeBudget S.base (S.increment l)≤ω l) ∧
    S.terminal.IsSymm ∧ relativeBudget S.base S.terminal≤w ∧
    ∀ k<N, (S.correction k).IsSymm ∧ relativeBudget S.base (S.correction k)≤τ

/-- Physical inverse form transport preserves symmetry exactly.
Use: transfer each actual finite-horizon coordinate constraint to its physical form.
Article: main_krylov, apD:centre, inverse direction-coordinate congruence.
Proof: the inverse transpose and inverse form an actual symmetric congruence. -/
theorem inverseForm_isSymm (D X : Matrix (Fin p) (Fin p) ℝ) (hX : X.IsSymm) :
    (inverseFormMap D X).IsSymm := by
  change (inverseCongruence D X).IsSymm
  simp only [inverseCongruence,Matrix.IsSymm,transpose_mul,
    transpose_nonsing_inv,transpose_transpose,hX.eq,Matrix.mul_assoc]

/-- The actual physical inverse form transport preserves positive definiteness.
Use: all completed physical correction budgets use the derived positive twin base.
Article: main_krylov, thm:centre(iii), physical positivity under nondegenerate directions.
Proof: the true inverse direction matrix has injective action, so its
congruence preserves every strictly positive nonzero quadratic form. -/
theorem inverseForm_posDef (D G : Matrix (Fin p) (Fin p) ℝ)
    (hD : IsUnit D.det) (hG : G.PosDef) : (inverseFormMap D G).PosDef := by
  -- Prove injectivity for the actual inverse coordinate map by cancelling its inverse.
  have hi : Function.Injective D⁻¹.mulVec := by
    intro u v huv
    have hh := congrArg (fun w => D*ᵥw) huv
    simpa only [mulVec_mulVec,mul_nonsing_inv _ hD,one_mulVec] using hh
  change (inverseCongruence D G).PosDef
  simpa only [inverseCongruence,conjTranspose_eq_transpose_of_trivial,
    transpose_nonsing_inv] using hG.conjTranspose_mul_mul_same (B := D⁻¹) hi

/-- Exact physical congruence preserves the actual relative spectral budget of every symmetric form.
Use: coordinate H1--H3 imply the source's original physical constraints with no extra loss.
Article: main_krylov, thm:centre(iii), coordinate-independent admissibility.
Proof: apply the established relative-budget congruence identity to the
actual nonsingular inverse direction matrix. -/
theorem inverseForm_budget (D G E : Matrix (Fin p) (Fin p) ℝ)
    (hD : IsUnit D.det) (hG : G.PosDef) (hE : E.IsSymm) :
    relativeBudget (inverseFormMap D G) (inverseFormMap D E)=relativeBudget G E := by
  change relativeBudget (inverseCongruence D G) (inverseCongruence D E)=_
  simpa only [inverseCongruence,transpose_nonsing_inv] using
    relativeBudget_congruence G E D⁻¹ hG hE (D.isUnit_nonsing_inv_det hD)

/-- Replace only the intermediate correction perturbations of an actual scenario.
Use: H4 completion keeps the reflected base, probes and terminal operator exactly fixed.
Article: main_krylov, thm:centre, admissible correction replacements. -/
def Scenario.withCorrections (S : Scenario p) (F : ℕ → Matrix (Fin p) (Fin p) ℝ) : Scenario p :=
  { S with correction := F }

/-- Correction replacement leaves every actual probe operator fixed.
Use: the completed twin still returns exactly the reflected physical probes.
Article: main_krylov, thm:centre, preservation of A_k under H4 completion.
Proof: actual probe sums contain only the unchanged base and increments. -/
theorem Scenario.withCorrections_probe (S : Scenario p)
    (F : ℕ → Matrix (Fin p) (Fin p) ℝ) (k : ℕ) :
    (S.withCorrections F).probe k=S.probe k := rfl

/-- Correction replacement leaves the actual terminal operator fixed.
Use: the opposite centred terminal error survives the admissible completion.
Article: main_krylov, thm:centre, fixed B_(n−1)^♯ after H4 replacement.
Proof: neither the terminal increment nor its accumulated probe is replaced. -/
theorem Scenario.withCorrections_lastOperator (S : Scenario p)
    (F : ℕ → Matrix (Fin p) (Fin p) ℝ) (N : ℕ) :
    (S.withCorrections F).lastOperator N=S.lastOperator N := rfl

/-- H1--H3 give every physical reflected constraint apart from intermediate corrections.
Use: the subsequent single-action construction completes precisely the remaining H4 obligation.
Article: main_krylov, thm:centre(iii), joint physical metric admissibility.
Proof: establish the actual positive reflected base and each individual
coordinate budget, then transport all forms through the same real inverse
direction congruence, including the fixed reference-radius difference. -/
theorem Scenario.physical_reflection_budgets (S : Scenario p) (N : ℕ)
    (A D : Matrix (Fin p) (Fin p) ℝ) (hA : A.PosDef) (hD : IsUnit D.det)
    (hG : S.base.PosDef) (he : directionDefect S.base<1)
    (hE : ∀ l<N, (S.increment l).IsSymm) (hT : S.terminal.IsSymm)
    (hv : S.twinDisplacement N<1) {r w : ℝ} (hr : 0≤r) (hw : 0≤w)
    (ω : ℕ → ℝ) (hω : ∀ l<N, 0≤ω l)
    (hH1 : ∀ l<N, relativeBudget S.base (S.increment l)≤
      ((1-S.twinDisplacement N)/flagDistortion S.base)*ω l)
    (hH2 : relativeBudget S.base S.terminal≤(1-S.twinDisplacement N)*w)
    (hH3 : relativeBudget A (S.base-A)+(1+r)*S.twinDisplacement N≤r) :
    let R := (S.reflect N).inPhysical D
    R.base.PosDef ∧ relativeBudget (inverseFormMap D A) (R.base-inverseFormMap D A)≤r ∧
      (∀ l<N, (R.increment l).IsSymm ∧ relativeBudget R.base (R.increment l)≤ω l) ∧
      R.terminal.IsSymm ∧ relativeBudget R.base R.terminal≤w := by
  -- The same constructed reflected base serves every transported profile constraint.
  have hp := (S.reflect_base_metric N hG he hE hv).2.2
  have hs := S.reflect_base_isSymm N hG.1.isSymm hE
  refine ⟨inverseForm_posDef D _ hD hp,?_,?_,?_,?_⟩
  · have heq : ((S.reflect N).inPhysical D).base-inverseFormMap D A=
        inverseFormMap D ((S.reflect N).base-A) := (map_sub _ _ _).symm
    have hsym : ((S.reflect N).base-A).IsSymm := by
      simp only [Matrix.IsSymm,transpose_sub,hs.eq,hA.1.isSymm.eq]
    have hn := inverseForm_budget D A ((S.reflect N).base-A) hD hA hsym
    exact (congrArg (relativeBudget (inverseFormMap D A)) heq).le.trans
      (hn.le.trans (S.reflect_reference_radius N A hA hG he hE hr hH3))
  · intro l hl
    have hsym := reflectedIncrement_isSymm l (S.increment l) (hE l hl)
    refine ⟨inverseForm_isSymm D _ hsym,?_⟩
    exact (inverseForm_budget D (S.reflect N).base (reflectedIncrement l (S.increment l))
      hD hp hsym).le.trans (S.reflect_increment_budget N hG he hE hv l hl (hω l hl) (hH1 l hl))
  · exact inverseForm_isSymm D _ (show (-S.terminal).IsSymm from by
      simp only [Matrix.IsSymm,transpose_neg,hT.eq])
  · have hsym : (-S.terminal).IsSymm := by simp only [Matrix.IsSymm,transpose_neg,hT.eq]
    exact (inverseForm_budget D (S.reflect N).base (-S.terminal) hD hp hsym).le.trans
      (S.reflect_terminal_budget N hG he hE hT hv hw hH2)

/-- Every prescribed sequence of actual one-query vectors satisfying H4 has admissible intermediate replacements.
Use: choose the complete finite family before replaying the method, with zero vectors allowed.
Article: main_krylov, thm:centre(iii), simultaneous H4 completion.
Proof: complete each actual physical single action in the proved symmetric
relative ball and choose these genuine finite-horizon witnesses; corrections
outside the observed horizon are set to zero. -/
theorem Scenario.complete_correction_actions (S : Scenario p) (N : ℕ)
    (hG : S.base.PosDef) (u : ℕ → EuclideanSpace ℝ (Fin p))
    {τ : ℝ} (hτ : 0≤τ)
    (hH4 : ∀ k<N, u k=0 ∨ ‖cgOperator (metricRoot S.base)⁻¹ (cgOperator (S.correction k) (u k))‖≤
      τ*‖cgOperator (metricRoot S.base) (u k)‖) :
    ∃ F : ℕ → Matrix (Fin p) (Fin p) ℝ, ∀ k<N,
      (F k).IsSymm ∧ relativeBudget S.base (F k)≤τ ∧
        cgOperator (F k) (u k)=cgOperator (S.correction k) (u k) := by
  -- All witnesses are real physical operators; no budget premise is imposed on the original full action.
  have hex (k : ℕ) (hk : k<N) :=
    exists_relative_action_replacement S.base (S.correction k) hG (u k) hτ (hH4 k hk)
  choose F hFs hFb hFu using hex
  classical
  refine ⟨fun k => if hk : k<N then F k hk else 0,?_⟩
  intro k hk
  simp only [dite_eq_left hk]
  exact ⟨hFs k hk,hFb k hk,hFu k hk⟩

end
end krylov.Information
