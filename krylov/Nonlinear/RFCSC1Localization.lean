import krylov.Nonlinear.RFCSLocalization

/-!
Article: main_krylov, thm:RFCS, genuine localization from continuous derivatives.
Use: Obtain one actual shrinking query-domain bound from real local
continuous derivative data, before any Hessian Lipschitz expansion.
Source: the proved compact nonlinear query-localization theorem and genuine
small gradient-model Lipschitz error from continuous actual derivatives.
-/

namespace krylov.Nonlinear
noncomputable section
open Set Filter Topology Metric krylov.Methods krylov.Reference
open scoped NNReal
variable {k : ℕ}

/-- A genuine gradient with continuous derivative at its true positive quadratic model has uniformly localized RFC-S iterates and finite probes at distances proportional to the actual cycle scale, before every compact full-active reference and bounded nonzero probe family.
Use: Share genuine nonlinear trajectory localization between the actual source-profile, cubic-remainder and search/correction geometry arguments.
Article: main_krylov, thm:RFCS, actual local-function query-domain control.
Proof: Choose an actual local gradient-error Lipschitz constant sufficiently small for the proved compact nonlinear localization theorem. Continuity of the genuine derivative supplies its true physical neighborhood. The theorem then gives all real query bounds uniformly; enlarge one common constant to cover every actual point and finite probe.
-/
theorem compact_rfcs_C1_localization (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (K : Set (EuclideanSpace ℝ (Fin (k+1)))) (hK : IsCompact K)
    (hN : ∀ g∈K, k+1≤referenceAtomCount base hb g)
    (G : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)))
    (H : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (r B T : ℝ) (hr : 0<r) (hB : 0<B) (hT : 0≤T)
    (hG₀ : G 0=0) (hH₀ : H 0=cgOperator base) (hH : ContinuousAt H 0)
    (hG : ∀ x∈ball 0 r, HasFDerivAt G (H x) x) :
    ∃ ε₀ D : ℝ, 0<ε₀ ∧ 0<D ∧ ∀ ε : ℝ, 0<ε → ε<ε₀ →
      ∀ u : EuclideanSpace ℝ (Fin (k+1)), ‖u‖≤B → cgOperator base u∈K →
      ∀ h : ℕ → ℝ, (∀ i, h i≠0) → (∀ i<k+1, |h i|≤T) →
      (∀ i≤k+1, rfcSFunctionPoint fullMemory G (ε • u) h i∈ball 0 r ∧
        ‖rfcSFunctionPoint fullMemory G (ε • u) h i‖≤ε*D) ∧
      (∀ i<k+1, rfcSFunctionPoint fullMemory G (ε • u) h i+h i •
        windowDirection (selectedWindow fullMemory (rfcSFunctionRun fullMemory G (ε • u) h i))
          (rfcSFunctionRun fullMemory G (ε • u) h i).gradient∈ball 0 r ∧
        ‖rfcSFunctionPoint fullMemory G (ε • u) h i+h i •
          windowDirection (selectedWindow fullMemory (rfcSFunctionRun fullMemory G (ε • u) h i))
            (rfcSFunctionRun fullMemory G (ε • u) h i).gradient‖≤ε*D) := by
  obtain ⟨δ,M,hδ,hM,hloc⟩ := compact_rfcs_nonlinear_localization base hb K hK hN
  let q : ℝ := Real.sqrt (k+1 : ℕ)
  have hq : 0≤q := Real.sqrt_nonneg _
  let κ : ℝ≥0 := ⟨δ/((2*q+1)*(B+1)),by positivity⟩
  have hκ : 0<κ := by change 0<δ/((2*q+1)*(B+1)); positivity
  have hκeq : (κ : ℝ)*((2*q+1)*(B+1))=δ := by
    change δ/((2*q+1)*(B+1))*((2*q+1)*(B+1))=δ
    exact div_mul_cancel₀ δ (by positivity)
  have hκext : ((NNReal.sqrt (k+1 : ℕ)*κ : ℝ≥0) : ℝ)=q*(κ : ℝ) := by
    simp only [NNReal.coe_mul,Real.coe_sqrt,NNReal.coe_natCast,q]
  have hsmall : 2*((NNReal.sqrt (k+1 : ℕ)*κ : ℝ≥0) : ℝ)≤δ ∧
      ((NNReal.sqrt (k+1 : ℕ)*κ : ℝ≥0) : ℝ)*B≤δ := by
    rw [hκext]
    have hprod : 0≤q*(κ : ℝ)*B := by positivity
    constructor <;> nlinarith [κ.2]
  have hder : ∀ᶠ x in 𝓝 0, HasFDerivAt G (H x) x := by
    filter_upwards [ball_mem_nhds (0 : EuclideanSpace ℝ (Fin (k+1))) hr] with x hx
    exact hG x hx
  obtain ⟨ρ₀,hρ₀,hlocal⟩ := exists_gradient_error_lipschitz_ball G H (cgOperator base) hH₀ hH hder κ hκ
  let ρ := min r ρ₀
  have hρ : 0<ρ := lt_min hr hρ₀
  have hlocal' := hlocal.mono (ball_subset_ball (min_le_right r ρ₀))
  obtain ⟨ε₁,hε₁,hlocalized⟩ := hloc G hG₀ ρ B T hρ hB hT κ hlocal' hsmall.1 hsmall.2
  let D := B+((k+1 : ℕ)+T)*M+1
  have hD : 0<D := by dsimp only [D]; positivity
  refine ⟨ε₁,D,hε₁,hD,?_⟩
  intro ε hε he u hu hKu h hh hTbound
  have hqueries := hlocalized ε hε he u hu hKu h hh hTbound
  constructor
  · intro i hi
    refine ⟨ball_subset_ball (min_le_left _ _) (hqueries.1 i hi).1,?_⟩
    apply (hqueries.1 i hi).2.2.trans
    apply mul_le_mul_of_nonneg_left _ hε.le
    dsimp only [D]
    nlinarith
  · intro i hi
    refine ⟨ball_subset_ball (min_le_left _ _) (hqueries.2 i hi).1,?_⟩
    apply (hqueries.2 i hi).2.2.trans
    apply mul_le_mul_of_nonneg_left _ hε.le
    dsimp only [D]
    linarith

end
end krylov.Nonlinear
