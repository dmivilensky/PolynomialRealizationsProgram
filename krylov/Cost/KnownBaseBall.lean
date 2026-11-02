import krylov.Cost.KnownBaseBallEmbedding
import krylov.OneGradient.KnownBaseOwnRisk
import krylov.Information.ReferenceErrorBall

/-!
Article: `main_krylov`, `thm:hier`, full known-base ball estimate.
For the literal fixed known-reference CG trials, choose one radius and
constants before the actual physical source, the prior radius r, and the
drift budget ω. Both radii vary independently. Exact source embedding,
true own-base budget transfer and the genuine preterminal CG error tube
turn the actual mixed output estimate into E≤C₁*r*ω+C₂*ω² in the source's
own metric and normalization, including r=0 and ω=0.
-/

namespace krylov.Cost
noncomputable section
open Matrix Filter Topology Asymptotics Finset krylov.Reference krylov.Methods
  krylov.OneGradient krylov.Information krylov.Correction krylov.Envelope krylov.Stability krylov.Secant
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The source's actual own-base penultimate-normalized physical error for
the literal τ_k=α_k(A) known-reference trial policy. -/
def fixedCGOwnError (directions : Bool)
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (g : EuclideanSpace ℝ (Fin (n+1))) (S : Scenario (n+1)) : ℝ :=
  ‖cgOperator (metricRoot S.base)⁻¹ (fixedScenarioOutput directions base g S)‖/
    ‖cgCanonicalError S.base g n‖

/-- Complete source known-base ball estimate, with independent prior and
drift radii and the true own-base metric and CG normalization. The S and
D methods both use the exact fixed known-reference lengths τ_k=α_k(A). -/
theorem fixedCG_known_base_ball_bound (directions : Bool)
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef) (hn : 0<n)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hc : referenceAtomCount base hb g=n+1) :
    ∃ δ C₁ C₂ : ℝ,0<δ ∧ 0<C₁ ∧ 0<C₂ ∧
      ∀ r ω : ℝ,0≤r → r<δ → 0≤ω → ω<δ → ∀ S : Scenario (n+1),
      S.Admissible n base r (fun _ ↦ ω) ω 0 →
        fixedCGOwnError directions base g S≤C₁*r*ω+C₂*ω^2 := by
  obtain ⟨δ₀,C,hδ₀,hC,hbound⟩ := fixedCG_known_metric_ball_bound directions base hb hn g hc
  obtain ⟨r₀,L,hr₀,_,hL,herror⟩ := referenceBaseChart_relative_error_ball base hb g hc
  let σ := ‖cgCanonicalError base g n‖
  have hσ : 0<σ := (last_reference_denominator base hb g n hc).1
  let R := cgOperator (metricRoot base)⁻¹
  let K := ‖R‖+1
  have hK : 0<K := by dsimp only [K]; positivity
  let δ := min (min (δ₀/4) (r₀/2)) (1/2)
  have hδ : 0<δ := lt_min (lt_min (by positivity) (half_pos hr₀)) (by norm_num)
  let C₁ := 4*K*C*(1+L)/σ
  let C₂ := 8*K*C*(1+L)/σ
  refine ⟨δ,C₁,C₂,hδ,by dsimp only [C₁]; positivity,by dsimp only [C₂]; positivity,?_⟩
  intro r ω hr hrδ hω hωδ S hS
  have hδ₀ : δ≤δ₀/4 := (min_le_left _ _).trans (min_le_left _ _)
  have hδr : δ≤r₀/2 := (min_le_left _ _).trans (min_le_right _ _)
  have hδhalf : δ≤1/2 := min_le_right _ _
  have hrhalf : r<1/2 := hrδ.trans_le hδhalf
  have hr1 : r<1 := by linarith
  have hrsmall : r<δ₀ := by linarith
  have hωsmall : 2*ω<δ₀ := by linarith
  have hbud := knownBase_admissible_known_budgets base hb S (fun _ ↦ ω)
    (fun _ _ ↦ hω) ω r 1 hω hr zero_le_one (by simpa only [mul_one] using hr1)
    (by simpa only [mul_one] using hS)
  have hquery : ∀ l<n,relativeBudget base (S.increment l)≤2*ω := by
    intro l hl
    have h := hbud.1 l hl
    simp only [mul_one] at h
    exact h.trans (by nlinarith)
  have houtput : relativeBudget base S.terminal≤2*ω := by
    have h := hbud.2
    simp only [mul_one] at h
    exact h.trans (by nlinarith)
  have hraw := hbound r (2*ω) hr (by positivity) hrsmall hωsmall S hS.1.1.isSymm
    (fun l hl ↦ (hS.2.2.1 l hl).1) hS.2.2.2.1 hS.2.1 hquery houtput
  let out := fixedScenarioOutput directions base g S
  have hcan : ‖R out‖≤K*(C*r*(2*ω)+C*(2*ω)^2) := by
    have hmap : ‖R out‖≤K*‖out‖ := (R.le_opNorm out).trans
      (mul_le_mul_of_nonneg_right (by dsimp only [K];linarith) (norm_nonneg out))
    exact hmap.trans (mul_le_mul_of_nonneg_left hraw hK.le)
  have hmetric := knownBase_prior_dual_norm_bound base S.base hb hS.1 r hr hr1 hS.2.1 out
  have hfactor : (1-r)⁻¹≤2 := by
    rw [← one_div]
    exact (div_le_iff₀ (by linarith : 0<1-r)).mpr (by linarith)
  have hown : ‖cgOperator (metricRoot S.base)⁻¹ out‖≤
      2*K*(C*r*(2*ω)+C*(2*ω)^2) := by
    apply hmetric.trans
    calc
      _ ≤ 2*‖R out‖ := mul_le_mul_of_nonneg_right hfactor (norm_nonneg _)
      _ ≤ 2*(K*(C*r*(2*ω)+C*(2*ω)^2)) := mul_le_mul_of_nonneg_left hcan (by norm_num)
      _ = _ := by ring
  have hzero : relativeBudget base (base-base)≤r₀ := by
    simpa only [sub_self,relativeBudget,relativeOperator,Matrix.mul_zero,Matrix.zero_mul,
      chebyshev1.opNorm,norm_zero] using hr₀.le
  have hprior : relativeBudget base (S.base-base)≤r₀ := hS.2.1.trans (by linarith)
  have he := herror S.base base hS.1 hb hprior hzero
  have hden : 0<‖cgCanonicalError S.base g n‖ := he.1
  have hprior1 : relativeBudget base (base-S.base)≤1 := by
    rw [show base-S.base=-(S.base-base) by abel,relative_budget_neg]
    exact hS.2.1.trans hr1.le
  have hσown : σ≤‖cgCanonicalError S.base g n‖*(1+L) :=
    he.2.2.trans (mul_le_mul_of_nonneg_left
      (by nlinarith [mul_le_mul_of_nonneg_left hprior1 hL]) hden.le)
  have hlow : σ/(1+L)≤‖cgCanonicalError S.base g n‖ :=
    (div_le_iff₀ (by positivity : 0<1+L)).mpr hσown
  have hB : 0≤2*K*(C*r*(2*ω)+C*(2*ω)^2) := by positivity
  change ‖cgOperator (metricRoot S.base)⁻¹ out‖/‖cgCanonicalError S.base g n‖≤_
  calc
    _ ≤ (2*K*(C*r*(2*ω)+C*(2*ω)^2))/‖cgCanonicalError S.base g n‖ :=
      div_le_div_of_nonneg_right hown hden.le
    _ ≤ (2*K*(C*r*(2*ω)+C*(2*ω)^2))/(σ/(1+L)) :=
      (div_le_div_iff₀ hden (div_pos hσ (by positivity))).mpr
        (mul_le_mul_of_nonneg_left hlow hB)
    _ = C₁*r*ω+C₂*ω^2 := by dsimp only [C₁,C₂]; field_simp; ring

end
end krylov.Cost
