import krylov.XR.FlagProjector
import krylov.XR.RelativeCorrection

/-!
Article: main_krylov, prop:status, sharp retention/refutation thresholds.
Use: solve the actual metric-transfer estimates with their printed
constants, then identify the complete relative minimax correction.
Source: the proved Hermitian criterion and reciprocal-gap metric transfer.
-/

/-!
Article: krylov, Proposition F.4 [prop:status].

Actual physical flag bounds imply the exact general/conjugate retention and refutation
thresholds, together with the hidden-error radius and minimax consequence.
The budget bounds entering VariationThreshold are derived in FlagVariation/PhysicalVariation;
their availability is not an extra article assumption.
-/
namespace krylov.XR
noncomputable section
open Matrix krylov.Secant krylov.Nonlinear
open scoped Matrix.Norms.L2Operator
variable {p : ℕ}

/-- The printed general-window budget threshold forces the actual
Hermitian test to pass and the actual model error below theta/2.
Article: main_krylov, prop:status. -/
theorem variation_budget_retention (G M : Matrix (Fin p) (Fin p) ℝ) (hG : G.PosDef)
    (θ κ W : ℝ) (hθ : 0<θ) (hκ : 1≤κ)
    (hmodel : relativeBudget G (G-latest M)≤κ^2*W)
    (hdefect : relativeBudget G (defect M)≤2*κ^2*W)
    (hsmall : W<θ/((2+θ)*κ^2)) :
    windowUnrefuted θ M ∧ relativeBudget (latest M) (G-latest M)<θ/2 := by
  have hκpos : 0<κ := by linarith
  have hden : 0<(2+θ)*κ^2 := by positivity
  have hb := (lt_div_iff₀ hden).mp hsmall
  have ha : κ^2*W<1 := by nlinarith
  have hzsym : (G-latest M).IsSymm := hG.isHermitian.isSymm.sub (latest_isSymm M)
  have hm := relativeBudget_model_transfer G (latest M) (G-latest M) hG (latest_isSymm M)
    (Or.inl hzsym) (κ^2*W) (κ^2*W) ha hmodel hmodel
  have hd := relativeBudget_model_transfer G (latest M) (defect M) hG (latest_isSymm M)
    (Or.inr (defect_transpose M)) (κ^2*W) (2*κ^2*W) ha hmodel hdefect
  have hr : (κ^2*W)/(1-κ^2*W)<θ/2 := by
    apply (div_lt_div_iff₀ (sub_pos.mpr ha) (by norm_num : (0:ℝ)<2)).mpr
    nlinarith
  have hδ : (2*κ^2*W)/(1-κ^2*W)<θ := by
    apply (div_lt_iff₀ (sub_pos.mpr ha)).mpr
    nlinarith
  exact ⟨(windowUnrefuted_iff θ hθ M).mpr ⟨hm.1,hd.2.trans_lt hδ⟩,hm.2.trans_lt hr⟩

/-- Refutation certifies exactly the source's genuine variation lower
bound, by contraposition of the proved observed test. Article: prop:status. -/
theorem variation_budget_refutation (G M : Matrix (Fin p) (Fin p) ℝ) (hG : G.PosDef)
    (θ κ W : ℝ) (hθ : 0<θ) (hκ : 1≤κ)
    (hmodel : relativeBudget G (G-latest M)≤κ^2*W)
    (hdefect : relativeBudget G (defect M)≤2*κ^2*W)
    (hrefute : ¬windowUnrefuted θ M) : θ/((2+θ)*κ^2)≤W := by
  by_contra! h
  exact hrefute (variation_budget_retention G M hG θ κ W hθ hκ hmodel hdefect h).1

/-- For genuinely conjugate flags the sharp constant-one commutator
bound improves the retention threshold to theta/(1+theta).
Article: main_krylov, prop:status. -/
theorem conjugate_budget_retention (G M : Matrix (Fin p) (Fin p) ℝ) (hG : G.PosDef)
    (θ W : ℝ) (hθ : 0<θ)
    (hmodel : relativeBudget G (G-latest M)≤W)
    (hdefect : relativeBudget G (defect M)≤W)
    (hsmall : W<θ/(1+θ)) :
    windowUnrefuted θ M ∧ relativeBudget (latest M) (G-latest M)<θ := by
  have hb := (lt_div_iff₀ (by linarith : 0<1+θ)).mp hsmall
  have ha : W<1 := by nlinarith
  have hzsym : (G-latest M).IsSymm := hG.isHermitian.isSymm.sub (latest_isSymm M)
  have hm := relativeBudget_model_transfer G (latest M) (G-latest M) hG (latest_isSymm M)
    (Or.inl hzsym) W W ha hmodel hmodel
  have hd := relativeBudget_model_transfer G (latest M) (defect M) hG (latest_isSymm M)
    (Or.inr (defect_transpose M)) W W ha hmodel hdefect
  have hr : W/(1-W)<θ := (div_lt_iff₀ (sub_pos.mpr ha)).mpr (by nlinarith)
  exact ⟨(windowUnrefuted_iff θ hθ M).mpr ⟨hm.1,hd.2.trans_lt hr⟩,hm.2.trans_lt hr⟩

/-- The sharp conjugate-window variation certificate follows from the
actual failure of the original Hermitian test. Article: prop:status. -/
theorem conjugate_budget_refutation (G M : Matrix (Fin p) (Fin p) ℝ) (hG : G.PosDef)
    (θ W : ℝ) (hθ : 0<θ)
    (hmodel : relativeBudget G (G-latest M)≤W)
    (hdefect : relativeBudget G (defect M)≤W)
    (hrefute : ¬windowUnrefuted θ M) : θ/(1+θ)≤W := by
  by_contra! h
  exact hrefute (conjugate_budget_retention G M hG θ W hθ hmodel hdefect h).1

/-- A certified retained window with model error below theta<=1 has the
full inverse-model correction as its genuine unique robust minimizer.
Article: main_krylov, prop:status, minimax clause. -/
theorem retained_full_correction_minimax (G M : Matrix (Fin p) (Fin p) ℝ)
    (θ : ℝ) (hθ : θ≤1) (hM : windowUnrefuted θ M) (hθpos : 0<θ)
    (herror : relativeBudget (latest M) (G-latest M)<θ)
    (r w : EuclideanSpace ℝ (Fin p)) :
    let hp := ((windowUnrefuted_iff θ hθpos M).mp hM).1
    let Ω := relativeBudget (latest M) (G-latest M)
    relativeCorrectionObjective (latest M) hp r Ω w=Ω*‖(metricCoordinates (latest M) hp).symm r‖ ↔
      w=relativeNewtonCorrection (latest M) hp r := by
  dsimp only
  exact relativeCorrection_small_iff _ _ r w _ (norm_nonneg _) (herror.trans_le hθ)

end
end krylov.XR
