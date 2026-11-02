import krylov.Stability.SpectralScale

/-!
Article: main_krylov, thm:UCq and apD:lem-step, observed-pair uniform search.
Use: Apply the scale-free true CG search comparison directly to arbitrary
actual recorded steps and correction-contaminated observed secants.
Source: proved weighted CG rank-one geometry, actual inverse-Gram projection
bounds and exact-search stability under positive spectral rescaling.
-/

namespace krylov.Stability
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The genuine next-line coefficient uses only the dimension, condition ratio and explicit prior error allowances.
Use: Construct uniform finite RFC induction constants before the real reference.
Article: main_krylov, thm:UCq and apD:lem-step.
-/
def observedCGStepConstant (k : ℕ) (κ C D a K : ℝ) : ℝ :=
  (2+8*κ)*D+2+4*κ*(8*a+4*(k : ℝ)*Real.sqrt κ*C)+64*Real.sqrt k*K*κ*(1+D)

/-- Actual observed-pair exact-search displacements satisfy the uniform CG comparison on every positive spectral scale.
Use: Close the ordinary-RFC step induction without an exact secant premise or a smallest reference energy.
Article: main_krylov, thm:UCq and apD:lem-step.
Proof: The genuine remaining CG error weights every old rank-one change. Real inverse-Gram conditioning controls the actual observed projection, and the true span and observed-image conjugacy feed the existing scale-free search theorem. Bound the resulting coefficient using the real accumulated-gradient and recorded-step allowances.
-/
theorem observedCG_line_step_bound (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (s y : Fin k → EuclideanSpace ℝ (Fin n))
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (G d : EuclideanSpace ℝ (Fin n)) {μ κ C D a K δ : ℝ}
    (hμ : 0<μ) (hκ : 1≤κ) (hC : 0≤C) (hD : 0≤D) (ha : 0≤a) (hK : 0≤K)
    (hspec : ∀ i, μ≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤μ*κ)
    (hinit : ‖cgCanonicalError base g 0‖≤1)
    (hpre : ∀ i≤k, CG.gradient (cgOperator base) g i≠0)
    (hs : ∀ i, s i≠0) (hd : d≠0)
    (hspan : d+cgOperator base G∈Submodule.span ℝ (Set.range (unitWindow s)))
    (hδ : 0≤δ) (hδone : δ≤1) (hhalf : δ≤1/2)
    (hGram : ‖crossGram (unitWindow s) (unitWindow s)-1‖≤a*δ)
    (hGramSmall : a*δ≤1/2) (hProj : 4*Real.sqrt k*(K*δ)≤1/2)
    (hy : ∀ i, ‖y i-s i‖≤K*δ*‖s i‖)
    (ho : ∀ i, inner ℝ (y i) d=0)
    (hA : ‖A-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤δ)
    (hgrad : ‖G-cgCanonicalError base g k‖≤D*δ)
    (hstep : ∀ i, ‖s i-canonicalCGStep base g i.val‖≤C*δ) :
    ‖lineLength G d (A d) • d-canonicalCGStep base g k‖≤observedCGStepConstant k κ C D a K*δ := by
  let t := unitWindow s
  let q : Fin k → EuclideanSpace ℝ (Fin n) := fun i => canonicalCGUnitStep base g i.val
  let e := cgCanonicalError base g k
  let D₀ := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (CG.direction (cgOperator base) g k)
  have hκ0 : 0≤κ := le_trans (by norm_num) hκ
  have he : ‖e‖≤1 := (cgError_antitone base hb g (Nat.zero_le k)).trans hinit
  have hgn : ‖G‖≤1+D := by
    have ht := (norm_le_norm_sub_add G e).trans (add_le_add hgrad he)
    nlinarith
  have hactive : k<referenceAtomCount base hb g := by
    by_contra hh
    exact hpre k le_rfl ((cg_stopping_iff base hb g k).mpr (by omega))
  have hcol (i : Fin k) : ‖e‖*
      ‖InnerProductSpace.rankOne ℝ (t i) (t i)-InnerProductSpace.rankOne ℝ (q i) (q i)‖≤
        4*Real.sqrt κ*(C*δ) := by
    simpa only [mul_div_cancel_left₀ _ hμ.ne',e,t,q,unitWindow,rescaleWindow,NormedSpace.normalize] using cg_weighted_rankOne base hb g hμ
      (by nlinarith : μ≤μ*κ) hspec (i.isLt.trans hactive) i.isLt.le (s i) (hs i) (C*δ) (hstep i)
  let ε := (8*a+4*(k : ℝ)*Real.sqrt κ*C)*δ
  have hweight : ‖e‖*‖observedProjection t-observedProjection q‖≤ε := by
    have ht := observedProjection_weighted_change t q (hGram.trans hGramSmall) (norm_nonneg e) hcol
    rw [← observedProjection_eq_frameSum q (canonicalCG_old_gram base hb g k hactive.le)] at ht
    have hm := mul_le_mul he hGram (norm_nonneg _) (by norm_num : (0 : ℝ)≤1)
    exact ht.trans (by dsimp only [ε]; nlinarith)
  have hline := observed_lineStep_stability_rescale t
    (rescaleWindow y (fun i => ‖s i‖⁻¹)) (cgOperator base) (observedProjection q) A G e d D₀
    μ⁻¹ (inv_ne_zero hμ.ne') (unitWindow_norm s hs) (hGram.trans hGramSmall) hspan
    (canonicalCG_direction_projection base hb g k (fun i hi => hpre i hi.le)) hd
    (canonicalCG_direction_ne base hb g k hpre)
    (canonicalCG_scaled_direction_size base hb hμ (fun i => (hspec i).1) g k (fun i hi => hpre i hi.le))
    (mul_nonneg hK hδ) hProj (unitWindow_pair_error s y hs hy)
    (fun i => by simp only [rescaleWindow,real_inner_smul_left,ho,mul_zero]) hweight hA hhalf
  rw [canonicalCG_line_step base hb g k] at hline
  have hH : ‖μ⁻¹ • cgOperator base‖≤κ := scaled_base_norm base hb hμ hκ0 (fun i => (hspec i).2)
  apply hline.trans
  calc
    _ ≤ (2+8*κ)*(D*δ)+2*δ*1+4*κ*ε+64*Real.sqrt k*(K*δ)*κ*(1+D) := by gcongr
    _ = _ := by dsimp only [observedCGStepConstant,ε]; ring

end
end krylov.Stability
