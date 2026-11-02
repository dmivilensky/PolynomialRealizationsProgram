import krylov.Stability.SpectralScale

/-!
Article: main_krylov, apB:lem:UAsteps, genuine scale-free FC induction step.
Use: extend the actual uniform next-step theorem to every positive lower
spectral endpoint with exactly the same horizon/conditioning-only constant.
Source: the real observed-search theorem with scaled actual directions,
true CG weighted projectors and the genuine finite secant accumulation.
-/

namespace krylov.Stability
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The genuine FC next-step error has the same uniform constant on every interval [mu,mu*kappa].
Use: The genuine FC next-step error has the same uniform constant on every interval [mu,mu*kappa].
Article: main_krylov, apB:lem:UAsteps.
Proof: Apply exact search to auxiliary directions divided by the positive lower endpoint. All real span, conjugacy, Gram and weighted CG premises come from the true trajectory; the scaled base norm is bounded by kappa and actual line displacements are unchanged. -/
theorem fullFC_uniform_next_step_scale (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (A : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) {μ κ C δ : ℝ} (hμ : 0<μ) (hκ : 1≤κ) (hC : 0≤C)
    (hspec : ∀ i, μ≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤μ*κ)
    (hinit : ‖cgCanonicalError base g 0‖≤1)
    (hpre : ∀ i≤k, CG.gradient (cgOperator base) g i≠0)
    (hsolve : ∀ i≤k, IsUnit (crossGram
      (windowImages (selectedWindow fullMemory (fcHistory fullMemory A g i)))
      (windowSteps (selectedWindow fullMemory (fcHistory fullMemory A g i)))).det)
    (hcurv : inner ℝ (fcDirection fullMemory A g k) (A k (fcDirection fullMemory A g k))≠0)
    (hA : ∀ i≤k, ‖canonicalOperator base (A i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤δ)
    (hδ : 0≤δ) (hδhalf : δ≤1/2) (hGram : (k : ℝ)*δ≤1/2)
    (hProj : 4*Real.sqrt k*δ≤1/2)
    (hstep : ∀ i<k, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (fcStep fullMemory A g i)-canonicalCGStep base g i‖≤C*δ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (fcStep fullMemory A g k)-canonicalCGStep base g k‖≤
      fcStepConstant k κ C*δ := by
  -- Every object below is read from the actual FC run or the genuine CG reference.
  let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
  let x : Fin k → EuclideanSpace ℝ (Fin n) := fun i => R (fcStep fullMemory A g i.val)
  let t : Fin k → EuclideanSpace ℝ (Fin n) := fun i => NormedSpace.normalize (x i)
  let q : Fin k → EuclideanSpace ℝ (Fin n) := fun i => canonicalCGUnitStep base g i.val
  let G := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ (fcGradient fullMemory A g k)
  let e := cgCanonicalError base g k
  let D := R (fcDirection fullMemory A g k)
  let D₀ := R (CG.direction (cgOperator base) g k)
  have hκ0 : 0≤κ := le_trans (by norm_num) hκ
  -- Genuine secant accumulation supplies the real current gradient estimate.
  have hgrad : ‖G-e‖≤(k : ℝ)*(2*C+1)*δ :=
    fullFC_canonical_gradient_bound base hb A g k hδ (by linarith) hC hinit
      (fun i hi => hA i hi.le) hstep
  have he : ‖e‖≤1 := (cgError_antitone base hb g (Nat.zero_le k)).trans hinit
  have hgn : ‖G‖≤1+(k : ℝ)*(2*C+1) := by
    have hg := (norm_le_norm_sub_add G e).trans (add_le_add hgrad he)
    have hm := mul_le_mul_of_nonneg_left (show δ≤1 by linarith)
      (show 0≤(k : ℝ)*(2*C+1) by positivity)
    nlinarith
  have hx (i : Fin k) : x i≠0 := fullFC_old_canonical_step_ne base hb A g i.val
    (hsolve (i.val+1) (by omega))
  have hG : ‖crossGram t t-1‖≤(k : ℝ)*δ :=
    fullFC_old_step_gram base hb A g k hδ hsolve (fun i hi => hA i hi.le)
  have hactive : k<referenceAtomCount base hb g := by
    by_contra hh
    exact hpre k le_rfl ((cg_stopping_iff base hb g k).mpr (by omega))
  have hcol (i : Fin k) : ‖e‖*
      ‖InnerProductSpace.rankOne ℝ (t i) (t i)-InnerProductSpace.rankOne ℝ (q i) (q i)‖≤
        4*Real.sqrt κ*(C*δ) := by
    simpa only [mul_div_cancel_left₀ _ hμ.ne'] using cg_weighted_rankOne base hb g hμ
      (by nlinarith : μ≤μ*κ) hspec
      (i.isLt.trans hactive) i.isLt.le (x i) (hx i) (C*δ) (hstep i.val i.isLt)
  let ε := (8*(k : ℝ)+4*(k : ℝ)*Real.sqrt κ*C)*δ
  -- Keep the true CG remaining-error weight on every actual old-column change.
  have hweight : ‖e‖*‖observedProjection t-observedProjection q‖≤ε := by
    have ht := observedProjection_weighted_change t q (hG.trans hGram) (norm_nonneg e) hcol
    rw [← observedProjection_eq_frameSum q (canonicalCG_old_gram base hb g k hactive.le)] at ht
    have hm := mul_le_mul he hG (norm_nonneg _) (by norm_num : (0 : ℝ)≤1)
    exact ht.trans (by dsimp only [ε]; nlinarith)
  -- Real inverse, span, conjugacy and search conditions now feed the uniform exact-search theorem.
  have hline := observed_lineStep_stability_rescale t
    (fun i => canonicalOperator base (A i.val) (t i)) (cgOperator base) (observedProjection q)
    (canonicalOperator base (A k)) G e D D₀ μ⁻¹ (inv_ne_zero hμ.ne')
    (fun i => NormedSpace.norm_normalize (hx i)) (hG.trans hGram)
    (fullFC_canonical_direction_span base hb A g k)
    (canonicalCG_direction_projection base hb g k (fun i hi => hpre i hi.le))
    (fullFC_canonical_direction_ne base hb A g k hcurv) (canonicalCG_direction_ne base hb g k hpre)
    (canonicalCG_scaled_direction_size base hb hμ (fun i => (hspec i).1) g k (fun i hi => hpre i hi.le))
    hδ hProj
    (fun i => fullFC_old_canonical_image_error base hb A g i.val (hsolve (i.val+1) (by omega)) (hA i.val i.isLt.le))
    (fun i => fullFC_old_canonical_image base hb A g k (hsolve k le_rfl) i)
    hweight (hA k le_rfl) hδhalf
  have hactual : lineLength G D (canonicalOperator base (A k) D) • D=R (fcStep fullMemory A g k) :=
    fullFC_canonical_line_step base hb A g k
  have href : lineLength e D₀ D₀ • D₀=canonicalCGStep base g k := canonicalCG_line_step base hb g k
  rw [hactual,href] at hline
  have hH : ‖μ⁻¹ • cgOperator base‖≤κ := scaled_base_norm base hb hμ hκ0 (fun i => (hspec i).2)
  apply hline.trans
  calc
    _ ≤ (2+8*κ)*((k : ℝ)*(2*C+1)*δ)+2*δ*1+4*κ*ε+
        64*Real.sqrt k*δ*κ*(1+(k : ℝ)*(2*C+1)) := by
      gcongr
    _ = _ := by dsimp only [fcStepConstant,ε]; ring

end
end krylov.Stability
