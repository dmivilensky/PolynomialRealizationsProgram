import krylov.Stability.CanonicalObservedFC
import krylov.Stability.UniformGradient
import krylov.Stability.UniformDirectionBasis

/-!
Article: main_krylov, apB:lem:UAsteps, actual uniform FC next-step induction.
Use: derive the real new canonical FC line-step error from true earlier
step errors, with every projection, Gram, search and CG weight discharged.
Source: genuine executed FC geometry, true compact-free CG energy ratios
and the proved real uniform observed-line search inequality.
-/

namespace krylov.Stability
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- An explicit dimension/conditioning induction coefficient for a real FC next-step estimate.
Use: depends only on the step index, spectral condition bound and previous uniform constant, never on individual reference energies.
Article: main_krylov, apB:lem:UAsteps, C(n,κ,C_a). -/
def fcStepConstant (k : ℕ) (κ C : ℝ) : ℝ :=
  (2+8*κ)*(k : ℝ)*(2*C+1)+2+
    4*κ*(8*(k : ℝ)+4*(k : ℝ)*Real.sqrt κ*C)+
      64*Real.sqrt k*κ*(1+(k : ℝ)*(2*C+1))

/-- The actual next canonical FC step has a uniform error bound with all real observed-data hypotheses discharged from the genuine executed history.
Use: this is the source finite stability induction step, including arbitrarily small true CG energies and a possible zero actual line displacement.
Article: main_krylov, apB:lem:UAsteps, μ=1 and ‖e₀‖≤1.
Proof: the actual secant accumulation bounds the genuine current gradient.
Real next solves make old steps nonzero; exact actual conjugacy bounds their
normalized Gram. Genuine CG weights control the actual old-span projection
change, and the true reference direction has the required error-size weight.
Apply the actual projected-search estimate, identify both real line steps,
and bound all remaining factors using only the stated spectral and prior constants. -/
theorem fullFC_uniform_next_step (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (A : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) {κ C δ : ℝ} (hκ : 1≤κ) (hC : 0≤C)
    (hspec : ∀ i, 1≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤κ)
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
    simpa only [div_one] using cg_weighted_rankOne base hb g (by norm_num : (0 : ℝ)<1) hκ hspec
      (i.isLt.trans hactive) i.isLt.le (x i) (hx i) (C*δ) (hstep i.val i.isLt)
  let ε := (8*(k : ℝ)+4*(k : ℝ)*Real.sqrt κ*C)*δ
  -- Keep the true CG remaining-error weight on every actual old-column change.
  have hweight : ‖e‖*‖observedProjection t-observedProjection q‖≤ε := by
    have ht := observedProjection_weighted_change t q (hG.trans hGram) (norm_nonneg e) hcol
    rw [← observedProjection_eq_frameSum q (canonicalCG_old_gram base hb g k hactive.le)] at ht
    have hm := mul_le_mul he hG (norm_nonneg _) (by norm_num : (0 : ℝ)≤1)
    exact ht.trans (by dsimp only [ε]; nlinarith)
  -- Real inverse, span, conjugacy and search conditions now feed the uniform exact-search theorem.
  have hline := observed_lineStep_stability t
    (fun i => canonicalOperator base (A i.val) (t i)) (cgOperator base) (observedProjection q)
    (canonicalOperator base (A k)) G e D D₀
    (fun i => NormedSpace.norm_normalize (hx i)) (hG.trans hGram)
    (fullFC_canonical_direction_span base hb A g k)
    (canonicalCG_direction_projection base hb g k (fun i hi => hpre i hi.le))
    (fullFC_canonical_direction_ne base hb A g k hcurv) (canonicalCG_direction_ne base hb g k hpre)
    (canonicalCG_direction_size base hb (fun i => (hspec i).1) g k (fun i hi => hpre i hi.le))
    hδ hProj
    (fun i => fullFC_old_canonical_image_error base hb A g i.val (hsolve (i.val+1) (by omega)) (hA i.val i.isLt.le))
    (fun i => fullFC_old_canonical_image base hb A g k (hsolve k le_rfl) i)
    hweight (hA k le_rfl) hδhalf
  have hactual : lineLength G D (canonicalOperator base (A k) D) • D=R (fcStep fullMemory A g k) :=
    fullFC_canonical_line_step base hb A g k
  have href : lineLength e D₀ D₀ • D₀=canonicalCGStep base g k := canonicalCG_line_step base hb g k
  rw [hactual,href] at hline
  have hH : ‖cgOperator base‖≤κ := cgOperator_norm_le base hb hκ0 (fun i => (hspec i).2)
  apply hline.trans
  calc
    _ ≤ (2+8*κ)*((k : ℝ)*(2*C+1)*δ)+2*δ*1+4*κ*ε+
        64*Real.sqrt k*δ*κ*(1+(k : ℝ)*(2*C+1)) := by
      gcongr
    _ = _ := by dsimp only [fcStepConstant,ε]; ring

/-- Every genuine FC next-step induction coefficient is nonnegative for nonnegative conditioning and preceding constants.
Use: build the finite dimension-only uniform stability constants monotonically.
Article: main_krylov, apB:lem:UAsteps.
Proof: every term in the explicit real coefficient is nonnegative. -/
theorem fcStepConstant_nonneg (k : ℕ) {κ C : ℝ} (hκ : 0≤κ) (hC : 0≤C) :
    0≤fcStepConstant k κ C := by
  unfold fcStepConstant
  positivity

end
end krylov.Stability
