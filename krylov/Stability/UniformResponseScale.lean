import krylov.Stability.UniformFCScale
import krylov.Stability.UniformDirectionFlags
import krylov.Stability.UniformFCResponse

/-!
Article: main_krylov, thm:A and apB:lem:UAsteps, complete scale-free global FC response.
Use: give the genuine global quadratic remainder and weighted real direction
flags for every positive reference scale, with the same explicit dimension
and condition-ratio constants and the actual source initial-error factor.
Source: the completed arbitrary-scale genuine finite FC induction, true CG
weighted projectors and exact real oblique residual reconstruction.
-/

namespace krylov.Stability
noncomputable section
open Matrix Finset krylov.Methods krylov.Reference krylov.Secant krylov.Variation krylov.LinearAlgebra
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- Actual FC direction flags have the genuine uniform CG-error-weighted bound at every positive spectral scale.
Use: Actual FC direction flags have the genuine uniform CG-error-weighted bound at every positive spectral scale.
Article: main_krylov, thm:A and apB:lem:UAsteps.
Proof: Use actual scale-free step stability; true retained step projectors coincide with their direction projectors and the genuine terminal tail is zero. The actual CG ratio cancels the lower spectral endpoint. -/
theorem fullFC_uniform_direction_flag_scale (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) {μ κ : ℝ}
    (hμ : 0<μ) (hκ : 1≤κ) (hspec : ∀ i, μ≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤μ*κ)
    (hcount : referenceAtomCount base hb g=n)
    (hsolve : ∀ i<n, IsUnit (crossGram
      (windowImages (selectedWindow fullMemory (fcHistory fullMemory (canonicalFCPath base E 1) g i)))
      (windowSteps (selectedWindow fullMemory (fcHistory fullMemory (canonicalFCPath base E 1) g i)))).det)
    (hcurv : ∀ i<n, inner ℝ (fcDirection fullMemory (canonicalFCPath base E 1) g i)
      (canonicalFCPath base E 1 i (fcDirection fullMemory (canonicalFCPath base E 1) g i))≠0)
    (hsmall : 8*((n : ℝ)+1)*(∑ l∈range n, ‖E l‖)≤1) (l : ℕ) (hl : l<n) :
    let W := ∑ l∈range n, ‖E l‖
    let T := canonicalFCDirectionMatrix base (canonicalFCPath base E 1) g
    let Q := canonicalCGUnitMatrix base g
    ‖cgCanonicalError base g (l+1)‖*‖transportedFlag T l-transportedFlag Q l‖≤
      (n : ℝ)*(3+4*Real.sqrt κ*fcUniformConstant κ n)*W*‖cgCanonicalError base g 0‖ := by
  -- Keep each true later reference error paired with its own actual flag before summing columns.
  let W := ∑ l∈range n, ‖E l‖
  let T := canonicalFCDirectionMatrix base (canonicalFCPath base E 1) g
  let Q := canonicalCGUnitMatrix base g
  change ‖cgCanonicalError base g (l+1)‖*‖transportedFlag T l-transportedFlag Q l‖≤
    (n : ℝ)*(3+4*Real.sqrt κ*fcUniformConstant κ n)*W*‖cgCanonicalError base g 0‖
  have hW : 0≤W := sum_nonneg fun _ _ => norm_nonneg _
  have hC := fcUniformConstant_nonneg (le_trans (by norm_num) hκ) n
  have hG := canonicalFCPath_directionMatrix_gram base hb E g hsolve hcurv
  have hhalf := (fc_uniform_radius_conditions n n le_rfl hW hsmall).2.1
  have hsmallG : ‖Tᵀ*T-1‖≤1/2 := hG.trans hhalf
  have he := fullFC_uniform_steps_weighted_scale base hb (canonicalFCPath base E 1) g n hμ hκ hspec
    (fun i hi => cg_nonstagnation base hb g i (by simpa only [hcount] using hi))
    hsolve hcurv (fun i hi => canonicalFCPath_budget_bound base hb E n i hi.le) hW hsmall
  -- The terminal reference tail is exactly zero, even when the final actual step vanishes.
  by_cases hlast : l+1=n
  · have hz : cgCanonicalError base g (l+1)=0 := by
      unfold cgCanonicalError
      have hg : CG.gradient (cgOperator base) g (l+1)=0 := by
        simpa only [hcount,hlast] using cg_terminates base hb g
      rw [hg,map_zero]
    rw [hz,norm_zero,zero_mul]
    positivity
  have hcol : ∀ j∈Finset.univ.filter (fun j : Fin n => j.val≤l),
      ‖cgCanonicalError base g (l+1)‖*
      ‖vecMulVec (fun i => T i j) (fun i => T i j)-vecMulVec (fun i => Q i j) (fun i => Q i j)‖≤
        4*Real.sqrt κ*(fcUniformConstant κ n*W*‖cgCanonicalError base g 0‖) := by
    intro j hj
    have hjl := (mem_filter.mp hj).2
    have hjnext : j.val+1<n := by omega
    have hne := fullFC_old_canonical_step_ne base hb (canonicalFCPath base E 1) g j.val (hsolve _ hjnext)
    have hw := cg_weighted_rankOne base hb g hμ (by nlinarith : μ≤μ*κ) hspec
      (show j.val<referenceAtomCount base hb g by simpa only [hcount] using j.isLt)
      (show j.val≤l+1 by omega) _ hne _ (he j.val j.isLt)
    change ‖cgCanonicalError base g (l+1)‖*
      ‖vecMulVec (WithLp.ofLp (NormedSpace.normalize (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
          (fcDirection fullMemory (canonicalFCPath base E 1) g j.val))))
        (WithLp.ofLp (NormedSpace.normalize (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
          (fcDirection fullMemory (canonicalFCPath base E 1) g j.val))))-
        vecMulVec (WithLp.ofLp (canonicalCGUnitStep base g j.val)) (WithLp.ofLp (canonicalCGUnitStep base g j.val))‖≤_
    rw [rankOne_matrix_difference_norm,fullFC_direction_rankOne base _ g j.val (hsolve _ hjnext)]
    simpa only [mul_div_cancel_left₀ _ hμ.ne'] using hw
  have hbound := transportedFlag_weighted_bound T Q l hsmallG (norm_nonneg _)
    (by positivity : 0≤4*Real.sqrt κ*(fcUniformConstant κ n*W*‖cgCanonicalError base g 0‖)) hcol
  have hmon := cgError_antitone base hb g (show 0≤l+1 by omega)
  have hprod := mul_le_mul hmon hG (norm_nonneg _) (norm_nonneg _)
  change ‖cgCanonicalError base g (l+1)‖*‖transportedFlag T l-transportedFlag Q l‖≤_
  have hQ : transportedFlag Q l=Q*prefixProjection n l*Qᵀ := by
    unfold transportedFlag
    rw [show Q⁻¹=Qᵀ from canonicalCGUnitMatrix_inverse base hb g hcount]
  rw [hQ]
  exact hbound.trans (by nlinarith)

/-- The actual defined FC full-cycle residual has the printed global quadratic first-response remainder on every interval [mu,mu*kappa].
Use: The actual defined FC full-cycle residual has the printed global quadratic first-response remainder on every interval [mu,mu*kappa].
Article: main_krylov, thm:A and apB:lem:UAsteps.
Proof: The true scale-free finite step induction and weighted direction flags bound the exact real oblique response difference. All actual solve/search domains and genuine reference quantities are explicit; no smallest-energy bound or spectral normalization premise is needed. -/
theorem fullFC_uniform_quadratic_response_scale (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (hE : ∀ l, (E l).IsSymm)
    (g : EuclideanSpace ℝ (Fin n)) {μ κ : ℝ} (hμ : 0<μ) (hκ : 1≤κ)
    (hspec : ∀ i, μ≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤μ*κ)
    (hcount : referenceAtomCount base hb g=n)
    (hsolve : ∀ i<n, IsUnit (crossGram
      (windowImages (selectedWindow fullMemory (fcHistory fullMemory (canonicalFCPath base E 1) g i)))
      (windowSteps (selectedWindow fullMemory (fcHistory fullMemory (canonicalFCPath base E 1) g i)))).det)
    (hcurv : ∀ i<n, inner ℝ (fcDirection fullMemory (canonicalFCPath base E 1) g i)
      (canonicalFCPath base E 1 i (fcDirection fullMemory (canonicalFCPath base E 1) g i))≠0)
    (hsmall : 8*((n : ℝ)+1)*(∑ l∈range n, ‖E l‖)≤1) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
        (fcGradient fullMemory (canonicalFCPath base E 1) g n)-fullCycleResponse base g (range n) E‖≤
      fcResponseConstant n κ*(∑ l∈range n, ‖E l‖)^2*‖cgCanonicalError base g 0‖ := by
  -- All uniform estimates are for this actual run and its genuine reference, before response subtraction.
  let W := ∑ l∈range n, ‖E l‖
  let T := canonicalFCDirectionMatrix base (canonicalFCPath base E 1) g
  let Q := canonicalCGUnitMatrix base g
  let s := fun j => Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (fcStep fullMemory (canonicalFCPath base E 1) g j)
  let ε := fcUniformConstant κ n*W*‖cgCanonicalError base g 0‖
  let η := (n : ℝ)*(3+4*Real.sqrt κ*fcUniformConstant κ n)*W*‖cgCanonicalError base g 0‖
  have hW : 0≤W := sum_nonneg fun _ _ => norm_nonneg _
  have hC := fcUniformConstant_nonneg (le_trans (by norm_num) hκ) n
  have hhalf := (fc_uniform_radius_conditions n n le_rfl hW hsmall).2.1
  have hG : ‖Tᵀ*T-1‖≤1/2 :=
    (canonicalFCPath_directionMatrix_gram base hb E g hsolve hcurv).trans hhalf
  have he := fullFC_uniform_steps_weighted_scale base hb (canonicalFCPath base E 1) g n hμ hκ hspec
    (fun i hi => cg_nonstagnation base hb g i (by simpa only [hcount] using hi))
    hsolve hcurv (fun i hi => canonicalFCPath_budget_bound base hb E n i hi.le) hW hsmall
  have hf : ∀ l<n, ‖∑ j∈Ico (l+1) n, canonicalCGStep base g j‖*
      ‖transportedFlag T l-transportedFlag Q l‖≤η := by
    intro l hl
    have ht : remainingTail base g l=∑ j∈Ico (l+1) n, canonicalCGStep base g j := by
      simpa only [hcount] using remainingTail_eq_sum base hb g l (by simpa only [hcount] using hl)
    rw [← ht,remainingTail_norm]
    exact fullFC_uniform_direction_flag_scale base hb E g hμ hκ hspec hcount hsolve hcurv hsmall l hl
  -- Exact real residual identities reduce the remainder to the proved finite oblique response bound.
  rw [fullFC_exact_oblique_response base hb E hE g hsolve hcurv hhalf,← canonicalCG_obliqueResponse base hb g hcount E]
  have h := obliqueResponse_difference_bound T Q E s (canonicalCGStep base g)
    (show 0≤ε by dsimp only [ε];positivity) hG he hf
  apply h.trans_eq
  dsimp only [ε,η,W,fcResponseConstant]
  ring
end
end krylov.Stability
