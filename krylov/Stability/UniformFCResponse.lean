import krylov.Stability.UniformDirectionFlags
import krylov.Stability.ObliqueResponseBounds

/-!
Article: main_krylov, thm:A and apB:lem:UAsteps, genuine global FC quadratic response.
Use: bound the actual physical full-cycle FC residual minus its proved
true first response uniformly over all defined full-active normalized references.
Source: completed genuine finite step induction, weighted actual direction
flags and exact oblique residual reconstruction; no minimum CG energy is used.
-/

namespace krylov.Stability
noncomputable section
open Matrix Finset krylov.Methods krylov.Reference krylov.Secant krylov.Variation
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- An explicit horizon-and-conditioning-only constant for the true global quadratic FC remainder.
Use: An explicit horizon-and-conditioning-only constant for the true global quadratic FC remainder.
Article: main_krylov, thm:A.
Proof: It combines the actual finite tail error and weighted direction-flag constants. -/
def fcResponseConstant (n : ℕ) (κ : ℝ) : ℝ :=
  2*(n : ℝ)*fcUniformConstant κ n+(n : ℝ)*(3+4*Real.sqrt κ*fcUniformConstant κ n)

/-- The genuine global FC quadratic-response constant is nonnegative.
Use: The genuine global FC quadratic-response constant is nonnegative.
Article: main_krylov, thm:A.
Proof: Every actual finite step constant and square-root factor is nonnegative. -/
theorem fcResponseConstant_nonneg {κ : ℝ} (hκ : 0≤κ) : 0≤fcResponseConstant n κ := by
  unfold fcResponseConstant
  have := fcUniformConstant_nonneg hκ n
  positivity

/-- Every genuinely defined small-budget full FC cycle has the true global quadratic response remainder with constants depending only on dimension and conditioning.
Use: Every genuinely defined small-budget full FC cycle has the true global quadratic response remainder with constants depending only on dimension and conditioning.
Article: main_krylov, thm:A.
Proof: Derive actual canonical budgets and the real normalized direction Gram bound. The completed true finite step induction and weighted direction flags control the exact oblique reconstruction; identify its real reference value with the genuine first response. No individual energy is divided by and a zero actual last step is allowed. -/
theorem fullFC_uniform_quadratic_response (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (hE : ∀ l, (E l).IsSymm)
    (g : EuclideanSpace ℝ (Fin n)) {κ : ℝ} (hκ : 1≤κ)
    (hspec : ∀ i, 1≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤κ)
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
  have he := fullFC_uniform_steps_weighted base hb (canonicalFCPath base E 1) g n hκ hspec
    (fun i hi => cg_nonstagnation base hb g i (by simpa only [hcount] using hi))
    hsolve hcurv (fun i hi => canonicalFCPath_budget_bound base hb E n i hi.le) hW hsmall
  have hf : ∀ l<n, ‖∑ j∈Ico (l+1) n, canonicalCGStep base g j‖*
      ‖transportedFlag T l-transportedFlag Q l‖≤η := by
    intro l hl
    have ht : remainingTail base g l=∑ j∈Ico (l+1) n, canonicalCGStep base g j := by
      simpa only [hcount] using remainingTail_eq_sum base hb g l (by simpa only [hcount] using hl)
    rw [← ht,remainingTail_norm]
    exact fullFC_uniform_direction_flag base hb E g hκ hspec hcount hsolve hcurv hsmall l hl
  -- Exact real residual identities reduce the remainder to the proved finite oblique response bound.
  rw [fullFC_exact_oblique_response base hb E hE g hsolve hcurv hhalf,← canonicalCG_obliqueResponse base hb g hcount E]
  have h := obliqueResponse_difference_bound T Q E s (canonicalCGStep base g)
    (show 0≤ε by dsimp only [ε];positivity) hG he hf
  apply h.trans_eq
  dsimp only [ε,η,W,fcResponseConstant]
  ring
end
end krylov.Stability
