import krylov.Stability.CanonicalResponseCoordinates
import krylov.Stability.UniformFCScaling
import krylov.Stability.WeightedCGFlags

/-!
Article: main_krylov, apB:lem:UAsteps, genuine weighted direction flags.
Use: control real executed FC oblique flags uniformly over arbitrarily small
reference energies, allowing the actual last line displacement to vanish.
Source: proved genuine finite FC stability, actual CG weighted rank-one
geometry, scalar-invariant normalized projectors and true direction Grams.
-/

namespace krylov.Stability
noncomputable section
open Matrix Finset krylov.Methods krylov.Reference krylov.Secant krylov.Variation krylov.LinearAlgebra
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The normalized real rank-one projector is invariant under every nonzero real scalar.
Use: The normalized real rank-one projector is invariant under every nonzero real scalar.
Article: main_krylov, apB:lem:UAsteps.
Proof: Positive normalization is unchanged; negative normalization negates both rank-one factors. -/
theorem normalize_rankOne_smul (c : ℝ) (hc : c≠0) (x : EuclideanSpace ℝ (Fin n)) :
    InnerProductSpace.rankOne ℝ (NormedSpace.normalize (c • x)) (NormedSpace.normalize (c • x))=
      InnerProductSpace.rankOne ℝ (NormedSpace.normalize x) (NormedSpace.normalize x) := by
  rcases lt_or_gt_of_ne hc with hn|hp
  · rw [NormedSpace.normalize_smul_of_neg hn]
    ext v
    simp only [InnerProductSpace.rankOne_apply,inner_neg_left,neg_smul,smul_neg,neg_neg]
  · rw [NormedSpace.normalize_smul_of_pos hp]

/-- Every actual FC direction and its step retained by the next real solve have the same normalized projector.
Use: Every actual FC direction and its step retained by the next real solve have the same normalized projector.
Article: main_krylov, apB:lem:UAsteps.
Proof: The true next solve forces the genuine step scalar nonzero; use actual linearity and normalized scalar invariance. -/
theorem fullFC_direction_rankOne (base : Matrix (Fin n) (Fin n) ℝ)
    (A : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (j : ℕ)
    (hnext : IsUnit (crossGram
      (windowImages (selectedWindow fullMemory (fcHistory fullMemory A g (j+1))))
      (windowSteps (selectedWindow fullMemory (fcHistory fullMemory A g (j+1))))).det) :
    let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
    InnerProductSpace.rankOne ℝ (NormedSpace.normalize (R (fcDirection fullMemory A g j)))
      (NormedSpace.normalize (R (fcDirection fullMemory A g j)))=
    InnerProductSpace.rankOne ℝ (NormedSpace.normalize (R (fcStep fullMemory A g j)))
      (NormedSpace.normalize (R (fcStep fullMemory A g j))) := by
  dsimp only
  have hα : lineLength (fcGradient fullMemory A g j) (fcDirection fullMemory A g j)
      (A j (fcDirection fullMemory A g j))≠0 := by
    intro hz
    exact fullFC_step_ne_of_next_solve A g j hnext (by rw [fcStep,hz,zero_smul])
  rw [fcStep,map_smul,normalize_rankOne_smul _ hα]

/-- The actual FC direction flags differ from genuine CG flags by the printed uniform weighted bound.
Use: The actual FC direction flags differ from genuine CG flags by the printed uniform weighted bound.
Article: main_krylov, apB:lem:UAsteps.
Proof: The true finite step induction bounds each old step. Every preceding retained displacement gives the same projector as its actual direction. Apply the true CG weighted rank-one estimate and exact inverse-Gram bound; the terminal reference error vanishes, so no final-step division is needed. -/
theorem fullFC_uniform_direction_flag (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) {κ : ℝ}
    (hκ : 1≤κ) (hspec : ∀ i, 1≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤κ)
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
  have he := fullFC_uniform_steps_weighted base hb (canonicalFCPath base E 1) g n hκ hspec
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
    have hw := cg_weighted_rankOne base hb g (by norm_num : (0 : ℝ)<1) hκ hspec
      (show j.val<referenceAtomCount base hb g by simpa only [hcount] using j.isLt)
      (show j.val≤l+1 by omega) _ hne _ (he j.val j.isLt)
    change ‖cgCanonicalError base g (l+1)‖*
      ‖vecMulVec (WithLp.ofLp (NormedSpace.normalize (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
          (fcDirection fullMemory (canonicalFCPath base E 1) g j.val))))
        (WithLp.ofLp (NormedSpace.normalize (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
          (fcDirection fullMemory (canonicalFCPath base E 1) g j.val))))-
        vecMulVec (WithLp.ofLp (canonicalCGUnitStep base g j.val)) (WithLp.ofLp (canonicalCGUnitStep base g j.val))‖≤_
    rw [rankOne_matrix_difference_norm,fullFC_direction_rankOne base _ g j.val (hsolve _ hjnext)]
    simpa only [div_one] using hw
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
end
end krylov.Stability
