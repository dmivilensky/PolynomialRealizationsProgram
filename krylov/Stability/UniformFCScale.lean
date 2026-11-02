import krylov.Stability.UniformFCStepScale
import krylov.Stability.UniformFCScaling

/-!
Article: Lemma B.8 [apB:lem:UAsteps] of krylov.tex.
Use: complete the genuine finite FC induction and its initial-error factor
on every positive spectral interval with constants depending only on dimension
and condition ratio, with no assumed invariance of the physical algorithm.
Source: the proved exact direction-rescaled search induction step and actual
initial-gradient homogeneity with genuine solve and curvature domain transfer.
-/

namespace krylov.Stability
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The actual finite FC step stability bound holds at every positive spectral scale with unchanged dimension/conditioning constants.
Use: The actual finite FC step stability bound holds at every positive spectral scale with unchanged dimension/conditioning constants.
Article: main_krylov, apB:lem:UAsteps.
Proof: Repeat the finite real trajectory induction using the proved scaled next-step theorem and the same genuine dimension-only radius. -/
theorem fullFC_uniform_steps_scale (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (A : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) {μ κ δ : ℝ} (hμ : 0<μ) (hκ : 1≤κ)
    (hspec : ∀ i, μ≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤μ*κ)
    (hinit : ‖cgCanonicalError base g 0‖≤1)
    (hpre : ∀ i<N, CG.gradient (cgOperator base) g i≠0)
    (hsolve : ∀ i<N, IsUnit (crossGram
      (windowImages (selectedWindow fullMemory (fcHistory fullMemory A g i)))
      (windowSteps (selectedWindow fullMemory (fcHistory fullMemory A g i)))).det)
    (hcurv : ∀ i<N, inner ℝ (fcDirection fullMemory A g i) (A i (fcDirection fullMemory A g i))≠0)
    (hA : ∀ i<N, ‖canonicalOperator base (A i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤δ)
    (hδ : 0≤δ) (hsmall : 8*((N : ℝ)+1)*δ≤1) :
    ∀ i<N, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (fcStep fullMemory A g i)-canonicalCGStep base g i‖≤
      fcUniformConstant κ N*δ := by
  -- Each induction hypothesis concerns the actual executed steps of the same real trajectory.
  have hκ0 : 0≤κ := le_trans (by norm_num) hκ
  have hprefix : ∀ k : ℕ, k≤N → ∀ i<k,
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (fcStep fullMemory A g i)-canonicalCGStep base g i‖≤
        fcUniformConstant κ k*δ := by
    intro k
    induction k with
    | zero => intro _ i hi; omega
    | succ k ih =>
      intro hk i hi
      have hkN : k<N := by omega
      have hprev := ih hkN.le
      obtain ⟨hδhalf,hGram,hProj⟩ := fc_uniform_radius_conditions N k hkN.le hδ hsmall
      -- All actual inverse, search, span and true-CG weights were discharged in the next-step theorem.
      have hnew := fullFC_uniform_next_step_scale base hb A g k hμ hκ (fcUniformConstant_nonneg hκ0 k)
        hspec hinit (fun j hj => hpre j (by omega)) (fun j hj => hsolve j (by omega))
        (hcurv k hkN) (fun j hj => hA j (by omega)) hδ hδhalf hGram hProj hprev
      by_cases he : i=k
      · subst i
        apply hnew.trans
        exact mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_left (fcUniformConstant_nonneg hκ0 k)) hδ
      · exact (hprev i (by omega)).trans (mul_le_mul_of_nonneg_right
          (fcUniformConstant_monotone hκ0 (Nat.le_succ k)) hδ)
  exact hprefix N le_rfl


/-- The actual finite uniform FC step error has its true initial-error factor at every positive spectral scale.
Use: The actual finite uniform FC step error has its true initial-error factor at every positive spectral scale.
Article: main_krylov, apB:lem:UAsteps.
Proof: Normalize the real initial gradient, transfer the actual solve/search domains and reference nonstagnation, and restore the genuine factor by actual FC/CG homogeneity. -/
theorem fullFC_uniform_steps_weighted_scale (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (A : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) {μ κ δ : ℝ} (hμ : 0<μ) (hκ : 1≤κ)
    (hspec : ∀ i, μ≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤μ*κ)
    (hpre : ∀ i<N, CG.gradient (cgOperator base) g i≠0)
    (hsolve : ∀ i<N, IsUnit (crossGram
      (windowImages (selectedWindow fullMemory (fcHistory fullMemory A g i)))
      (windowSteps (selectedWindow fullMemory (fcHistory fullMemory A g i)))).det)
    (hcurv : ∀ i<N, inner ℝ (fcDirection fullMemory A g i) (A i (fcDirection fullMemory A g i))≠0)
    (hA : ∀ i<N, ‖canonicalOperator base (A i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤δ)
    (hδ : 0≤δ) (hsmall : 8*((N : ℝ)+1)*δ≤1) :
    ∀ i<N, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (fcStep fullMemory A g i)-canonicalCGStep base g i‖≤
      fcUniformConstant κ N*δ*‖cgCanonicalError base g 0‖ := by
  -- The empty trajectory needs no fictitious nonzero initial-error normalization.
  by_cases hN : N=0
  · subst N
    intro i hi
    omega
  have hg : g≠0 := hpre 0 (Nat.pos_of_ne_zero hN)
  have he : 0 < ‖cgCanonicalError base g 0‖ := norm_pos_iff.mpr (cgCanonicalError_initial_ne_zero base hb g hg)
  let c := ‖cgCanonicalError base g 0‖⁻¹
  have hc : 0<c := inv_pos.mpr he
  have hscaled : ‖cgCanonicalError base (c • g) 0‖≤1 := by
    rw [cgCanonicalError_scalar base hb g c hc.ne' 0,norm_smul,Real.norm_eq_abs,abs_of_pos hc]
    dsimp only [c]
    rw [inv_mul_cancel₀ he.ne']
  -- Every domain below belongs to the actual normalized run and is discharged from the real original run.
  have hbound := fullFC_uniform_steps_scale base hb A (c • g) N hμ hκ hspec hscaled
    (fun i hi => by rw [cg_gradient_scalar base hb g c hc.ne' i]; exact smul_ne_zero hc.ne' (hpre i hi))
    (fun i hi => fullFC_solve_scalar A g c hc.ne' i (hsolve i hi))
    (fun i hi => fullFC_curvature_scalar A g c hc.ne' i (hcurv i hi)) hA hδ hsmall
  intro i hi
  have ht := hbound i hi
  have hs : Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (fcStep fullMemory A (c • g) i)-canonicalCGStep base (c • g) i=
      c • (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (fcStep fullMemory A g i)-canonicalCGStep base g i) := by
    rw [((fullFC_scalar A g c hc.ne' N).2 i hi).2,map_smul,canonicalCGStep_scalar base hb g c hc.ne' i,smul_sub]
  rw [hs,norm_smul,Real.norm_eq_abs,abs_of_pos hc] at ht
  calc
    _ = ‖cgCanonicalError base g 0‖*(c*‖Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (fcStep fullMemory A g i)-canonicalCGStep base g i‖) := by
      dsimp only [c]
      rw [← mul_assoc,mul_inv_cancel₀ he.ne',one_mul]
    _ ≤ ‖cgCanonicalError base g 0‖*(fcUniformConstant κ N*δ) := mul_le_mul_of_nonneg_left ht he.le
    _ = _ := by ring

end
end krylov.Stability
