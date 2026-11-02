import krylov.Stability.UniformFC
import krylov.Methods.HomogeneousFC

/-!
Article: main_krylov, apB:lem:UAsteps, genuine global initial-error scaling.
Use: restore the actual initial-error factor in the uniform FC stability
bound with exactly the same dimension/conditioning constants and radius.
Source: proved true FC execution homogeneity, actual CG/FC quadratic equality
and genuine observed determinant and curvature scaling; no energy minimum is used.
-/

namespace krylov.Stability
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every actual defined full-memory FC coefficient solve stays genuinely defined when its real initial gradient is scaled by a nonzero scalar.
Use: transfer the source defined-cycle domain itself during the uniform error normalization.
Article: main_krylov, apB:lem:UAsteps and lem:U(c).
Proof: actual finite-age steps and observed images both scale by the real
execution theorem. Their genuine cross-Gram scales quadratically, so its
true determinant stays nonzero, including the empty solve. -/
theorem fullFC_solve_scalar (A : ℕ → E →L[ℝ] E) (g : E) (c : ℝ) (hc : c≠0) (k : ℕ)
    (hu : IsUnit (crossGram
      (windowImages (selectedWindow fullMemory (fcHistory fullMemory A g k)))
      (windowSteps (selectedWindow fullMemory (fcHistory fullMemory A g k)))).det) :
    IsUnit (crossGram
      (windowImages (selectedWindow fullMemory (fcHistory fullMemory A (c • g) k)))
      (windowSteps (selectedWindow fullMemory (fcHistory fullMemory A (c • g) k)))).det := by
  -- Scale the actual observed matrix itself, so its real inverse domain is proved to transfer.
  rw [fullFC_conjugacy_det_array] at hu ⊢
  have hS : (fun i : Fin k => fcStep fullMemory A (c • g) (k-1-i.val))=
      fun i => c • fcStep fullMemory A g (k-1-i.val) := by
    funext i
    exact ((fullFC_scalar A g c hc k).2 _ (by omega)).2
  have hY : (fun i : Fin k => fcSecant fullMemory A (c • g) (k-1-i.val))=
      fun i => c • fcSecant fullMemory A g (k-1-i.val) := by
    funext i
    simp only [fcSecant,((fullFC_scalar A g c hc k).2 (k-1-i.val) (by omega)).2,map_smul]
  rw [hS,hY,crossGram_scalar,Matrix.det_smul]
  exact isUnit_iff_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ (mul_ne_zero hc hc)) (isUnit_iff_ne_zero.mp hu))

/-- A true actual nonzero-curvature FC search stays genuinely defined under nonzero initial-gradient scaling.
Use: normalize actual trajectories without introducing a search-domain hypothesis on the normalized run.
Article: main_krylov, apB:lem:UAsteps and lem:U(c).
Proof: actual direction homogeneity and true operator linearity scale the genuine curvature by the nonzero scalar squared. -/
theorem fullFC_curvature_scalar (A : ℕ → E →L[ℝ] E) (g : E) (c : ℝ) (hc : c≠0) (k : ℕ)
    (hcurv : inner ℝ (fcDirection fullMemory A g k) (A k (fcDirection fullMemory A g k))≠0) :
    inner ℝ (fcDirection fullMemory A (c • g) k) (A k (fcDirection fullMemory A (c • g) k))≠0 := by
  rw [((fullFC_scalar A g c hc (k+1)).2 k (by omega)).1,map_smul,real_inner_smul_left,real_inner_smul_right]
  exact mul_ne_zero hc (mul_ne_zero hc hcurv)

variable {n : ℕ}

/-- The actual CG residual scales with its real initial gradient on every positive quadratic reference.
Use: genuine reference nonstagnation transfers under the same actual normalization as FC.
Article: main_krylov, apB:lem:UAsteps and lem:U(c).
Proof: actual FC homogeneity on the true static positive operator and the
proved real quadratic transcript equality identify both genuine CG runs. -/
theorem cg_gradient_scalar (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (c : ℝ) (hc : c≠0) (k : ℕ) :
    CG.gradient (cgOperator base) (c • g) k=c • CG.gradient (cgOperator base) g k := by
  have hp := cgOperator_positive base hb
  have hs := (fullFC_scalar (fun _ => cgOperator base) g c hc k).1
  rw [(fullFC_reference_step (cgOperator base) hp.1 hp.2 (c • g) k).1,
    (fullFC_reference_step (cgOperator base) hp.1 hp.2 g k).1] at hs
  exact hs

/-- The genuine canonical CG step scales with the true initial physical gradient.
Use: the same reference step enters the normalized and actual weighted uniform stability estimates.
Article: main_krylov, apB:lem:UAsteps.
Proof: real static FC step homogeneity transfers through actual quadratic
CG equality and the genuine linear positive metric root. -/
theorem canonicalCGStep_scalar (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (c : ℝ) (hc : c≠0) (k : ℕ) :
    canonicalCGStep base (c • g) k=c • canonicalCGStep base g k := by
  have hp := cgOperator_positive base hb
  have hs := ((fullFC_scalar (fun _ => cgOperator base) g c hc (k+1)).2 k (by omega)).2
  rw [(fullFC_reference_step (cgOperator base) hp.1 hp.2 (c • g) k).2.2,
    (fullFC_reference_step (cgOperator base) hp.1 hp.2 g k).2.2] at hs
  change Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (referenceStep (cgOperator base) (c • g) k)=_
  rw [hs,map_smul]
  rfl

/-- The actual canonical CG error scales with its true initial gradient.
Use: normalize the genuine initial error and restore its physical source factor.
Article: main_krylov, apB:lem:UAsteps.
Proof: actual CG gradient homogeneity transfers through the real inverse-root map. -/
theorem cgCanonicalError_scalar (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (c : ℝ) (hc : c≠0) (k : ℕ) :
    cgCanonicalError base (c • g) k=c • cgCanonicalError base g k := by
  rw [cgCanonicalError,cg_gradient_scalar base hb g c hc k,map_smul]
  rfl

/-- Every genuinely defined finite FC cycle has the uniform canonical step-error bound with its actual initial-error factor and unchanged dimension/conditioning constants.
Use: this is the source global homogeneous step estimate, including arbitrarily small individual CG energies and zero actual final steps; an empty cycle is included.
Article: main_krylov, apB:lem:UAsteps, ‖σ_k−σ_k⁰‖≤C(N,κ)δ‖e₀‖.
Proof: a nonempty actual active reference has strictly positive true initial
error. Scale the real initial gradient by its reciprocal, prove that both
actual solve/search domains and true reference nonstagnation transfer, and
apply the completed genuine finite normalized induction. Actual FC and CG
homogeneity restore the same real error factor; the constants and radius
remain unchanged throughout this true positive cone. -/
theorem fullFC_uniform_steps_weighted (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (A : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) {κ δ : ℝ} (hκ : 1≤κ)
    (hspec : ∀ i, 1≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤κ)
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
  have hbound := fullFC_uniform_steps base hb A (c • g) N hκ hspec hscaled
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
