import krylov.Stability.ObservedProjection
import krylov.Stability.ReferenceWeights

/-!
Article: main_krylov, apB:lem:UAsteps and eq:weighted-flags, actual CG old-span weights.
Use: apply genuine rectangular projection estimates to actual normalized
perturbed steps and the real CG old span, uniformly near tiny reference steps.
Source: proved actual CG orthonormality and later-error/earlier-step ratios;
all rank-one weights come from genuine CG nonstagnation, not supplied data.
-/

namespace krylov.Stability
noncomputable section
open Matrix krylov.Methods krylov.Reference
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n p : ℕ}

/-- The true finite old CG unit-step family has actual identity Gram through its active atom count.
Use: its genuine old-span orthogonal projector equals its real rank-one frame sum.
Article: main_krylov, eq:weighted-flags and apB:lem:UAsteps.
Proof: actual nonstagnation gives the real CG orthonormality theorem;
its unit diagonal and true zero off-diagonal pairings identify the Gram.
-/
theorem canonicalCG_old_gram (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (p : ℕ) (hp : p≤referenceAtomCount base hb g) :
    crossGram (fun i : Fin p => canonicalCGUnitStep base g i.val)
      (fun i : Fin p => canonicalCGUnitStep base g i.val)=1 := by
  have hq := canonicalCGUnitStep_orthonormal base hb g p
    (fun i hi => cg_nonstagnation base hb g i (lt_of_lt_of_le hi hp))
  ext i j
  by_cases hij : i=j
  · subst j
    simp only [crossGram,Matrix.one_apply_eq,real_inner_self_eq_norm_sq,hq.1 i,one_pow]
  · simpa only [crossGram,Matrix.one_apply_ne hij] using hq.2 hij

/-- The actual old-span projection change has the uniform true-CG-error weighted bound with no smallest reference step.
Use: supplies the exact rectangular old-span estimate in the real FC stability induction, including empty old windows.
Article: main_krylov, apB:lem:UAsteps and eq:weighted-flags.
Proof: genuine normalized actual angles bound the real column Gram.
For every actual old column, the true CG nonstagnation ratio and its real
step error give the weighted rank-one bound. The proved actual projection
change inequality then sums these real weights; true CG orthonormality
identifies the reference projection itself.
-/
theorem cg_weighted_old_projection (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) {mu upper : ℝ} (hm : 0<mu) (hmu : mu≤upper)
    (hspec : ∀ i, mu≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤upper)
    (p k : ℕ) (hp : p≤referenceAtomCount base hb g) (hpk : p≤k)
    (x : Fin p → EuclideanSpace ℝ (Fin n)) (hx : ∀ i, x i≠0)
    {η ε : ℝ} (hη : 0≤η) (hsmall : (p : ℝ)*η≤1/2)
    (hstep : ∀ i, ‖x i-canonicalCGStep base g i.val‖≤ε)
    (hangle : ∀ i j, i≠j → |inner ℝ (NormedSpace.normalize (x i)) (NormedSpace.normalize (x j))|≤η) :
    ‖cgCanonicalError base g k‖*‖observedProjection (fun i => NormedSpace.normalize (x i))-
      observedProjection (fun i : Fin p => canonicalCGUnitStep base g i.val)‖≤
      8*‖cgCanonicalError base g k‖*(p : ℝ)*η+4*(p : ℝ)*Real.sqrt (upper/mu)*ε := by
  -- Every old normalized column retains its genuine later CG error weight before summation.
  let t : Fin p → EuclideanSpace ℝ (Fin n) := fun i => NormedSpace.normalize (x i)
  let q : Fin p → EuclideanSpace ℝ (Fin n) := fun i => canonicalCGUnitStep base g i.val
  have hG : ‖crossGram t t-1‖≤(p : ℝ)*η :=
    unitGram_deviation t (fun i => NormedSpace.norm_normalize (hx i)) hη hangle
  have hcol (i : Fin p) : ‖cgCanonicalError base g k‖*
      ‖InnerProductSpace.rankOne ℝ (t i) (t i)-InnerProductSpace.rankOne ℝ (q i) (q i)‖≤
        4*Real.sqrt (upper/mu)*ε :=
    cg_weighted_rankOne base hb g hm hmu hspec (lt_of_lt_of_le i.isLt hp)
      (le_trans i.isLt.le hpk) (x i) (hx i) ε (hstep i)
  have ht := observedProjection_weighted_change t q (hG.trans hsmall) (norm_nonneg _) hcol
  rw [← observedProjection_eq_frameSum q (canonicalCG_old_gram base hb g p hp)] at ht
  have hmul := mul_le_mul_of_nonneg_left hG
    (mul_nonneg (by norm_num : (0 : ℝ)≤8) (norm_nonneg (cgCanonicalError base g k)))
  exact ht.trans (by nlinarith)
end
end krylov.Stability
