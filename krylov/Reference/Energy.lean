import krylov.Reference.Stopping
import krylov.Reference.FullCycle
import krylov.Reference.PolynomialAction

/-!
Article: main_krylov, s2:eq:cg and lem:chris, the actual CG energy identities.
Use: derive the energy drop, suffix sum and terminal displacement from the
computed trajectory, including the solved and zero-gradient regimes.
Source: exact-search orthogonality and Pythagoras (Meurant06).
-/

namespace krylov.Reference
noncomputable section
open Matrix krylov.Secant
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace BigOperators
variable {n : ℕ}

/-- The actual canonical error of the computed reference iterate.
Use: the energy norm is the ordinary Euclidean norm of this vector.
Article: main_krylov, s2:eq:cg, ê_k=A^(−1/2)g_k. -/
def cgCanonicalError (base : Matrix (Fin n) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) : EuclideanSpace ℝ (Fin n) :=
  Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base)⁻¹
    (CG.gradient (cgOperator base) g k)

/-- The canonical error changes by the actual canonical CG step.
Use: telescoping identities concern the computed reference errors.
Article: main_krylov, s2:eq:cg.
Proof: use the already established genuine root-inverse update identity. -/
theorem cgCanonicalError_succ (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    cgCanonicalError base g (k+1)=cgCanonicalError base g k+canonicalCGStep base g k :=
  canonicalCG_gradient_step base hb g k

/-- The actual step is orthogonal to the actual post-search canonical error.
Use: proves the energy drop without requiring a fictitious nonzero step after termination.
Article: main_krylov, s2:eq:cg, Pythagorean energy identity.
Proof: a zero step is immediate; otherwise multiply the proved normalized exact-search pairing by its norm. -/
theorem canonicalCGStep_postsearch_orth (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    inner ℝ (canonicalCGStep base g k) (cgCanonicalError base g (k+1))=0 := by
  by_cases hs : canonicalCGStep base g k=0
  · rw [hs, inner_zero_left]
  · have hn : canonicalCGStep base g k=‖canonicalCGStep base g k‖ • canonicalCGUnitStep base g k :=
      (NormedSpace.norm_smul_normalize _).symm
    rw [hn, real_inner_smul_left]
    have ho : inner ℝ (canonicalCGUnitStep base g k) (cgCanonicalError base g (k+1))=0 :=
      canonicalCG_postsearch_orth base hb g k hs
    rw [ho, mul_zero]

/-- Each computed step energy is exactly the computed drop in squared energy error.
Use: energy drops are justified even at and after stopping.
Article: main_krylov, s2:eq:cg and lem:chris, c_k=‖ê_k‖²−‖ê_(k+1)‖².
Proof: the old error is the new error minus the actual step; exact-search orthogonality gives Pythagoras. -/
theorem cgEnergy_drop (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    cgEnergy base g k=‖cgCanonicalError base g k‖^2-‖cgCanonicalError base g (k+1)‖^2 := by
  have he : cgCanonicalError base g k=cgCanonicalError base g (k+1)-canonicalCGStep base g k := by
    rw [cgCanonicalError_succ base hb]
    abel
  have ho : inner ℝ (cgCanonicalError base g (k+1)) (canonicalCGStep base g k)=0 := by
    rw [real_inner_comm]
    exact canonicalCGStep_postsearch_orth base hb g k
  rw [cgEnergy_eq_norm_sq base hb, he, norm_sub_sq_real, ho]
  ring

/-- The actual step energy is the true positive line length times the squared residual norm.
Use: identifies the paper's c_k with the coefficients used by the executed CG recurrence.
Article: main_krylov, lem:chris, c_k=α_k‖g_k‖².
Proof: substitute the genuine search-pairing line formula and cancel its proved positive curvature. -/
theorem cgEnergy_eq_length_norm (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) {k : ℕ} (hk : k<referenceAtomCount base hb g) :
    cgEnergy base g k=CG.length (cgOperator base) g k*‖CG.gradient (cgOperator base) g k‖^2 := by
  -- Nonzero residuals and positive curvature are established before any cancellation.
  have hp := cgOperator_positive base hb
  have hi := CG.invariant (cgOperator base) hp.1 hp.2 g k
    (fun i hi => cg_nonstagnation base hb g i (hi.trans hk))
  obtain ⟨hd, _, hl⟩ := CG.invariant_line_pos (cgOperator base) hp.2 g k hi
    (cg_nonstagnation base hb g k hk)
  have hc := (hp.2 _ hd).ne'
  change inner ℝ (CG.length (cgOperator base) g k • CG.direction (cgOperator base) g k)
    (cgOperator base (CG.length (cgOperator base) g k • CG.direction (cgOperator base) g k))=_
  rw [map_smul, real_inner_smul_left, real_inner_smul_right, hl]
  field_simp

/-- The sum of actual canonical steps over any finite interval is the actual canonical displacement.
Use: terminal suffix vectors are tied to actual CG iterates.
Article: main_krylov, lem:chris, orthogonal suffix displacement.
Proof: telescope the already proved true canonical error recurrence. -/
theorem canonicalCGStep_sum (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) {l m : ℕ} (hlm : l≤m) :
    (∑ k∈Finset.Ico l m, canonicalCGStep base g k)=
      cgCanonicalError base g m-cgCanonicalError base g l := by
  have hs (k : ℕ) : canonicalCGStep base g k=
      cgCanonicalError base g (k+1)-cgCanonicalError base g k := by
    rw [cgCanonicalError_succ base hb]
    abel
  simp_rw [hs]
  exact Finset.sum_Ico_sub _ hlm

/-- The computed squared error is exactly the sum of its remaining actual energy drops.
Use: the Christoffel error profile and later variation coefficients use the genuine energy tail.
Article: main_krylov, lem:chris, ‖e_l‖_A²=Σ_(j≥l)c_j.
Proof: telescope all actual energy drops to the proved active-atom stopping time. -/
theorem cgEnergy_tail (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) {l : ℕ} (hl : l≤referenceAtomCount base hb g) :
    ‖cgCanonicalError base g l‖^2=
      ∑ k∈Finset.Ico l (referenceAtomCount base hb g), cgEnergy base g k := by
  have ht : cgCanonicalError base g (referenceAtomCount base hb g)=0 := by
    simp only [cgCanonicalError, cg_terminates base hb g, map_zero]
  simp_rw [cgEnergy_drop base hb]
  have he := Finset.sum_Ico_sub (fun k => -‖cgCanonicalError base g k‖^2) hl
  simp only [neg_sub_neg, ht, norm_zero, zero_pow (by omega : 2≠0), neg_zero, zero_sub, neg_neg] at he
  exact he.symm

/-- The remaining actual canonical displacement is the negative current error.
Use: the suffix vector has precisely the printed remaining energy norm.
Article: main_krylov, lem:chris, ‖v_l‖=‖e_(l+1)‖_A.
Proof: telescope the computed canonical steps to the proved zero terminal gradient. -/
theorem canonicalCGStep_tail (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) {l : ℕ} (hl : l≤referenceAtomCount base hb g) :
    (∑ k∈Finset.Ico l (referenceAtomCount base hb g), canonicalCGStep base g k)=
      -cgCanonicalError base g l := by
  rw [canonicalCGStep_sum base hb g hl]
  simp only [cgCanonicalError, cg_terminates base hb g, map_zero, zero_sub]

end
end krylov.Reference
