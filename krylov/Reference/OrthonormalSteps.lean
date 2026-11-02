import krylov.Reference.CanonicalGradient
import krylov.Reference.CGGeometry

/-!
Article: main_krylov, s2:eq:cg and lem:terminal-fibre, derived actual canonical CG frame.
Use: construct the actual orthonormal step family from the genuine recurrence
and actual finite nonstagnation; no frame is assumed in the terminal theorem wrapper.
Source: the proved simultaneous CG invariants and genuine positive-root metric pairing.
-/

namespace krylov.Reference
noncomputable section
open Matrix krylov.Secant
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace
variable {n : ℕ}

/-- Actual nonstagnating CG generates a nonzero actual canonical step.
Use: justify its actual normalization before any reference frame is formed.
Article: main_krylov, s2:eq:cg, positive reference energies.
Proof: the proved true CG search has a positive line and nonzero direction;
the genuine invertible metric root cannot annihilate their actual nonzero step. -/
theorem canonicalCGStep_ne_zero (base : Matrix (Fin n) (Fin n) ℝ) (hbase : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (hg : ∀ i≤k, CG.gradient (cgOperator base) g i≠0) : canonicalCGStep base g k≠0 := by
  have hi := CG.invariant (cgOperator base) (cgOperator_positive base hbase).1
    (cgOperator_positive base hbase).2 g k (fun i h => hg i h.le)
  obtain ⟨hd, hl, _⟩ := CG.invariant_line_pos (cgOperator base) (cgOperator_positive base hbase).2 g k hi (hg k le_rfl)
  have hp : cgStep base g k≠0 := smul_ne_zero hl.ne' hd
  intro hz
  -- Apply the true inverse root to the actual zero image and cancel the two genuine factors.
  have he := congrArg (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base)⁻¹) hz
  change Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base)⁻¹
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base) (cgStep base g k))=_ at he
  apply hp
  simpa only [← mul_apply_eq_comp, ← map_mul, nonsing_inv_mul _ (metricRoot_det_unit base hbase),
    map_one, one_apply_eq_self, map_zero] using he

/-- Genuine CG conjugacy gives actual orthogonality of the actual positive-root reference steps.
Use: the reference frame is a consequence of the real algorithm, not an input data field.
Article: main_krylov, s2:eq:cg, orthogonal canonical steps.
Proof: true primal/dual metric pairing turns the two canonical steps into their
actual physical A-pairing; the executed step scalars multiply the proved true direction conjugacy. -/
theorem canonicalCGStep_orth (base : Matrix (Fin n) (Fin n) ℝ) (hbase : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (i j : ℕ) (hij : i<j)
    (hg : ∀ k<j, CG.gradient (cgOperator base) g k≠0) :
    inner ℝ (canonicalCGStep base g i) (canonicalCGStep base g j)=0 := by
  have hi := CG.invariant (cgOperator base) (cgOperator_positive base hbase).1
    (cgOperator_positive base hbase).2 g j hg
  have hp := canonical_search_pairing base hbase (cgStep base g i) (cgOperator base (cgStep base g j))
  rw [canonical_reference_action base hbase] at hp
  simp only [canonicalCGStep]
  rw [← hp]
  simp only [cgStep, map_smul, real_inner_smul_left, real_inner_smul_right,
    hi.conjugate i j hij le_rfl, mul_zero]

/-- The true nonstagnating finite CG run generates its own actual orthonormal canonical step frame.
Use: discharges the frame hypothesis of the full terminal data-fibre theorem from the real recurrence.
Article: main_krylov, s2:eq:cg and lem:terminal-fibre, actual ŝ_i.
Proof: every actual step is nonzero by the proved positive-line invariant;
true conjugacy makes distinct actual step pairings zero, and genuine norm normalization makes every diagonal one. -/
theorem canonicalCGUnitStep_orthonormal (base : Matrix (Fin n) (Fin n) ℝ) (hbase : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (M : ℕ)
    (hg : ∀ k<M, CG.gradient (cgOperator base) g k≠0) :
    Orthonormal ℝ (fun i : Fin M => canonicalCGUnitStep base g i.val) := by
  apply orthonormal_iff_ite.mpr
  intro i j
  split_ifs with he
  · subst j
    have hs := canonicalCGStep_ne_zero base hbase g i.val (fun k hk => hg k (hk.trans_lt i.isLt))
    simp only [real_inner_self_eq_norm_sq, canonicalCGUnitStep, NormedSpace.norm_normalize hs, one_pow]
  · have hz : inner ℝ (canonicalCGStep base g i.val) (canonicalCGStep base g j.val)=0 := by
      rcases lt_or_gt_of_ne (show i.val≠j.val from fun h => he (Fin.ext h)) with h | h
      · exact canonicalCGStep_orth base hbase g i.val j.val h (fun k hk => hg k (hk.trans j.isLt))
      · rw [real_inner_comm]
        exact canonicalCGStep_orth base hbase g j.val i.val h (fun k hk => hg k (hk.trans i.isLt))
    -- Normalization preserves the proved genuine zero cross pairings.
    simp only [canonicalCGUnitStep, NormedSpace.normalize, real_inner_smul_left, real_inner_smul_right, hz, mul_zero]

end
end krylov.Reference
