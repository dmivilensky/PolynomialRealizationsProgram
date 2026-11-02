import krylov.Reference.CanonicalGradient
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
Article: main_krylov, s2:eq:cg and lem:terminal-fibre, completion of the actual full reference.
Use: an actual orthonormal full CG step frame forces its true terminal gradient
to vanish; terminal data-fibre proofs do not assume their desired last gradient.
Source: exact line search, the actual canonical gradient recurrence and the
finite-dimensional spanning property of a full orthonormal family.
-/

namespace krylov.Reference
noncomputable section
open Matrix krylov.Secant
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace
variable {n : ℕ}

/-- Every actual nonzero canonical reference step is orthogonal to its actual post-search canonical gradient.
Use: exact line-search orthogonality is transferred through the true metric coordinates.
Article: main_krylov, s2:eq:cg and lem:terminal-fibre.
Proof: the actual positive curvature makes the true line denominator nonzero;
the physical exact-search pairing vanishes, and true primal/dual metric pairing
then gives the normalized canonical orthogonality. -/
theorem canonicalCG_postsearch_orth (base : Matrix (Fin n) (Fin n) ℝ) (hbase : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (hs : canonicalCGStep base g k≠0) :
    inner ℝ (canonicalCGUnitStep base g k)
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base)⁻¹
        (cgRun (cgOperator base) g (k+1)).gradient)=0 := by
  let d := (cgRun (cgOperator base) g k).direction
  have hd : Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base) d≠0 := by
    intro hz
    dsimp only [d] at hz
    apply hs
    simp only [canonicalCGStep, cgStep, map_smul, hz, smul_zero]
  have hc : inner ℝ d (cgOperator base d)≠0 := by
    rw [canonical_search_pairing base hbase d (cgOperator base d),
      canonical_reference_action base hbase, real_inner_self_eq_norm_sq]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hd)
  have hp : inner ℝ d (cgRun (cgOperator base) g (k+1)).gradient=0 := by
    change inner ℝ d (searchedGradient (cgRun (cgOperator base) g k).gradient d (cgOperator base d))=0
    rw [searchedGradient, inner_add_right, real_inner_smul_right, lineLength, div_mul_cancel₀ _ hc]
    abel
  have he : inner ℝ (canonicalCGStep base g k)
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base)⁻¹
        (cgRun (cgOperator base) g (k+1)).gradient)=0 := by
    rw [canonicalCGStep, cgStep, map_smul, real_inner_smul_left,
      ← canonical_search_pairing base hbase, hp, mul_zero]
  -- Divide only by the actual nonzero step norm after proving the exact unnormalized pairing.
  have hn := norm_ne_zero_iff.mpr hs
  have hmul : ‖canonicalCGStep base g k‖*inner ℝ (canonicalCGUnitStep base g k)
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base)⁻¹
        (cgRun (cgOperator base) g (k+1)).gradient)=0 := by
    rw [← real_inner_smul_left]
    simpa only [canonicalCGUnitStep, NormedSpace.norm_smul_normalize] using he
  exact (mul_eq_zero.mp hmul).resolve_left hn

/-- Every actual old normalized reference step remains orthogonal to every later actual canonical gradient.
Use: full reference completion follows from actual line searches and actual conjugate steps.
Article: main_krylov, s2:eq:cg, full-cycle reference orthogonality.
Proof: the true post-search pairing vanishes; each later true canonical gradient
increment is an actual orthogonal reference step and therefore preserves that pairing. -/
theorem canonicalCG_old_step_orth (base : Matrix (Fin n) (Fin n) ℝ) (hbase : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (M : ℕ)
    (ho : Orthonormal ℝ (fun i : Fin M => canonicalCGUnitStep base g i.val)) (i : Fin M) :
    ∀ k≤M, i.val<k → inner ℝ (canonicalCGUnitStep base g i.val)
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base)⁻¹ (cgRun (cgOperator base) g k).gradient)=0 := by
  -- Start at the true exact-search pairing, then transport it through every later orthogonal increment.
  have hs : canonicalCGStep base g i.val≠0 := by
    intro hz
    exact ho.ne_zero i (by simp only [canonicalCGUnitStep, hz, NormedSpace.normalize_zero_eq_zero])
  intro k
  induction k with
  | zero => intro _ hik; omega
  | succ k ih =>
    intro hk hik
    by_cases hi : i.val=k
    · subst k
      exact canonicalCG_postsearch_orth base hbase g i.val hs
    · have hik' : i.val<k := by omega
      have hold := ih (by omega) hik'
      rw [canonicalCG_gradient_step base hbase g k, inner_add_right, hold, zero_add]
      have hn : canonicalCGStep base g k=‖canonicalCGStep base g k‖ • canonicalCGUnitStep base g k :=
        (NormedSpace.norm_smul_normalize _).symm
      rw [hn, real_inner_smul_right]
      have ho0 := ho.inner_eq_zero (i := i) (j := ⟨k, by omega⟩) (by intro hz; exact hi (congrArg Fin.val hz))
      rw [ho0, mul_zero]

/-- A full actual orthonormal frame of true CG steps forces actual finite termination.
Use: the terminal data-fibre residual is derived from a genuine completed reference run.
Article: main_krylov, s2:eq:cg and lem:terminal-fibre, full reference completion.
Proof: all true old-step pairings with the actual terminal canonical gradient
vanish. The actual orthonormal family has the full physical dimension and hence
spans; its true orthogonal gradient is zero, and the actual invertible root recovers the physical zero. -/
theorem cg_full_frame_terminates (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hbase : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1)))
    (ho : Orthonormal ℝ (fun i : Fin (n+1) => canonicalCGUnitStep base g i.val)) :
    (cgRun (cgOperator base) g (n+1)).gradient=0 := by
  let v := Matrix.toEuclideanCLM (n := Fin (n+1)) (𝕜 := ℝ) (metricRoot base)⁻¹
    (cgRun (cgOperator base) g (n+1)).gradient
  let b := basisOfOrthonormalOfCardEqFinrank ho (by simp)
  have hb : Submodule.span ℝ (Set.range fun i : Fin (n+1) => canonicalCGUnitStep base g i.val)=⊤ := by
    simpa only [b, coe_basisOfOrthonormalOfCardEqFinrank] using b.span_eq
  have hle : Submodule.span ℝ (Set.range fun i : Fin (n+1) => canonicalCGUnitStep base g i.val)≤
      (innerSL ℝ v).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change inner ℝ v (canonicalCGUnitStep base g i.val)=0
    rw [real_inner_comm]
    exact canonicalCG_old_step_orth base hbase g (n+1) ho i (n+1) le_rfl i.isLt
  have hv : v=0 := by
    have he : inner ℝ v v=0 := hle (by rw [hb]; trivial)
    exact inner_self_eq_zero.mp he
  -- Cancel the actual inverse root only after the canonical gradient has been proved zero.
  have he := congrArg (Matrix.toEuclideanCLM (n := Fin (n+1)) (𝕜 := ℝ) (metricRoot base)) hv
  change Matrix.toEuclideanCLM (n := Fin (n+1)) (𝕜 := ℝ) (metricRoot base)
    (Matrix.toEuclideanCLM (n := Fin (n+1)) (𝕜 := ℝ) (metricRoot base)⁻¹
      (cgRun (cgOperator base) g (n+1)).gradient)=_ at he
  simpa only [← mul_apply_eq_comp, ← map_mul, mul_nonsing_inv _ (metricRoot_det_unit base hbase),
    map_one, one_apply_eq_self, map_zero] using he

/-- The actual penultimate canonical gradient is the negative actual last reference step.
Use: the planar terminal residual starts from the true completed CG reference gradient.
Article: main_krylov, lem:terminal-fibre, ĝ_(n−1)=−√c h.
Proof: actual full-frame termination and the true canonical gradient update
give ĝ_last=−ŝ_last; zero-safe normalization identifies the actual step length. -/
theorem canonicalCG_last_gradient (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hbase : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1)))
    (ho : Orthonormal ℝ (fun i : Fin (n+1) => canonicalCGUnitStep base g i.val)) :
    Matrix.toEuclideanCLM (n := Fin (n+1)) (𝕜 := ℝ) (metricRoot base)⁻¹ (cgRun (cgOperator base) g n).gradient=
      -‖canonicalCGStep base g n‖ • canonicalCGUnitStep base g n := by
  have he := canonicalCG_gradient_step base hbase g n
  rw [cg_full_frame_terminates base hbase g ho, map_zero] at he
  have hh : Matrix.toEuclideanCLM (n := Fin (n+1)) (𝕜 := ℝ) (metricRoot base)⁻¹
      (cgRun (cgOperator base) g n).gradient= -canonicalCGStep base g n := by
    exact eq_neg_of_add_eq_zero_left he.symm
  simpa only [neg_smul, canonicalCGUnitStep, NormedSpace.norm_smul_normalize] using hh

end
end krylov.Reference
