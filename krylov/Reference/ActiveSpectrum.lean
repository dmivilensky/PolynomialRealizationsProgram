import krylov.Reference.CGPolynomials
import krylov.Reference.OrthonormalSteps
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order

/-!
Article: main_krylov, s2:eq:cg and lem:terminal-fibre, active atoms of the actual reference.
Use: count the genuinely present eigenvalues of the canonical initial error
and discharge true CG nonstagnation and the actual orthonormal step frame.
Source: the actual Hermitian eigenbasis, positive-root functional calculus
and the proved actual CG polynomial root obstruction.
-/

namespace krylov.Reference
noncomputable section
open Matrix Filter krylov.Secant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators
variable {n : ℕ}

/-- The actual positive metric root acts on each true reference eigenvector by its positive scalar square root.
Use: the physical initial gradient and canonical initial error have exactly the same active spectral atoms.
Article: main_krylov, s2:eq:cg, energy spectral measure support.
Source: mathlib's proved Hermitian continuous functional calculus in its actual orthonormal eigenbasis.
Proof: expand the genuine square root in the actual unitary eigenbasis,
cancel the true inverse unitary on the actual eigenvector and evaluate its diagonal entry. -/
theorem metricRoot_eigenvector (base : Matrix (Fin n) (Fin n) ℝ) (hbase : base.PosDef) (i : Fin n) :
    Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base) (hbase.1.eigenvectorBasis i)=
      Real.sqrt (hbase.1.eigenvalues i) • hbase.1.eigenvectorBasis i := by
  -- The actual functional-calculus diagonal is evaluated on the actual eigenvector, without a hypothetical spectral formula.
  have he : metricRoot base*ᵥ WithLp.ofLp (hbase.1.eigenvectorBasis i)=
      Real.sqrt (hbase.1.eigenvalues i) • WithLp.ofLp (hbase.1.eigenvectorBasis i) := by
    rw [metricRoot, CFC.sqrt_eq_cfc, cfc_nnreal_eq_real _ base, hbase.1.cfc_eq,
      Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
    rw [← mulVec_mulVec, hbase.1.star_eigenvectorUnitary_mulVec i, ← mulVec_mulVec,
      diagonal_mulVec_single, mul_one, mulVec_single]
    ext j
    simp only [Pi.smul_apply, smul_eq_mul, Function.comp_apply, Real.coe_sqrt,
      Real.coe_toNNReal', max_eq_left (hbase.posSemidef.eigenvalues_nonneg i),
      RCLike.ofReal_real_eq_id, id_eq]
    exact mul_comm _ _
  ext j
  exact congrFun he j

/-- Distinct spectral values actually present in a vector's genuine Hermitian eigenbasis coordinates.
Use: repeated eigenvalues count once and zero spectral weights count zero times.
Article: main_krylov, s2:eq:cg, the number of atoms of the reference spectral measure. -/
def activeSpectralValues (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.IsHermitian)
    (v : EuclideanSpace ℝ (Fin n)) : Finset ℝ :=
  (Finset.univ.filter fun i => inner ℝ (hb.eigenvectorBasis i) v≠0).image hb.eigenvalues

/-- Actual active atom count of the canonical initial error in the true reference eigenspaces.
Use: this is the paper's n-atom nondegeneracy hypothesis, with repeated/absent atoms handled explicitly.
Article: main_krylov, s2:eq:cg, atom count of ν. -/
def referenceAtomCount (base : Matrix (Fin n) (Fin n) ℝ) (hbase : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) : ℕ :=
  (activeSpectralValues base hbase.1
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base)⁻¹ g)).card

/-- A full actual atom count forces all true canonical spectral coordinates to be present and all eigenvalues distinct.
Use: discharges the concrete eigenvector nonstagnation hypotheses from the article's full-atom premise.
Article: main_krylov, lem:terminal-fibre, n-atom reference.
Proof: image cardinality is at most the number of present coordinates, which
is at most the physical dimension; equality forces every coordinate and an injective eigenvalue map. -/
theorem full_atoms_coordinates (base : Matrix (Fin n) (Fin n) ℝ) (hbase : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hcount : referenceAtomCount base hbase g=n) :
    Function.Injective hbase.1.eigenvalues ∧ ∀ i,
      inner ℝ (hbase.1.eigenvectorBasis i)
        (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base)⁻¹ g)≠0 := by
  -- Equality in both finite cardinality bounds forces every actual coordinate to be present.
  let P := fun i => inner ℝ (hbase.1.eigenvectorBasis i)
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base)⁻¹ g)≠0
  let I := Finset.univ.filter P
  have hImg : (I.image hbase.1.eigenvalues).card=n := hcount
  have hcard : I.card=(Finset.univ : Finset (Fin n)).card := by
    have hc : (I.image hbase.1.eigenvalues).card=n := hcount
    have hl := Finset.card_image_le (s := I) (f := hbase.1.eigenvalues)
    have hu := Finset.card_le_card (Finset.filter_subset P (Finset.univ : Finset (Fin n)))
    change I.card≤(Finset.univ : Finset (Fin n)).card at hu
    simp only [Fintype.card_fin, Finset.card_univ] at hu ⊢
    omega
  have hall := Finset.card_filter_eq_iff.mp hcard
  have hI : I=Finset.univ := Finset.filter_eq_self.mpr hall
  have hc : (Finset.univ.image hbase.1.eigenvalues).card=(Finset.univ : Finset (Fin n)).card := by
    simpa only [hI, Finset.card_univ, Fintype.card_fin] using hImg
  refine ⟨?_, fun i => hall i (Finset.mem_univ i)⟩
  have hi := Finset.injOn_of_card_image_eq hc
  exact fun i j he => hi (Finset.mem_univ i) (Finset.mem_univ j) he

/-- The actual physical-gradient spectral coordinate is its canonical-error coordinate times the positive root eigenvalue.
Use: the paper's energy spectral atoms are the actual active eigenvalues relevant to the real CG recurrence.
Article: main_krylov, s2:eq:cg, equality of active supports.
Proof: move the genuine symmetric metric root from the canonical error onto
the actual eigenvector and use its proved actual square-root eigenvalue action. -/
theorem gradient_spectral_coordinate (base : Matrix (Fin n) (Fin n) ℝ) (hbase : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    inner ℝ (hbase.1.eigenvectorBasis i) g=Real.sqrt (hbase.1.eigenvalues i)*
      inner ℝ (hbase.1.eigenvectorBasis i)
        (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base)⁻¹ g) := by
  -- Move the genuine root across the actual eigenvector pairing, then cancel its actual inverse.
  have hs : (Matrix.toEuclideanLin (metricRoot base)).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr (Matrix.isHermitian_iff_isSymm.mpr (metricRoot_isSymm base))
  have he : inner ℝ (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base) (hbase.1.eigenvectorBasis i))
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base)⁻¹ g)=
        inner ℝ (hbase.1.eigenvectorBasis i) (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base)
          (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base)⁻¹ g)) :=
    hs _ _
  rw [metricRoot_eigenvector base hbase, real_inner_smul_left, ← mul_apply_eq_comp,
    ← map_mul, mul_nonsing_inv _ (metricRoot_det_unit base hbase), map_one, one_apply_eq_self] at he
  exact he.symm

/-- The full actual reference atom count prevents actual CG stagnation before the physical dimension.
Use: the terminal reference frame is obtained from the paper's original atom-count condition.
Article: main_krylov, lem:terminal-fibre and s2:eq:cg, full nonstagnating reference.
Proof: full atoms give distinct true eigenvalues and nonzero true canonical
coordinates. The actual positive metric root preserves their support, and the
proved true residual-polynomial root obstruction gives actual nonstagnation. -/
theorem cg_nonstagnation_of_full_atoms (base : Matrix (Fin n) (Fin n) ℝ) (hbase : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hcount : referenceAtomCount base hbase g=n) :
    ∀ k<n, CG.gradient (cgOperator base) g k≠0 := by
  -- The positive square-root eigenvalues preserve precisely the actual active coordinate support.
  obtain ⟨hdistinct, hactive⟩ := full_atoms_coordinates base hbase g hcount
  have heig (i : Fin n) : cgOperator base (hbase.1.eigenvectorBasis i)=
      hbase.1.eigenvalues i • hbase.1.eigenvectorBasis i := by
    ext j
    exact congrFun (hbase.1.mulVec_eigenvectorBasis i) j
  have ha (i : Fin n) : inner ℝ (hbase.1.eigenvectorBasis i) g≠0 := by
    rw [gradient_spectral_coordinate base hbase]
    exact mul_ne_zero (Real.sqrt_pos.mpr (hbase.eigenvalues_pos i)).ne' (hactive i)
  intro k hk
  exact CG.nonstagnation_of_active_eigenvectors (cgOperator base) (cgOperator_positive base hbase).1 g
    hbase.1.eigenvectorBasis hbase.1.eigenvalues hdistinct heig ha k hk

/-- The actual orthonormal canonical CG frame is derived from the paper's true full-atom premise.
Use: discharges the remaining reference-geometry assumption in the complete terminal fibre.
Article: main_krylov, lem:terminal-fibre, actual nondegenerate full reference.
Proof: combine true active-atom nonstagnation with the actual CG geometric induction and genuine normalization. -/
theorem canonicalCG_frame_of_full_atoms (base : Matrix (Fin n) (Fin n) ℝ) (hbase : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hcount : referenceAtomCount base hbase g=n) :
    Orthonormal ℝ (fun i : Fin n => canonicalCGUnitStep base g i.val) := by
  exact canonicalCGUnitStep_orthonormal base hbase g n (cg_nonstagnation_of_full_atoms base hbase g hcount)

end
end krylov.Reference
