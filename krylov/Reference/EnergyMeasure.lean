import krylov.Reference.ActiveSpectrum
import jacobi.Finite.DiscreteMeasure

/-!
Article: main_krylov, s2:eq:cg and lem:terminal-fibre, actual full energy spectral measure.
Use: reuse the existing distinct-atom probability data model for the real
normalized spectral weights of the actual canonical initial error.
Source: jacobi.Finite.DiscreteMeasure, the actual Hermitian eigenbasis and Parseval.
-/

namespace krylov.Reference
noncomputable section
open Matrix krylov.Secant
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace BigOperators
variable {n : ℕ}

/-- The actual full energy spectral probability data of the real canonical initial CG error.
Use: the n-atom premise is tied to the existing genuine finite positive probability model,
with its actual nodes, actual squared eigen-coordinates and proved normalization.
Article: main_krylov, s2:eq:cg, ν.
Source: reuse jacobi.Finite.DiscreteMeasure; Parseval in the actual reference eigenbasis.
Proof: the proved actual full-atom condition gives distinct nodes and positive
coordinates; actual eigenbasis Parseval makes the normalized squared weights sum to one. -/
def fullEnergySpectralData (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hbase : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hcount : referenceAtomCount base hbase g=n+1) :
    jacobi.Finite.DiscreteMeasure (n+1) := by
  let v := Matrix.toEuclideanCLM (n := Fin (n+1)) (𝕜 := ℝ) (metricRoot base)⁻¹ g
  obtain ⟨hd, ha⟩ := full_atoms_coordinates base hbase g hcount
  have hv : v≠0 := by
    intro hz
    apply ha 0
    change inner ℝ (hbase.1.eigenvectorBasis 0) v=0
    rw [hz, inner_zero_right]
  have hn : 0<‖v‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
  have hp : (∑ i, (inner ℝ (hbase.1.eigenvectorBasis i) v)^2)=‖v‖^2 := by
    have he := EuclideanSpace.real_norm_sq_eq (hbase.1.eigenvectorBasis.repr v)
    simpa only [hbase.1.eigenvectorBasis.repr.norm_map,
      OrthonormalBasis.repr_apply_apply] using he.symm
  refine ⟨hbase.1.eigenvalues, hd,
    fun i => (inner ℝ (hbase.1.eigenvectorBasis i) v)^2/‖v‖^2,
    fun i => div_pos (sq_pos_of_ne_zero (ha i)) hn, ?_⟩
  -- Normalize only after both the genuine nonzero denominator and actual Parseval sum are established.
  rw [← Finset.sum_div, hp, div_self hn.ne']

end
end krylov.Reference
