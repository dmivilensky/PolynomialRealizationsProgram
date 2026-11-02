import krylov.Reference.EnergyMeasure

/-!
Article: main_krylov, s2:eq:cg, the spectral measure for arbitrary active support.
Use: aggregate repeated eigenvalues, discard zero weights, and normalize only
for a genuinely nonzero vector. The zero reference is treated by the stopping theorem.
Source: the finite spectral theorem and Parseval; the measure type and its
polynomial L² model are reused from jacobi.Finite.DiscreteMeasure.
-/

namespace krylov.Reference
noncomputable section
open Matrix krylov.Secant
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace BigOperators
variable {n : ℕ}

/-- The squared spectral mass of one eigenspace, including all its multiplicities.
Use: defines a measure independent of repeated eigenvalue labels.
Article: main_krylov, s2:eq:cg, the unnormalized energy spectral mass. -/
def spectralMass (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.IsHermitian)
    (v : EuclideanSpace ℝ (Fin n)) (t : ℝ) : ℝ :=
  ∑ i : Fin n with hb.eigenvalues i=t, (inner ℝ (hb.eigenvectorBasis i) v)^2

/-- Every genuinely active eigenspace has strictly positive total squared mass.
Use: the aggregated atoms have positive rather than merely nonnegative weights.
Article: main_krylov, s2:eq:cg, support of the spectral measure.
Proof: every summand is a square, and membership supplies one nonzero coordinate. -/
theorem spectralMass_pos (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.IsHermitian)
    (v : EuclideanSpace ℝ (Fin n)) {t : ℝ} (ht : t∈activeSpectralValues base hb v) :
    0<spectralMass base hb v t := by
  obtain ⟨i, hi, he⟩ := Finset.mem_image.mp ht
  exact Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨i,
    Finset.mem_filter.mpr ⟨Finset.mem_univ i, he⟩,
    sq_pos_of_ne_zero (Finset.mem_filter.mp hi).2⟩

/-- Summing against the distinct active spectral masses is exactly summing all eigenbasis coordinates.
Use: a single aggregation identity supplies probability, moments and polynomial energy integrals.
Article: main_krylov, s2:eq:cg, finite spectral integration.
Proof: group the squared coordinates by eigenvalue, and remove only coordinates whose square is zero. -/
theorem spectralMass_sum (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.IsHermitian)
    (v : EuclideanSpace ℝ (Fin n)) (f : ℝ → ℝ) :
    (∑ t∈activeSpectralValues base hb v, spectralMass base hb v t*f t)=
      ∑ i : Fin n, (inner ℝ (hb.eigenvectorBasis i) v)^2*f (hb.eigenvalues i) := by
  -- First restore all spectral values; an omitted value has only zero eigen-coordinates.
  let S := activeSpectralValues base hb v
  let T := Finset.univ.image hb.eigenvalues
  have hST : S⊆T := Finset.image_subset_image (Finset.filter_subset _ _)
  have hext : (∑ t∈S, spectralMass base hb v t*f t)=
      ∑ t∈T, spectralMass base hb v t*f t := by
    apply Finset.sum_subset hST
    intro t _ ht
    have hz : spectralMass base hb v t=0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hc : inner ℝ (hb.eigenvectorBasis i) v=0 := by
        by_contra h
        exact ht (Finset.mem_image.mpr ⟨i,
          Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩, (Finset.mem_filter.mp hi).2⟩)
      rw [hc, zero_pow (by omega : 2≠0)]
    rw [hz, zero_mul]
  rw [hext]
  have he : (∑ t∈T, spectralMass base hb v t*f t)=
      ∑ t∈T, ∑ i : Fin n with hb.eigenvalues i=t,
        (inner ℝ (hb.eigenvectorBasis i) v)^2*f (hb.eigenvalues i) := by
    apply Finset.sum_congr rfl
    intro t _
    rw [spectralMass, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [(Finset.mem_filter.mp hi).2]
  rw [he]
  exact Finset.sum_fiberwise_of_maps_to
    (fun i _ => Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩) _

/-- The actual distinct-atom spectral probability data of any nonzero vector.
Use: both energy and gradient spectral measures share the same finite measure and Jacobi machinery.
Article: main_krylov, s2:eq:cg and s5:fibre, normalized spectral measure.
Proof: aggregate true eigenspace masses; Parseval proves probability one. -/
def vectorSpectralData (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.IsHermitian)
    (v : EuclideanSpace ℝ (Fin n)) (hv : v≠0) :
    jacobi.Finite.DiscreteMeasure (activeSpectralValues base hb v).card := by
  let S := activeSpectralValues base hb v
  let e := S.equivFin.symm
  have hn : 0<‖v‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
  refine ⟨fun i => (e i).val, Subtype.val_injective.comp e.injective,
    fun i => spectralMass base hb v (e i).val/‖v‖^2,
    fun i => div_pos (spectralMass_pos base hb v (e i).property) hn, ?_⟩
  -- Enumeration preserves the actual finite sum; its unnormalized mass is the true squared norm.
  have hp : (∑ i : Fin n, (inner ℝ (hb.eigenvectorBasis i) v)^2)=‖v‖^2 := by
    simpa only [hb.eigenvectorBasis.repr.norm_map, OrthonormalBasis.repr_apply_apply]
      using (EuclideanSpace.real_norm_sq_eq (hb.eigenvectorBasis.repr v)).symm
  rw [← Finset.sum_div, e.sum_comp (fun t : S => spectralMass base hb v t.val),
    ← Finset.sum_subtype S (fun _ => Iff.rfl)]
  have hm := spectralMass_sum base hb v (fun _ => 1)
  simp only [mul_one] at hm
  rw [hm, hp, div_self hn.ne']

/-- Integration against the constructed spectral probability is the normalized genuine spectral sum.
Use: ties all polynomial and quadrature statements to the actual matrix and vector.
Article: main_krylov, s2:eq:cg, the energy spectral dictionary.
Proof: undo the support enumeration and use the established aggregation identity. -/
theorem vectorSpectralData_integral (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.IsHermitian)
    (v : EuclideanSpace ℝ (Fin n)) (hv : v≠0) (f : ℝ → ℝ) :
    (∑ i, (vectorSpectralData base hb v hv).weight i*f ((vectorSpectralData base hb v hv).node i))=
      (∑ i : Fin n, (inner ℝ (hb.eigenvectorBasis i) v)^2*f (hb.eigenvalues i))/‖v‖^2 := by
  -- The construction keeps the actual weights, rather than only an abstract existence witness.
  change (∑ i : Fin (activeSpectralValues base hb v).card,
    spectralMass base hb v ((activeSpectralValues base hb v).equivFin.symm i).val/‖v‖^2*
      f ((activeSpectralValues base hb v).equivFin.symm i).val)=_
  simp only [div_mul_eq_mul_div, ← Finset.sum_div]
  rw [(activeSpectralValues base hb v).equivFin.symm.sum_comp
    (fun t : activeSpectralValues base hb v => spectralMass base hb v t.val*f t.val),
    ← Finset.sum_subtype (activeSpectralValues base hb v) (fun _ => Iff.rfl)
      (fun t => spectralMass base hb v t*f t),
    spectralMass_sum]

/-- Every atom of the constructed spectral measure of a positive matrix is strictly positive.
Use: all inverse moments and exterior-zero normalizations have genuine nonzero spectral denominators.
Article: main_krylov, s2:eq:cg, ν and σ on a positive interval.
Proof: each enumerated active atom is an actual eigenvalue of the original positive matrix. -/
theorem vectorSpectralData_node_pos (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (v : EuclideanSpace ℝ (Fin n)) (hv : v≠0)
    (j : Fin (activeSpectralValues base hb.1 v).card) :
    0<(vectorSpectralData base hb.1 v hv).node j := by
  let t := (activeSpectralValues base hb.1 v).equivFin.symm j
  obtain ⟨i, _, he⟩ := Finset.mem_image.mp t.property
  change 0<t.val
  rw [← he]
  exact hb.eigenvalues_pos i

end
end krylov.Reference
