import krylov.Reference.Contraction
set_option autoImplicit false
/-!
Article: main_krylov, prop:where, genuine full-atom concentrated reference family.
Use: concentrate the actual initial canonical error near one true eigenmode
while retaining all original active atoms at every positive parameter.
Source: the original positive-root/gradient dictionary and finite Parseval in
the actual Hermitian eigenbasis; no spectral-measure realization is assumed.
-/

namespace krylov.Reference
noncomputable section
open Matrix krylov.Secant
open scoped BigOperators InnerProductSpace
variable {n : ℕ}

/-- The actual canonical initial error with unit chosen mode and parameter-s
coefficients on every other original physical eigenmode.
Use: approach a single atom through genuine full-atom physical references.
Article: main_krylov, prop:where. -/
def concentratedCanonicalVector (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (p : Fin n) (s : ℝ) : EuclideanSpace ℝ (Fin n) :=
  ∑ i : Fin n,(if i=p then (1 : ℝ) else s) • hb.1.eigenvectorBasis i

/-- The actual physical gradient realizing the original concentrated canonical error.
Use: every member is a genuine matrix/gradient reference for the original executor.
Article: main_krylov, prop:where. -/
def concentratedGradient (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (p : Fin n) (s : ℝ) : EuclideanSpace ℝ (Fin n) :=
  cgOperator (metricRoot base) (concentratedCanonicalVector base hb p s)

/-- The true inverse-base canonical error and every actual eigenmode
coordinate of the concentrated physical gradient are exactly the supplied ones.
Use: verify original initial energy and all genuine active spectral weights.
Article: main_krylov, prop:where.
Proof: the actual positive root and its true inverse cancel. Finite
orthonormal eigenbasis pairing extracts each original real coefficient. -/
theorem concentrated_gradient_coordinates
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (p : Fin n) (s : ℝ) :
    cgCanonicalError base (concentratedGradient base hb p s) 0=concentratedCanonicalVector base hb p s ∧
      ∀ i,inner ℝ (hb.1.eigenvectorBasis i)
        (cgCanonicalError base (concentratedGradient base hb p s) 0)=if i=p then 1 else s := by
  have he : cgCanonicalError base (concentratedGradient base hb p s) 0=concentratedCanonicalVector base hb p s := by
    change cgOperator (metricRoot base)⁻¹ (cgOperator (metricRoot base) _)=_
    simp only [cgOperator,← mul_apply_eq_comp,← map_mul,Matrix.nonsing_inv_mul _ (metricRoot_det_unit base hb),
      map_one,one_apply_eq_self]
  refine ⟨he,?_⟩
  intro i
  rw [he]
  exact hb.1.eigenvectorBasis.orthonormal.inner_right_fintype _ i

/-- Every nonzero parameter retains exactly the full original number of
active atoms whenever the actual positive matrix has distinct eigenvalues.
Use: the concentration family never enters a lower-dimensional reference class.
Article: main_krylov, prop:where.
Proof: the genuine canonical coordinates are one or the nonzero parameter;
all are present, and the original actual eigenvalue map is injective. -/
theorem concentrated_gradient_full_atoms
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (hd : Function.Injective hb.1.eigenvalues) (p : Fin n) (s : ℝ) (hs : s≠0) :
    referenceAtomCount base hb (concentratedGradient base hb p s)=n := by
  have hcoord := (concentrated_gradient_coordinates base hb p s).2
  have ha (i : Fin n) : inner ℝ (hb.1.eigenvectorBasis i)
      (cgCanonicalError base (concentratedGradient base hb p s) 0)≠0 := by
    rw [hcoord i]
    split_ifs
    · exact one_ne_zero
    · exact hs
  change ((Finset.univ.filter (fun i => inner ℝ (hb.1.eigenvectorBasis i)
    (cgCanonicalError base (concentratedGradient base hb p s) 0)≠0)).image hb.1.eigenvalues).card=n
  rw [Finset.filter_eq_self.mpr (fun i _ => ha i),Finset.card_image_of_injective _ hd]
  simp only [Finset.card_univ,Fintype.card_fin]

/-- The true initial squared canonical error in the concentrated family is
one plus exactly n-minus-one copies of the squared parameter.
Use: compare the actual first energy drop with the concentrated tail bound.
Article: main_krylov, prop:where.
Proof: finite real Parseval in the original orthonormal eigenbasis, splitting
its genuine chosen index from the n-minus-one other coordinates. -/
theorem concentrated_initial_energy
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (p : Fin n) (s : ℝ) :
    ‖cgCanonicalError base (concentratedGradient base hb p s) 0‖^2=1+(n-1 : ℕ)*s^2 := by
  rw [(concentrated_gradient_coordinates base hb p s).1]
  have h := hb.1.eigenvectorBasis.orthonormal.inner_sum
    (fun i : Fin n => if i=p then (1 : ℝ) else s) (fun i : Fin n => if i=p then (1 : ℝ) else s) Finset.univ
  change inner ℝ (concentratedCanonicalVector base hb p s) (concentratedCanonicalVector base hb p s)=
    ∑ i : Fin n,(if i=p then (1 : ℝ) else s)*(if i=p then 1 else s) at h
  rw [real_inner_self_eq_norm_sq] at h
  rw [h,← Finset.sum_erase_add _ _ (Finset.mem_univ p)]
  have he : (∑ i∈Finset.univ.erase p,(if i=p then (1 : ℝ) else s)*(if i=p then 1 else s))=
      (n-1 : ℕ)*s^2 := by
    calc
      _ = ∑ _i∈Finset.univ.erase p,s^2 := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [ite_eq_right (Finset.mem_erase.mp hi).1,sq]
      _ = _ := by simp only [Finset.sum_const,Finset.card_erase_of_mem (Finset.mem_univ p),Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [he]
  simp only [ite_true,mul_one]
  ring

end
end krylov.Reference
