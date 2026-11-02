import krylov.OneGradient.XRFCBidiagonal
import krylov.LinearAlgebra.ProjectionRowNorm
set_option autoImplicit false
/-!
Article: main_krylov, apE:Pi, the complete real oblique flag block and row norm.
Use: retain the original actual evaluated-step projector, its literal
chronological r_lk row and its exact spectral norm.
Source: actual CG orthonormality, original bidiagonal inverse columns,
finite-dimensional basis uniqueness and the proved projection/row norm theorem.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Stability krylov.Envelope krylov.LinearAlgebra
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The original boundary row vector of the actual evaluated-step old flag.
Use: its norm is the exact amplification of the real oblique projector.
Article: main_krylov, apE:Pi, r_l=sum_(k>=l) r_lk shat_k. -/
def xrfcFlagRow (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (l : ℕ) :
    EuclideanSpace ℝ (Fin n) :=
  ∑ k : Fin n,(if l≤k.val then xrfcFlagCoefficient trial base g l k.val else 0) •
    canonicalCGUnitStep base g k.val

/-- The actual flag row has exactly its printed coordinates in the true CG frame.
Use: include the boundary coefficient one and every zero earlier coordinate.
Article: main_krylov, apE:Pi.
Proof: the real full-atom CG run generates the orthonormal frame, whose finite
linear-combination pairing extracts the actual supplied coordinate. -/
theorem xrfc_flag_row_coordinates
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (hc : referenceAtomCount base hb g=n) (l : ℕ) (k : Fin n) :
    inner ℝ (canonicalCGUnitStep base g k.val) (xrfcFlagRow trial base g l)=
      if l≤k.val then xrfcFlagCoefficient trial base g l k.val else 0 :=
  (canonicalCG_frame_of_full_atoms base hb g hc).inner_right_fintype _ k

/-- Actual CG unit vectors and the real boundary row are perpendicular to
the strict old prefix, and the true boundary row has norm at least one.
Use: derive the domains of the exact orthogonal-block/row norm formula.
Article: main_krylov, apE:Pi.
Proof: the true row coordinates vanish on the old prefix and its boundary
coordinate is one. CG orthonormality gives the other perpendicularity;
Cauchy--Schwarz applied to the boundary coordinate gives the norm bound. -/
theorem xrfc_flag_row_geometry
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (hc : referenceAtomCount base hb g=n) (l : ℕ) (hl : l<n) :
    canonicalCGUnitStep base g l∈(exploredFlag base g l)ᗮ ∧
      xrfcFlagRow trial base g l∈(exploredFlag base g l)ᗮ ∧ 1≤‖xrfcFlagRow trial base g l‖ := by
  have ho := canonicalCG_frame_of_full_atoms base hb g hc
  have horth (v : EuclideanSpace ℝ (Fin n))
      (hv : ∀ i : ℕ,i<l → inner ℝ v (canonicalCGUnitStep base g i)=0) :
      v∈(exploredFlag base g l)ᗮ := by
    have hK : exploredFlag base g l≤(innerSL ℝ v).ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact hv i.val i.isLt
    exact (Submodule.mem_orthogonal' _ _).mpr (fun w hw => hK hw)
  refine ⟨horth (canonicalCGUnitStep base g l) (fun i hi => ?_),
    horth (xrfcFlagRow trial base g l) (fun i hi => ?_),?_⟩
  · have hne : (⟨l,hl⟩ : Fin n)≠⟨i,hi.trans hl⟩ := by
      intro he
      have heq : l=i := congrArg Fin.val he
      omega
    have hh := orthonormal_iff_ite.mp ho ⟨l,hl⟩ ⟨i,hi.trans hl⟩
    rw [ite_eq_right hne] at hh
    exact hh
  · rw [real_inner_comm,xrfc_flag_row_coordinates trial base hb g hc l ⟨i,by omega⟩,
      ite_eq_right (by change ¬ (l ≤ i);omega)]
  · have hcoord := xrfc_flag_row_coordinates trial base hb g hc l ⟨l,hl⟩
    simp only [le_refl,ite_true,xrfcFlagCoefficient,Finset.Ico_self,Finset.prod_empty] at hcoord
    have hcs := abs_real_inner_le_norm (canonicalCGUnitStep base g l) (xrfcFlagRow trial base g l)
    rw [hcoord,abs_one,ho.norm_eq_one ⟨l,hl⟩,one_mul] at hcs
    exact hcs

/-- The true strict old CG projector selects exactly its original unit prefix.
Use: identify the orthogonal identity block in the full oblique flag formula.
Article: main_krylov, apE:Pi.
Proof: an old unit vector is a true prefix generator; every later one is
orthogonal to the actual span by genuine CG orthonormality. -/
theorem cg_strict_prefix_unit_columns
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (hc : referenceAtomCount base hb g=n) (l : ℕ) (hl : l≤n) (k : Fin n) :
    (exploredFlag base g l).starProjection (canonicalCGUnitStep base g k.val)=
      if k.val<l then canonicalCGUnitStep base g k.val else 0 := by
  have ho := canonicalCG_frame_of_full_atoms base hb g hc
  split_ifs with hkl
  · apply Submodule.starProjection_eq_self_iff.mpr
    exact Submodule.subset_span ⟨⟨k.val,hkl⟩,rfl⟩
  · have horth : canonicalCGUnitStep base g k.val∈(exploredFlag base g l)ᗮ := by
      have hK : exploredFlag base g l≤(innerSL ℝ (canonicalCGUnitStep base g k.val)).ker := by
        apply Submodule.span_le.mpr
        rintro _ ⟨i,rfl⟩
        exact ho.inner_eq_zero (i := k) (j := ⟨i.val,i.isLt.trans_le hl⟩)
          (by intro he;have hi := i.isLt;have heq := congrArg Fin.val he;change k.val=i.val at heq;omega)
      exact (Submodule.mem_orthogonal' _ _).mpr (fun w hw => hK hw)
    rw [Submodule.starProjection_apply,
      Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal horth,Submodule.coe_zero]

/-- The original actual oblique projector is the orthogonal strict-prefix
identity plus its genuine boundary rank-one row.
Use: this is the source's full operator block formula, not merely column bounds.
Article: main_krylov, apE:Pi, Pi_l=sum_(k<l) shat_k shat_k^T+shat_l r_l^T.
Proof: the actual full CG frame is a basis. Its true inverse-column product
formula, strict-prefix projection and exact row coordinates agree on every
basis vector, including the boundary where r_ll=1. -/
theorem xrfc_projector_row_block
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (hc : referenceAtomCount base hb g=n)
    (ht : ∀ i<n,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g i)≠0)
    (l : ℕ) (hl : l<n) :
    cgOperator (transportedFlag (xrfcCanonicalColumns trial base g) l)=
      (exploredFlag base g l).starProjection+
        InnerProductSpace.rankOne ℝ (canonicalCGUnitStep base g l) (xrfcFlagRow trial base g l) := by
  let ho := canonicalCG_frame_of_full_atoms base hb g hc
  let : Nonempty (Fin n) := ⟨⟨l,hl⟩⟩
  let b := basisOfOrthonormalOfCardEqFinrank ho (by simp)
  apply ContinuousLinearMap.coe_injective
  apply b.ext
  intro k
  change cgOperator (transportedFlag (xrfcCanonicalColumns trial base g) l) (b k)=
    (exploredFlag base g l).starProjection (b k)+
      inner ℝ (xrfcFlagRow trial base g l) (b k) • canonicalCGUnitStep base g l
  have hbk : b k=canonicalCGUnitStep base g k.val := congrFun (coe_basisOfOrthonormalOfCardEqFinrank ho (by simp)) k
  rw [hbk,xrfc_projector_unit_columns trial base hb g hc ht l hl k.val k.isLt,
    cg_strict_prefix_unit_columns base hb g hc l hl.le k,real_inner_comm,
    xrfc_flag_row_coordinates trial base hb g hc l k]
  by_cases hlt : k.val<l
  · rw [ite_eq_left hlt,ite_eq_left hlt.le,ite_eq_right (by omega),zero_smul,add_zero]
  · by_cases he : k.val=l
    · rw [he,ite_eq_left le_rfl,ite_eq_right (by omega),ite_eq_left le_rfl,
        xrfcFlagCoefficient,Finset.Ico_self,Finset.prod_empty,one_smul,zero_add]
    · rw [ite_eq_right (by omega),ite_eq_right hlt,ite_eq_left (by omega),zero_add]

/-- The source's true oblique amplification is exactly its printed row norm.
Use: make the sharp XRFC constant and geometric forgetting estimates literal.
Article: main_krylov, apE:Pi, norm(Pi_l)=norm(r_l).
Proof: use the genuine block formula and the row geometry in the exact
orthogonal-projection plus perpendicular-row norm theorem. -/
theorem xrfc_projector_norm
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (hc : referenceAtomCount base hb g=n)
    (ht : ∀ i<n,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g i)≠0)
    (l : ℕ) (hl : l<n) :
    ‖cgOperator (transportedFlag (xrfcCanonicalColumns trial base g) l)‖=‖xrfcFlagRow trial base g l‖ := by
  rw [xrfc_projector_row_block trial base hb g hc ht l hl]
  obtain ⟨hu,hr,hbound⟩ := xrfc_flag_row_geometry trial base hb g hc l hl
  exact projection_row_norm _ _ _ ((canonicalCG_frame_of_full_atoms base hb g hc).norm_eq_one ⟨l,hl⟩) hu hr hbound

end
end krylov.OneGradient
