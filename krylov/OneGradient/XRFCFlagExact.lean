import krylov.OneGradient.XRFCFlagRow
set_option autoImplicit false
/-!
Article: Lemma C.2 [apE:Pi] of krylov.tex.
Use: close the source's prefix-space, squared-norm and scalar amplitude
clauses for the actual original full-memory XRFC evaluated-step flags.
Source: genuine nonzero-diagonal span equality, exact actual row norm,
CG orthonormal finite Parseval and true last-amplitude telescoping.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Stability krylov.Envelope krylov.LinearAlgebra
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- Every actual canonical evaluated-step prefix spans exactly its original
CG unit-step prefix, including arbitrary nonzero signed reference trials.
Use: the real evaluated flag is the printed CG flag as a subspace, while its
oblique complement still depends on the later actual evaluated steps.
Article: main_krylov, apE:Pi.
Proof: the true bidiagonal step identity and derived nonzero trial diagonals
supply the finite triangular prefix-span theorem. -/
theorem xrfc_canonical_prefix_span
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (hc : referenceAtomCount base hb g=n)
    (ht : ∀ i<n,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g i)≠0)
    (l : ℕ) (hl : l<n) :
    Submodule.span ℝ ((fun j => cgOperator (metricRoot base)
      (oneGradientStep (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g j)) '' Set.Iic l)=
    Submodule.span ℝ (canonicalCGUnitStep base g '' Set.Iic l) := by
  have hs := xrfc_canonical_step_bidiagonal trial base hb g hc (by omega) ht
  have h := bidiagonal_prefix_span (canonicalCGUnitStep base g)
    (fun j => cgOperator (metricRoot base)
      (oneGradientStep (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g j))
    (xrfcCanonicalOffDiagonal trial base g) (xrfcCanonicalDiagonal trial base g) n (l+1) (by omega)
    (xrfc_canonical_diagonal_ne_zero trial base hb g hc ht) hs.1 hs.2
  have hset : (Set.Iio (l+1) : Set ℕ)=Set.Iic l := by
    ext j
    simp only [Set.mem_Iio,Set.mem_Iic]
    omega
  simpa only [hset] using h

/-- The literal squared row norm is one plus the sum of squared real
chronological tail products.
Use: compute the original oblique projector amplification explicitly.
Article: main_krylov, apE:Pi, norm(Pi_l)^2=1+sum_(k>l) r_lk^2.
Proof: finite CG orthonormal Parseval gives the sum of actual row-coordinate
squares; its boundary coordinate is the empty product one and earlier
coordinates vanish. -/
theorem xrfc_flag_row_norm_sq
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (hc : referenceAtomCount base hb g=n) (l : ℕ) (hl : l<n) :
    ‖xrfcFlagRow trial base g l‖^2=1+
      ∑ k∈(Finset.univ.filter (fun k : Fin n => l<k.val)),(xrfcFlagCoefficient trial base g l k.val)^2 := by
  let w := fun k : Fin n => if l≤k.val then xrfcFlagCoefficient trial base g l k.val else 0
  have ho := canonicalCG_frame_of_full_atoms base hb g hc
  have h := ho.inner_sum w w Finset.univ
  change inner ℝ (xrfcFlagRow trial base g l) (xrfcFlagRow trial base g l)=_ at h
  rw [real_inner_self_eq_norm_sq] at h
  change ‖xrfcFlagRow trial base g l‖^2=∑ k : Fin n,w k*w k at h
  have hw (k : Fin n) : w k*w k=(if k=⟨l,hl⟩ then (1 : ℝ) else 0)+
      (if l<k.val then (xrfcFlagCoefficient trial base g l k.val)^2 else 0) := by
    by_cases he : k=⟨l,hl⟩
    · subst k
      simp only [w,le_refl,ite_true,xrfcFlagCoefficient,Finset.Ico_self,Finset.prod_empty,
        mul_one,lt_self_iff_false,ite_false,add_zero]
    · have hne : k.val≠l := by intro heq;exact he (Fin.ext heq)
      by_cases hlt : l<k.val
      · simp only [w,ite_eq_left hlt.le,ite_eq_right he,zero_add,ite_eq_left hlt,sq]
      · have hle : ¬ (l≤k.val) := by omega
        simp only [w,ite_eq_right hle,zero_mul,ite_eq_right he,ite_eq_right hlt,add_zero]
  rw [h]
  simp_rw [hw]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true,← Finset.sum_filter]

/-- The exact spectral matrix norm of the original projector is its genuine
boundary-row norm in the actual canonical metric.
Use: preserve the source matrix norm convention literally.
Article: main_krylov, apE:Pi.
Proof: the standard Euclidean matrix/operator isometry transfers the already
proved genuine row-block norm equality. -/
theorem xrfc_projector_matrix_norm
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (hc : referenceAtomCount base hb g=n)
    (ht : ∀ i<n,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g i)≠0)
    (l : ℕ) (hl : l<n) :
    ‖transportedFlag (xrfcCanonicalColumns trial base g) l‖=‖xrfcFlagRow trial base g l‖ := by
  rw [Matrix.cstar_norm_def]
  exact xrfc_projector_norm trial base hb g hc ht l hl

/-- The original last trial amplitude times its real oblique tail product
is exactly the original earlier amplitude, even when either one is zero.
Use: the scalar telescoping identity never divides by a trial error.
Article: main_krylov, apE:Pi, a_(n-1) r_(l,n-1)=a_l.
Proof: the true last-column projector formula and actual native weighted-prefix
amplitude identity agree. Pair their genuine boundary unit direction to
extract the real scalar equality. -/
theorem xrfc_flag_last_scalar_amplitude
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (hc : referenceAtomCount base hb g=n)
    (ht : ∀ i<n,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g i)≠0)
    (l : ℕ) (hl : l<n) :
    xrfcTrialCoefficient trial base g n (n-1)*xrfcFlagCoefficient trial base g l (n-1)=
      xrfcTrialCoefficient trial base g n l := by
  have hcol := xrfc_projector_unit_columns trial base hb g hc ht l hl (n-1) (by omega)
  have hPu : cgOperator (transportedFlag (xrfcCanonicalColumns trial base g) l)
      (canonicalCGUnitStep base g (n-1))=
      xrfcFlagCoefficient trial base g l (n-1) • canonicalCGUnitStep base g l := by
    dsimp only at hcol
    by_cases he : n-1=l
    · rw [he] at hcol ⊢
      simpa only [le_refl,ite_true,xrfcFlagCoefficient,Finset.Ico_self,Finset.prod_empty,one_smul] using hcol
    · rw [ite_eq_right (by omega)] at hcol
      exact hcol
  have h := xrfc_projector_last_amplitude trial base hb g hc ht l hl
  dsimp only at h
  rw [map_smul,hPu,smul_smul] at h
  have hp := congrArg (fun v => inner ℝ (canonicalCGUnitStep base g l) v) h
  have hu := (canonicalCG_frame_of_full_atoms base hb g hc).norm_eq_one ⟨l,hl⟩
  simpa only [real_inner_smul_right,real_inner_self_eq_norm_sq,hu,one_pow,mul_one] using hp

end
end krylov.OneGradient
