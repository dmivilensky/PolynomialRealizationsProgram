import jacobi.Comparison.CellGram
import jacobi.Analysis.PairedPrefix

/-!
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
The actual cell-integrated comparison form is a matrix on the original
physical indices. Zero padding preserves the entire original half prefix,
including its middle row, and yields one uniform positive lower bound.
Use: cellPerturbation_coercive supplies the actual positive comparison matrix for the source's uniform finite Gram lower bound.
-/
namespace jacobi.Comparison
noncomputable section
open Real Set MeasureTheory jacobi.Reference jacobi.Analysis jacobi.GelfandLevitan
attribute [local instance] Measure.Subtype.measureSpace

/-- The genuine cell-integrated two-edge perturbation on original
matrix indices, with the original alternating second-edge sign.
Use: cellPerturbation_coercive supplies the actual positive comparison
matrix for the source's uniform finite Gram lower bound.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
-/
def cellPerturbation (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ)
    (i j:Fin (n+1)) : ℝ :=
  (((n:ℝ)+5)/4)*
    (cellKernelEntry (kernelMap a ha) (halfCell ((n:ℝ)+5) (i.val/2))
      (halfCell ((n:ℝ)+5) (j.val/2))+
    (-1:ℝ)^(i.val+j.val)*
    cellKernelEntry (kernelMap b hb) (halfCell ((n:ℝ)+5) (i.val/2))
      (halfCell ((n:ℝ)+5) (j.val/2)))

/-- Pairing preserves the actual quotient cell and the exact original
parity of the second edge.
Use: cellPerturbation_form regroups the original matrix into the true
continuum forms on P and Q, with no omitted midpoint coordinate.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Proof: division by two recovers the pair index. The two even exponent
parts contribute one and leave exactly the two within-pair signs. -/
theorem cellPerturbation_pair (a b:ℝ) (ha:-1<a) (hb:-1<b)
    (n:ℕ) (hn:1≤n) (p q:Fin (pairCount n) × Fin 2) :
    cellPerturbation a b ha hb n (pairIndex n hn p) (pairIndex n hn q) =
      (((n:ℝ)+5)/4)*
      (cellKernelEntry (kernelMap a ha) (halfCell ((n:ℝ)+5) p.1.val) (halfCell ((n:ℝ)+5) q.1.val)+
      (-1:ℝ)^(p.2.val+q.2.val)*
      cellKernelEntry (kernelMap b hb) (halfCell ((n:ℝ)+5) p.1.val) (halfCell ((n:ℝ)+5) q.1.val)) := by
  have hp := p.2.isLt
  have hq := q.2.isLt
  have hpd : (pairIndex n hn p).val/2=p.1.val := by dsimp [pairIndex]; omega
  have hqd : (pairIndex n hn q).val/2=q.1.val := by dsimp [pairIndex]; omega
  have he : (pairIndex n hn p).val+(pairIndex n hn q).val=
      2*(p.1.val+q.1.val)+(p.2.val+q.2.val) := by dsimp [pairIndex]; omega
  simp only [cellPerturbation,hpd,hqd,he,pow_add,pow_mul]
  norm_num

/-- The genuine original-index cell matrix has exactly the paired
continuum quadratic form on every actual half-supported finite vector.
Use: cellPerturbation_coercive applies the two actual continuum gaps to
the full original physical half prefix, rather than an even truncation.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Proof: transport both actual finite sums through the injective padded
pairing. Use the exact two-edge paired identity and the actual physical
cell-integral formulas; the finite paired-norm identity cancels the
continuum identity terms with their exact n'/4 normalization. -/
theorem cellPerturbation_form (a b:ℝ) (ha:-1<a) (hb:-1<b)
    (n:ℕ) (hn:1≤n) (v:Fin (n+1)→ℝ) (hv:∀i, n+1<2*i.val → v i=0) :
    (∑ i, (v i)^2)+(∑ i, ∑ j, cellPerturbation a b ha hb n i j*v i*v j) =
      pairedCellForm a b ha hb ((n:ℝ)+5) (fun p => v (pairIndex n hn p)) := by
  -- Exact zero padding preserves the original norm and both indices of its quadratic form.
  let w : Fin (pairCount n) × Fin 2 → ℝ := fun p => v (pairIndex n hn p)
  have hL : 4*(pairCount n:ℝ)≤(n:ℝ)+5 := by
    have hh : 4*pairCount n≤n+5 := by dsimp [pairCount]; omega
    exact_mod_cast hh
  rw [← pairIndex_sum n hn (fun i => (v i)^2) (fun i hi => by rw [hv i hi]; norm_num),
    ← pairIndex_quadratic n hn (cellPerturbation a b ha hb n) v hv]
  simp_rw [cellPerturbation_pair a b ha hb n hn]
  -- Adjacent pairing separates the alpha and beta forms before any limiting approximation.
  have hs : (∑ p, ∑ q,
      ((((n:ℝ)+5)/4)*
      (cellKernelEntry (kernelMap a ha) (halfCell ((n:ℝ)+5) p.1.val) (halfCell ((n:ℝ)+5) q.1.val)+
      (-1:ℝ)^(p.2.val+q.2.val)*
      cellKernelEntry (kernelMap b hb) (halfCell ((n:ℝ)+5) p.1.val) (halfCell ((n:ℝ)+5) q.1.val)))*w p*w q) =
      (((n:ℝ)+5)/4)*
      ((∑ i,∑ j, cellKernelEntry (kernelMap a ha) (halfCell ((n:ℝ)+5) i.val)
        (halfCell ((n:ℝ)+5) j.val)*pairPlus w i*pairPlus w j)+
       (∑ i,∑ j, cellKernelEntry (kernelMap b hb) (halfCell ((n:ℝ)+5) i.val)
        (halfCell ((n:ℝ)+5) j.val)*pairMinus w i*pairMinus w j)) := by
    rw [← paired_kernel_quadratic]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    ring
  change (∑ p, (w p)^2)+_ = _
  rw [hs]
  -- The exact physical cell norms recover the identity contribution with its M/4 factor.
  unfold pairedCellForm
  rw [halfCellVector_quadratic a ha (by positivity) hL,
    halfCellVector_quadratic b hb (by positivity) hL]
  have hnorm := paired_norm w
  have hM : (n:ℝ)+5≠0 := by positivity
  field_simp
  nlinarith [hnorm]

/-- The true original-index cell comparison matrix has a common strictly
positive lower bound on all actual physical half-supported vectors.
Use: the uniform Gram approximation can be absorbed into this bound
to establish uniform coercivity of every original principal section.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Proof: exact zero padding identifies the original matrix form with
the two genuinely coercive continuum cell forms. Their common gap is
independent of mesh size, and the norm transport is exact. -/
theorem cellPerturbation_coercive (a b:ℝ) (ha:-1<a) (hb:-1<b) :
    ∃ κ:ℝ, 0<κ ∧ ∀ n:ℕ, 1≤n → ∀ v:Fin (n+1)→ℝ,
      (∀i, n+1<2*i.val → v i=0) →
      κ*(∑ i, (v i)^2) ≤
      (∑ i, (v i)^2)+(∑ i, ∑ j, cellPerturbation a b ha hb n i j*v i*v j) := by
  -- Apply the genuine paired continuum bound only after identifying the original finite form.
  obtain ⟨κ,hκ,hbound⟩ := pairedCellForm_coercive a b ha hb
  refine ⟨κ,hκ,fun n hn v hv => ?_⟩
  rw [cellPerturbation_form a b ha hb n hn v hv]
  have hL : 4*(pairCount n:ℝ)≤(n:ℝ)+5 := by
    have hh : 4*pairCount n≤n+5 := by dsimp [pairCount]; omega
    exact_mod_cast hh
  have hbnd := hbound ((n:ℝ)+5) (by positivity) (pairCount n) hL (fun p => v (pairIndex n hn p))
  rw [pairIndex_sum n hn (fun i => (v i)^2) (fun i hi => by rw [hv i hi]; norm_num)] at hbnd
  exact hbnd

end
end jacobi.Comparison
