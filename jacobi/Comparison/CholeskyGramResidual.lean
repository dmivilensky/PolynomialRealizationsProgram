import jacobi.Comparison.TwoEdgeCholeskyResidual
import jacobi.Comparison.UniformGram
import jacobi.Analysis.CoerciveSystem

/-!
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
Replacing the sampled source F kernels by the actual original finite
Gram entries preserves uniform vanishing of the complete GL residual.
All estimates concern the genuine constructed transformation kernels.
Use: choleskyResidual_uniform controls the original growing-prefix error when replacing the source kernels by actual Gram entries.
-/
namespace jacobi.Comparison
noncomputable section
open Real Set Filter jacobi.Reference jacobi.Analysis jacobi.GelfandLevitan jacobi.Finite
open scoped Topology
attribute [local irreducible] kernel transformationKernel
set_option backward.isDefEq.respectTransparency false

/-- The actual sampled two-edge transformation kernel is uniformly
bounded at every original matrix dimension and pair of indices.
Use: choleskyResidual_uniform controls the original growing-prefix
error when replacing the source kernels by actual Gram entries.
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
Proof: both genuine original continuous transformation kernels have
proved compact bounds; the unchanged original parity has absolute one. -/
theorem twoEdgeTransformation_bounded (a b:ℝ) (ha:-1<a) (hb:-1<b) :
    ∃ C:ℝ, 0<C ∧ ∀ n:ℕ, ∀ i j:Fin (n+1), |twoEdgeTransformation a b ha hb n i j|≤C := by
  obtain ⟨A,hA,hKA⟩ := transformationKernel_bounded a ha
  obtain ⟨B,hB,hKB⟩ := transformationKernel_bounded b hb
  refine ⟨A+B,by positivity,fun n i j => ?_⟩
  unfold twoEdgeTransformation
  exact (abs_add_le _ _).trans (by
    rw [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul]
    exact add_le_add (hKA _ _) (hKB _ _))

/-- At genuine physical matrix indices the actual two-edge sampled
kernel is exactly the source expression in the uniform Gram theorem.
Use: choleskyResidual_uniform replaces those original kernel samples by
the actual original Gram entries with their proved full uniform error.
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
Proof: the actual physical half-coordinate clamp fixes both original
matrix mesh coordinates, including the exact midpoint. -/
theorem twoEdgeKernel_physical (a b:ℝ) (ha:-1<a) (hb:-1<b)
    {n:ℕ} (i j:Fin (n+1)) (hi:2*i.val≤n+1) (hj:2*j.val≤n+1) :
    twoEdgeKernel a b ha hb n i j=kernel a ha (matrixMesh n i) (matrixMesh n j)+
      (-1:ℝ)^(i.val+j.val)*kernel b hb (matrixMesh n i) (matrixMesh n j) := by
  have hpi : matrixHalfPoint n i=(⟨matrixMesh n i,matrixMesh_mem_half hi⟩:HalfInterval) :=
    Set.projIcc_of_mem (by norm_num) (matrixMesh_mem_half hi)
  have hpj : matrixHalfPoint n j=(⟨matrixMesh n j,matrixMesh_mem_half hj⟩:HalfInterval) :=
    Set.projIcc_of_mem (by norm_num) (matrixMesh_mem_half hj)
  simp only [twoEdgeKernel,hpi,hpj]

/-- The literal actual finite Gram residual of the two genuine sampled
transformation kernels, in original matrix-size normalization.
Use: the exact original Cholesky difference row has right-hand side
minus this residual; the genuine uniform inverse estimate then proves
the complete continuum coefficient limit.
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
-/
def choleskyResidual (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) (i j:Fin (n+1)) : ℝ :=
  twoEdgeTransformation a b ha hb n i j+((n:ℝ)+1)*gramPerturbation a b ha hb n i j+
    (∑l:Fin i.val, twoEdgeTransformation a b ha hb n i (Gram.before i l)*
      gramPerturbation a b ha hb n (Gram.before i l) j)

/-- The complete residual of the actual finite Gram equation vanishes
uniformly over all original physical half-chain row-column pairs.
Use: the final genuine coefficient stability argument has its entire
source right-hand side proved uniformly small, with no residual premise.
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
Proof: the sampled two-edge GL residual already vanishes uniformly.
The actual uniform Gram approximation contributes its row error and
a preceding-prefix sum weighted by the genuinely bounded K. Its true
prefix count is at most the original matrix size, so both errors vanish. -/
theorem choleskyResidual_uniform (a b:ℝ) (ha:-1<a) (hb:-1<b) :
    ∀ ε:ℝ, 0<ε → ∃ N:ℕ, ∀ n≥N, ∀ i j:Fin (n+1),
      2*i.val≤n+1 → 2*j.val≤n+1 → |choleskyResidual a b ha hb n i j|<ε := by
  -- The bounded actual K controls the whole growing prefix error when replacing F by N*B.
  intro ε hε
  obtain ⟨C,hC,hK⟩ := twoEdgeTransformation_bounded a b ha hb
  let δ : ℝ := ε/(2*(1+C))
  have hδ : 0<δ := by dsimp [δ]; positivity
  obtain ⟨NR,hR⟩ := twoEdgeModelResidual_uniform a b ha hb (ε/2) (by positivity)
  obtain ⟨NG,hG⟩ := gramPerturbation_uniform ha hb δ hδ
  refine ⟨max NR NG,fun n hn i j hi hj => ?_⟩
  let E := fun k l:Fin (n+1) => ((n:ℝ)+1)*gramPerturbation a b ha hb n k l-twoEdgeKernel a b ha hb n k l
  have hE (k l:Fin (n+1)) (hk:2*k.val≤n+1) (hl:2*l.val≤n+1) : |E k l|≤δ := by
    have hh := hG n (by omega) k l hk hl
    rw [← twoEdgeKernel_physical a b ha hb k l hk hl] at hh
    exact hh.le
  have hbefore (l:Fin i.val) : 2*(Gram.before i l).val≤n+1 := by
    have hl := l.isLt
    change 2*l.val≤n+1
    omega
  have hsum : |(∑l:Fin i.val, twoEdgeTransformation a b ha hb n i (Gram.before i l)*
      E (Gram.before i l) j)/((n:ℝ)+1)|≤C*δ := by
    rw [abs_div,abs_of_pos (by positivity : (0:ℝ)<(n:ℝ)+1)]
    apply (div_le_iff₀ (by positivity : (0:ℝ)<(n:ℝ)+1)).mpr
    calc
      _ ≤ ∑l:Fin i.val, |twoEdgeTransformation a b ha hb n i (Gram.before i l)*E (Gram.before i l) j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑_:Fin i.val, C*δ := Finset.sum_le_sum (fun l _ => by
        rw [abs_mul]
        exact mul_le_mul (hK n i (Gram.before i l)) (hE _ _ (hbefore l) hj) (abs_nonneg _) hC.le)
      _ ≤ C*δ*((n:ℝ)+1) := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
        have hv : (i.val:ℝ)≤(n:ℝ)+1 := by exact_mod_cast i.isLt.le
        exact (mul_le_mul_of_nonneg_right hv (mul_nonneg hC.le hδ.le)).trans_eq (by ring)
  have he : choleskyResidual a b ha hb n i j=twoEdgeModelResidual a b ha hb n i j+E i j+
      (∑l:Fin i.val, twoEdgeTransformation a b ha hb n i (Gram.before i l)*E (Gram.before i l) j)/((n:ℝ)+1) := by
    dsimp only [choleskyResidual,twoEdgeModelResidual,E]
    simp_rw [mul_sub,Finset.sum_sub_distrib]
    have hs : (∑l:Fin i.val, twoEdgeTransformation a b ha hb n i (Gram.before i l)*
      (((n:ℝ)+1)*gramPerturbation a b ha hb n (Gram.before i l) j))=
      ((n:ℝ)+1)*(∑l:Fin i.val, twoEdgeTransformation a b ha hb n i (Gram.before i l)*
        gramPerturbation a b ha hb n (Gram.before i l) j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      ring
    rw [hs]
    field_simp
    ring
  rw [he]
  have hR' := hR n (by omega) i j hi hj
  have hE' := hE i j hi hj
  have hδeq : δ+C*δ=ε/2 := by dsimp [δ]; field_simp
  calc
    _ ≤ |twoEdgeModelResidual a b ha hb n i j|+|E i j|+
        |(∑l:Fin i.val, twoEdgeTransformation a b ha hb n i (Gram.before i l)*
          E (Gram.before i l) j)/((n:ℝ)+1)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ < ε := by linarith

end
end jacobi.Comparison
