import jacobi.Analytic.FiniteShiftedL1
import jacobi.Analytic.ShiftedMatrixIdentity

/-!
Article: jacobi, Appendix C.6 (uniform shifted spectral convergence).
The original finite shifted spectra retain their common unshifted
spectral majorant on compact slit sets. At every admissible real shift,
the actual finite spectral point eventually lies strictly above every
original Jacobi node, uniformly over the entire genuine finite fibre.
Use: Lemma specw and the real-shift packing reduction use genuine finite shifted spectra with no extra summability or pole premise.
-/
namespace jacobi.EdgeResolvent
noncomputable section
open Real Set Filter
open scoped Topology

/-- The actual finite shifted spectral coefficients have the complete
original compact majorant by the same unshifted positive Jacobi spectrum.
Use: Lemma specw and the real-shift packing reduction use genuine
finite shifted spectra with no extra summability or pole premise.
Article: jacobi, Appendix C.6 (uniform shifted spectral convergence).
Proof: use the exact genuine resolvent transform and the proved common
compact inverse-denominator bound at every actual finite mode. -/
theorem finiteShiftedEdge_compact_bound {a b:ℝ} (ha:-1<a) (hb:-1<b)
    {W:Set ℂ} (hW:IsCompact W) (hsub:W⊆edgeDomain a ha) :
    ∃C:ℝ,0<C ∧ ∀ᶠn:ℕ in atTop,∀k:ℕ,∀w∈W,
      ‖finiteShiftedEdge a b ha hb n k w‖≤C* jacobi.Jacobi.finiteLambdaAt a b ha hb (n+1) k := by
  obtain ⟨C,hC,hbound⟩ := finite_denominator_compact ha hb hW hsub
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with n hn k w hw
  rw [finiteShiftedEdge,resolventTransform,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (jacobi.Jacobi.finiteLambdaAt_nonneg ha hb (n+1) k)]
  exact (mul_le_mul_of_nonneg_left (hn k w hw).2.1
    (jacobi.Jacobi.finiteLambdaAt_nonneg ha hb (n+1) k)).trans_eq (mul_comm _ _)

/-- Every fixed admissible real shift eventually puts the actual
finite source spectral point strictly above all original Jacobi nodes.
Use: the real-shift finite-fibre problem has a genuinely positive
resolvent, allowing the original affine contraction and packing reduction.
Article: jacobi, Appendix C.6 (uniform shifted spectral convergence).
Proof: the actual first scaled finite spectral gap tends to sigma_1.
Its sum with the real shift is eventually positive. The exact original
finite node identity gives the true first node margin, and the original
descending node order retains that margin at every other genuine node. -/
theorem real_edgePoint_above_nodes {a b:ℝ} (ha:-1<a) (hb:-1<b)
    {w:ℝ} (hw: - jacobi.Bessel.sigma a ha 0<w) :
    ∀ᶠn:ℕ in atTop,∀k:Fin (n+1),
      (jacobi.Jacobi.nodes a b ha hb (n+1)).value k<1+w/(2*((n:ℝ)+1)^2) := by
  -- The actual first finite root is used; no independent finite positivity certificate is assumed.
  have hlim := ((jacobi.Jacobi.finiteSigmaAt_tendsto ha hb 0).comp (tendsto_add_atTop_nat 1)).add_const w
  have hpos : 0< jacobi.Bessel.sigma a ha 0+w := by linarith
  filter_upwards [hlim.eventually (Ioi_mem_nhds hpos)] with n hn k
  dsimp only [Function.comp_def] at hn
  rw [jacobi.Jacobi.finiteSigmaAt_eq ha hb (Nat.succ_pos n),
    jacobi.Jacobi.finiteSigma_node ha hb (⟨0,Nat.succ_pos n⟩:Fin (n+1))] at hn
  have hz : (⟨0,Nat.succ_pos n⟩:Fin (n+1))=0 := Fin.ext (by simp)
  rw [hz] at hn
  have hN : 0<2*((n:ℝ)+1)^2 := by positivity
  have hfirst : (jacobi.Jacobi.nodes a b ha hb (n+1)).value 0<1+w/(2*((n:ℝ)+1)^2) := by
    have hm : (jacobi.Jacobi.nodes a b ha hb (n+1)).value 0-1<w/(2*((n:ℝ)+1)^2) := by
      apply (lt_div_iff₀ hN).mpr
      push_cast at hn
      nlinarith
    linarith
  exact ((jacobi.Jacobi.nodes a b ha hb (n+1)).strictAnti.antitone (Fin.zero_le k)).trans_lt hfirst

end
end jacobi.EdgeResolvent
