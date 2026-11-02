import jacobi.Jacobi.Zeros

/-!
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
The actual original target-to-support node displacement, multiplied by
the full weighted derivative scale N^2/hat_d, has a uniform inverse-square
edge plus inverse-square matrix-size bound. It is derived from the full
proved Proposition B.1, with the original frequency comparison.
Use: supportGram_node_error bounds the original T_k'' summand in Appendix C.4, without assuming a separate scaled-node-error certificate.
-/
namespace jacobi.Comparison
noncomputable section
open Real Filter jacobi.Jacobi
open scoped Topology

/-- The actual spectral displacement at the weighted polynomial derivative scale has the complete summable two-edge error needed by the original Gram comparison.
Use: supportGram_node_error bounds the original T_k'' summand in Appendix C.4, without assuming a separate scaled-node-error certificate.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Proof: apply the full original two-edge node error. The true matrix size is at most twice its actual frequency, and every original edge index is at least one. The two resulting terms are bounded by 4/d^2 and 16/N^2 respectively; absorb both into a common positive constant. -/
theorem scaledNodeDisplacement_bound {a b:ℝ} (ha:-1<a) (hb:-1<b) :
    ∃C:ℝ,0<C ∧ ∀ᶠn:ℕ in atTop,∀k:Fin (n+1),
      ((n:ℝ)+1)^2/(edgeIndex (n+1) k.val:ℝ)*
        |(nodes a b ha hb (n+1)).value k-modelNode a b (n+1) k.val|≤
        C*(1/(edgeIndex (n+1) k.val:ℝ)^2+1/((n:ℝ)+1)^2) := by
  -- The original actual node error and frequency remain paired at the same genuine finite dimension.
  obtain ⟨C,hC,hbound⟩ := zeros_node_error ha hb
  refine ⟨16*C,by positivity,?_⟩
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hbound,
    (tendsto_add_atTop_nat 1).eventually (frequency_degree_comparison a b)] with n hn hf
  intro k
  let N : ℝ := (n:ℝ)+1
  let F := frequency a b (n+1)
  let d : ℝ := edgeIndex (n+1) k.val
  have hN : 0<N := by dsimp [N]; positivity
  have hF : 0<F := hf.1
  have hd : 1≤d := by dsimp [d,edgeIndex]; exact_mod_cast (show 1≤min (k.val+1) (n+1-k.val) by omega)
  have hd0 : 0<d := by linarith
  have hNF : N≤2*F := by simpa only [N,Nat.cast_add,Nat.cast_one] using hf.2.1
  have hsq : N^2≤4*F^2 := by nlinarith
  have h₁ : N^2/d*(1/(F^2*d^2))≤4/d^2 := by
    have he : N^2/d*(1/(F^2*d^2))=N^2/(F^2*d^3) := by
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    rw [he]
    apply (div_le_div_iff₀ (by positivity) (sq_pos_of_pos hd0)).mpr
    have hfd : N^2≤4*F^2*d := hsq.trans (by nlinarith [mul_le_mul_of_nonneg_left hd (show 0≤4*F^2 by positivity)])
    nlinarith only [mul_le_mul_of_nonneg_right hfd (sq_nonneg d)]
  have h₂ : N^2/d*(d/F^4)≤16/N^2 := by
    have he : N^2/d*(d/F^4)=N^2/F^4 := by field_simp [hd0.ne']
    rw [he]
    apply (div_le_div_iff₀ (by positivity) (sq_pos_of_pos hN)).mpr
    have hfour := pow_le_pow_left₀ hN.le hNF 4
    norm_num only [mul_pow] at hfour
    nlinarith only [hfour]
  have hsum : N^2/d*(1/(F^2*d^2)+d/F^4)≤16*(1/d^2+1/N^2) := by
    rw [mul_add]
    have h := add_le_add h₁ h₂
    have hp : 0≤1/d^2 := by positivity
    have he : 4/d^2+16/N^2≤16*(1/d^2+1/N^2) := by
      calc
        _ ≤ (4/d^2+16/N^2)+12*(1/d^2) := le_add_of_nonneg_right (by positivity)
        _ = _ := by ring
    exact h.trans he
  calc
    _ ≤ N^2/d*(C*(1/(F^2*d^2)+d/F^4)) := mul_le_mul_of_nonneg_left (hn.2 k) (by positivity)
    _ = C*(N^2/d*(1/(F^2*d^2)+d/F^4)) := by ring
    _ ≤ C*(16*(1/d^2+1/N^2)) := mul_le_mul_of_nonneg_left hsum hC.le
    _ = _ := by ring

end
end jacobi.Comparison
