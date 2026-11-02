import jacobi.Jacobi.CosineError

/-!
Article: jacobi, Appendix C.3 (support weights and segment bounds).
The sharp true first-half error and exact parameter/index reflection
supply the literal corrected-model estimate at every original finite
node with one common parameter-dependent constant and degree threshold.
Use: transfers the true corrected-node error and interpolation geometry to the opposite original edge.
-/
namespace jacobi.Jacobi
noncomputable section
open Real Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The original literal affine cosine-model nodes reflect exactly after parameter exchange and reverse-index reflection.
Use: transfers the true corrected-node error and interpolation geometry to the opposite original edge.
Article: jacobi, Proposition B.1.
Proof: the genuine model angles reflect to pi-x. The literal affine scale
is symmetric and its literal shift is antisymmetric under parameter exchange. -/
theorem modelNode_reflection {a b : ℝ} (ha : -1<a) (hb : -1<b) {n k : ℕ} (hk : k<n) :
    modelNode a b n (n-1-k)= -modelNode b a n k := by
  have hfreq : frequency b a n=frequency a b n := by unfold frequency; ring
  unfold modelNode
  rw [modelAngle_reflection ha hb hk,Real.cos_pi_sub]
  dsimp [modelScale,modelShift]
  rw [hfreq]
  ring

/-- The complete actual finite Jacobi spectrum satisfies the original sharp corrected-model error uniformly at both edges and all growing indices.
Use: supplies Proposition B.1 (b) and the later finite support-chain approximation for the actual original polynomial spectrum.
Article: jacobi, Proposition B.1.
Proof: apply the proved true first-half cosine error directly on the first
half. Every remaining original index reverses to a genuine first-half
index for the exchanged parameters. Exact actual-node and literal-model
reflection preserve the absolute error, and the original minimum index
weight becomes that reversed one-based index. -/
theorem zeros_node_error {a b : ℝ} (ha : -1<a) (hb : -1<b) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ n : ℕ in atTop,0<frequency a b n ∧ ∀ i : Fin n,
      |(nodes a b ha hb n).value i-modelNode a b n i.val|≤
        C*(1/((frequency a b n)^2*(edgeIndex n i.val:ℝ)^2)+(edgeIndex n i.val:ℝ)/(frequency a b n)^4) := by
  -- Both reflected estimates concern the exact original node enumerations, so the uniform minimum index weight has no missing middle case.
  obtain ⟨Ca,hCa,hA⟩ := firstHalf_node_error ha hb
  obtain ⟨Cb,hCb,hB⟩ := firstHalf_node_error hb ha
  refine ⟨max Ca Cb,lt_of_lt_of_le hCa (le_max_left _ _),?_⟩
  filter_upwards [hA,hB] with n hAn hBn
  have hfreq : frequency b a n=frequency a b n := by unfold frequency; ring
  rw [hfreq] at hBn
  refine ⟨hAn.1,?_⟩
  intro i
  by_cases hi : 2*i.val<n
  · have hweight : edgeIndex n i.val=i.val+1 := by dsimp [edgeIndex]; omega
    have h := hAn.2 i.val hi
    rw [finiteAngleAt_eq ha hb i.isLt,(angle_properties ha hb i).2] at h
    rw [hweight,Nat.cast_add,Nat.cast_one]
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left Ca Cb) (by positivity))
  · let j := i.rev
    have hj : 2*j.val<n := by dsimp [j,Fin.rev]; omega
    have hjval : j.val+1=n-i.val := by dsimp [j,Fin.rev]; omega
    have hweight : edgeIndex n i.val=j.val+1 := by dsimp [edgeIndex]; omega
    have href : (nodes a b ha hb n).value i= -(nodes b a hb ha n).value j := by
      simpa only [j,Fin.rev_rev] using nodes_reflection ha hb j
    have hmodel : modelNode a b n i.val= -modelNode b a n j.val := by
      have h := modelNode_reflection ha hb j.isLt
      rwa [show n-1-j.val=i.val by dsimp [j,Fin.rev]; omega] at h
    have h := hBn.2 j.val hj
    rw [finiteAngleAt_eq hb ha j.isLt,(angle_properties hb ha j).2] at h
    rw [href,hmodel,show -(nodes b a hb ha n).value j- -modelNode b a n j.val=
      -((nodes b a hb ha n).value j-modelNode b a n j.val) by ring,abs_neg,hweight,Nat.cast_add,Nat.cast_one]
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_right Ca Cb) (by positivity))

end
end jacobi.Jacobi
