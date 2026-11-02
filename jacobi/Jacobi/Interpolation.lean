import jacobi.Jacobi.HalfInterpolation

/-!
Article: jacobi, Proposition B.1.
The true first-half theorem is applied to both parameter orders. Exact
reflection sends every remaining original node segment to a first-half
segment, sends theta to pi-theta, and preserves its sine. The theorem
uses the physical angle interval [0,pi], implicit in the source's
inverse affine cosine coordinate.
Use: completes Proposition B.1 (d) and supplies the interpolation geometry for the later finite support-chain limit.
-/
namespace jacobi.Jacobi
noncomputable section
open Real Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual original finite Jacobi interpolation segments satisfy the complete uniform two-edge sine estimate, including every small index.
Use: completes Proposition B.1 (d) and supplies the interpolation geometry for the later finite support-chain limit.
Article: jacobi, Proposition B.1.
Proof: the first half uses the proved positive true shifted endpoint
margins. Every other original index reverses to a first-half index for
the exchanged parameters. The model scale is symmetric, the shift is
antisymmetric, and both actual and model nodes negate under reflection.
Thus theta maps to pi-theta, preserving sine and the nearer-edge index.
Taking the minimum lower constant and maximum upper constant covers all
original finite nodes with one common eventual degree threshold. -/
theorem zeros_interpolation {a b : ℝ} (ha : -1<a) (hb : -1<b) :
    ∃ c C : ℝ,0<c ∧ 0<C ∧ ∀ᶠ n : ℕ in atTop,0<n ∧ ∀ i : Fin n,
      ∀ theta : ℝ,theta ∈ Icc 0 Real.pi →
      modelScale a b n*cos theta+modelShift a b n ∈
        uIcc (modelNode a b n i.val) ((nodes a b ha hb n).value i) →
      c*(edgeIndex n i.val:ℝ)/(n:ℝ)≤sin theta ∧
        sin theta≤C*(edgeIndex n i.val:ℝ)/(n:ℝ) := by
  -- Reflection acts on the genuine original sorted node list, so there is no change of enumeration or independently chosen spectral family.
  obtain ⟨ca,Ca,hca,hCa,hA⟩ := firstHalf_interpolation ha hb
  obtain ⟨cb,Cb,hcb,hCb,hB⟩ := firstHalf_interpolation hb ha
  refine ⟨min ca cb,max Ca Cb,lt_min hca hcb,lt_of_lt_of_le hCa (le_max_left _ _),?_⟩
  filter_upwards [hA,hB] with n hAn hBn
  refine ⟨hAn.1,?_⟩
  intro i theta htheta hinterp
  have hnR : (0:ℝ)<n := by exact_mod_cast hAn.1
  by_cases hi : 2*i.val<n
  · have hweight : edgeIndex n i.val=i.val+1 := by dsimp [edgeIndex]; omega
    have h := hAn.2 i.val hi theta htheta (by
      rwa [finiteAngleAt_eq ha hb i.isLt,(angle_properties ha hb i).2])
    rw [hweight,Nat.cast_add,Nat.cast_one]
    exact ⟨(div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_left ca cb) (by positivity)) hnR.le).trans h.1,
      h.2.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left Ca Cb) (by positivity)) hnR.le)⟩
  · let j := i.rev
    have hj : 2*j.val<n := by dsimp [j,Fin.rev]; omega
    have hweight : edgeIndex n i.val=j.val+1 := by dsimp [edgeIndex,j,Fin.rev]; omega
    have href : (nodes a b ha hb n).value i= -(nodes b a hb ha n).value j := by
      simpa only [j,Fin.rev_rev] using nodes_reflection ha hb j
    have hmodel : modelNode a b n i.val= -modelNode b a n j.val := by
      have h := modelNode_reflection ha hb j.isLt
      rwa [show n-1-j.val=i.val by dsimp [j,Fin.rev]; omega] at h
    have hfreq : frequency b a n=frequency a b n := by unfold frequency; ring
    have hsc : modelScale b a n=modelScale a b n := by unfold modelScale; rw [hfreq]; ring
    have hsh : modelShift b a n= -modelShift a b n := by unfold modelShift; rw [hfreq]; ring
    have hangle : Real.pi-theta ∈ Icc 0 Real.pi := by constructor <;> linarith [htheta.1,htheta.2]
    have hcoord : modelScale b a n*cos (Real.pi-theta)+modelShift b a n=
        -(modelScale a b n*cos theta+modelShift a b n) := by rw [hsc,hsh,Real.cos_pi_sub]; ring
    have hsegment : modelScale b a n*cos (Real.pi-theta)+modelShift b a n ∈
        uIcc (modelNode b a n j.val) (cos (finiteAngleAt b a hb ha n j.val)) := by
      rw [hcoord,finiteAngleAt_eq hb ha j.isLt,(angle_properties hb ha j).2]
      rw [hmodel,href] at hinterp
      rcases mem_uIcc.mp hinterp with h | h
      · exact mem_uIcc_of_ge (by linarith [h.2]) (by linarith [h.1])
      · exact mem_uIcc_of_le (by linarith [h.2]) (by linarith [h.1])
    have h := hBn.2 j.val hj (Real.pi-theta) hangle hsegment
    rw [Real.sin_pi_sub] at h
    rw [hweight,Nat.cast_add,Nat.cast_one]
    exact ⟨(div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_right ca cb) (by positivity)) hnR.le).trans h.1,
      h.2.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right Ca Cb) (by positivity)) hnR.le)⟩

end
end jacobi.Jacobi
