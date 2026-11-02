import jacobi.Jacobi.InterpolationCap

/-!
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Every point of each actual first-half support-to-target segment has a
genuine physical affine-cosine coordinate. Its angle lies in the support
derivative envelope interval and its sine has the proved endpoint scale.
In particular the later weighted bounds require no assumed coordinate.
Use: supportPolynomial_segment_bounds applies the actual support envelopes on the entire original segment, including its endpoints, with no independently postulated angular representation.
-/
namespace jacobi.Jacobi
noncomputable section
open Real Set Filter
open scoped Topology

/-- Every actual first-half node interpolation point has a genuine positive angular coordinate in the original derivative-envelope interval, with the original uniform sine lower bound.
Use: supportPolynomial_segment_bounds applies the actual support envelopes on the entire original segment, including its endpoints, with no independently postulated angular representation.
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Proof: the proved positive endpoint-distance margin makes the inverse affine coordinate less than one; the independent opposite margin makes it greater than minus one. Take its actual arccosine. The earlier interval cap and sine interpolation theorem supply the genuine angular bounds and exclude zero. -/
theorem firstHalf_interpolation_coordinates {a b:ℝ} (ha:-1<a) (hb:-1<b) :
    ∃c:ℝ,0<c ∧ ∀ᶠn:ℕ in atTop,0<n ∧ 0<modelScale a b n ∧ ∀k:ℕ,2*k<n→∀x:ℝ,
      x∈uIcc (modelNode a b n k) (cos (finiteAngleAt a b ha hb n k))→
      ∃theta:ℝ,theta∈Ioo 0 (3*π/4) ∧ x=modelScale a b n*cos theta+modelShift a b n ∧
        c*(k+1:ℝ)/(n:ℝ)≤sin theta := by
  -- The endpoint and opposite margins are both needed: a right-edge estimate alone does not define arccos on the full segment.
  obtain ⟨c,C,hc,hC,hsine⟩ := firstHalf_interpolation ha hb
  obtain ⟨d,D,hd,hD,hmargins⟩ := firstHalf_endpoint_margins ha hb
  refine ⟨c,hc,?_⟩
  filter_upwards [hsine,hmargins,firstHalf_interpolation_opposite ha hb,
    firstHalf_interpolation_cap ha hb] with n hn hm ho hcap
  refine ⟨hn.1,hcap.1,?_⟩
  intro k hk x hx
  let v := (x-modelShift a b n)/modelScale a b n
  have hvlo : -1<v := lt_of_lt_of_le (by norm_num : (-1:ℝ)< -(15/16:ℝ)) (ho.2 k hk x hx)
  obtain ⟨hal,hau,hml,hmu⟩ := hm.2 k hk
  have hdist := interpolationDistance_bounds ha hb hm.1 ho.1.ne' ⟨hal,hau⟩ ⟨hml,hmu⟩ hx
  have hpositive : 0<d*(k+1:ℝ)^2 := mul_pos hd (sq_pos_of_pos (by positivity))
  have hvhi : v<1 := by
    have hlo := hdist.1
    change d*(k+1:ℝ)^2≤(frequency a b n)^2*(1-v) at hlo
    by_contra h
    have hz := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (frequency a b n)) (show 1-v≤0 by linarith)
    linarith
  let theta := arccos v
  have ht : theta∈Icc 0 π := ⟨arccos_nonneg _,arccos_le_pi _⟩
  have hcos : cos theta=v := cos_arccos hvlo.le hvhi.le
  have hxcoord : x=modelScale a b n*cos theta+modelShift a b n := by
    rw [hcos]
    dsimp [v]
    field_simp [hcap.1.ne']
    ring
  have hsegment : modelScale a b n*cos theta+modelShift a b n∈
      uIcc (modelNode a b n k) (cos (finiteAngleAt a b ha hb n k)) := hxcoord ▸ hx
  have hs := (hn.2 k hk theta ht hsegment).1
  have hspos : 0<sin theta := lt_of_lt_of_le
    (div_pos (mul_pos hc (by positivity)) (by exact_mod_cast hn.1)) hs
  have htpos : 0<theta := by
    by_contra h
    have he : theta=0 := le_antisymm (le_of_not_gt h) ht.1
    rw [he,sin_zero] at hspos
    exact (lt_irrefl (0:ℝ)) hspos
  exact ⟨theta,⟨htpos,hcap.2 k hk theta ht hsegment⟩,hxcoord,hs⟩

end
end jacobi.Jacobi
