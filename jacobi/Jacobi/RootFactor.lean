import jacobi.Jacobi.WeightedPositivity
import Mathlib.Topology.Order.IntermediateValue

/-!
Article: jacobi, Proposition A.1.
Separate the actual real roots in the open Jacobi interval, preserving
their multiplicities. The remaining polynomial has no zero there and
therefore has constant sign. This supplies the standard sign-correcting
test for the full polynomial orthogonality theorem.
Source: the classical real orthogonal-polynomial zero-location argument.
Use: determines the sign of the root-free factor in the Jacobi zero-location argument.
-/
namespace jacobi.Jacobi
noncomputable section
open Polynomial Set MeasureTheory
set_option backward.isDefEq.respectTransparency false

/-- A continuous zero-free real function with positive midpoint is positive throughout the open unit interval.
Use: determines the sign of the root-free factor in the Jacobi zero-location argument.
Article: jacobi, Proposition A.1.
Proof: any negative value would have a zero between it and the positive
midpoint. The entire joining interval stays inside (0,1). -/
theorem positive_on_unit_of_no_zero {f : ℝ → ℝ} (hf : Continuous f)
    (hne : ∀ t∈Ioo (0:ℝ) 1,f t≠0) (hmid : 0<f (1/2)) : ∀ t∈Ioo (0:ℝ) 1,0<f t := by
  -- The intermediate value theorem works regardless of the point's side of the midpoint.
  intro t ht
  by_contra hn
  have hz : (0:ℝ)∈uIcc (f t) (f (1/2)) := Icc_subset_uIcc ⟨le_of_not_gt hn,hmid.le⟩
  obtain ⟨z,hzmem,hzero⟩ := intermediate_value_uIcc hf.continuousOn hz
  exact hne z (ordConnected_Ioo.uIcc_subset ht (show (1/2:ℝ)∈Ioo 0 1 by norm_num) hzmem) hzero

/-- A polynomial without a zero on (0,1) has one strict sign there.
Use: constructs a sign-correcting polynomial test for the actual Jacobi weight.
Article: jacobi, Proposition A.1.
Proof: its midpoint value is nonzero. Apply the positive midpoint
argument either to the actual polynomial or to its negative. -/
theorem polynomial_fixed_sign {p : Polynomial ℝ} (hne : ∀ t∈Ioo (0:ℝ) 1,p.eval t≠0) :
    (∀ t∈Ioo (0:ℝ) 1,0<p.eval t) ∨ (∀ t∈Ioo (0:ℝ) 1,p.eval t<0) := by
  by_cases hp : 0<p.eval (1/2)
  · exact Or.inl (positive_on_unit_of_no_zero p.continuous hne hp)
  · have hneg : 0< -p.eval (1/2) := neg_pos.mpr
      (lt_of_le_of_ne (le_of_not_gt hp) (hne (1/2) (by norm_num)))
    have h := positive_on_unit_of_no_zero p.continuous.neg
      (fun t ht => neg_ne_zero.mpr (hne t ht)) hneg
    exact Or.inr (fun t ht => neg_pos.mp (h t ht))

/-- A nonzero polynomial paired with its interval-root factor has nonzero actual Jacobi-weight integral when the remaining factor has no interior zero.
Use: a lower-degree interval-root factor contradicts the complete Jacobi orthogonality theorem.
Article: jacobi, Proposition A.1.
Proof: write p=q*r. Then p*q=q^2*r has the constant sign of r on
the interior and is a nonzero polynomial. Apply the proved strict
weighted positivity theorem to p*q or its negative. -/
theorem root_factor_pairing_ne_zero {a b : ℝ} (ha : -1<a) (hb : -1<b)
    {p q r : Polynomial ℝ} (hp : p≠0) (hq : q≠0) (he : p=q*r)
    (hr : ∀ t∈Ioo (0:ℝ) 1,r.eval t≠0) :
    (∫ t in (0:ℝ)..1,weight a b t*(p.eval t*q.eval t))≠0 := by
  -- The sign is proved for the genuine polynomial product on the whole integration interior.
  rcases polynomial_fixed_sign hr with hpos | hneg
  · have hnon : ∀ t∈Ioo (0:ℝ) 1,0≤(p*q).eval t := by
      intro t ht
      rw [he,eval_mul,eval_mul]
      nlinarith [mul_nonneg (sq_nonneg (q.eval t)) (hpos t ht).le]
    have h := weighted_polynomial_integral_pos ha hb (mul_ne_zero hp hq) hnon
    simpa only [eval_mul] using h.ne'
  · have hnon : ∀ t∈Ioo (0:ℝ) 1,0≤(-(p*q)).eval t := by
      intro t ht
      rw [eval_neg,he,eval_mul,eval_mul]
      nlinarith [mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (q.eval t)) (hneg t ht).le]
    have h := weighted_polynomial_integral_pos ha hb (neg_ne_zero.mpr (mul_ne_zero hp hq)) hnon
    simp only [eval_neg,eval_mul,mul_neg,intervalIntegral.integral_neg] at h
    exact neg_ne_zero.mp h.ne'

/-- Every nonzero real polynomial factors into its full multiset of interior roots and an interior-zero-free remainder.
Use: complete orthogonality forces the actual Jacobi interior-root factor to have full degree.
Article: jacobi, Proposition A.1.
Proof: the product over the filtered root multiset divides the original
polynomial by the community root-multiset divisibility theorem. Roots of
the product are exactly that multiset. Root multiplicity addition then
excludes any further interior root of the remainder. -/
theorem factor_interior_roots {p : Polynomial ℝ} (hp : p≠0) :
    ∃ q r : Polynomial ℝ,p=q*r ∧ q≠0 ∧ r≠0 ∧
      q.natDegree=(p.roots.filter (fun t => t∈Ioo (0:ℝ) 1)).card ∧
      ∀ t∈Ioo (0:ℝ) 1,r.eval t≠0 := by
  classical
  -- The finite factor contains every interior multiplicity, so no sign-changing root can remain.
  let S := p.roots.filter (fun t => t∈Ioo (0:ℝ) 1)
  let q : Polynomial ℝ := (S.map (fun t => X-C t)).prod
  have hq : q≠0 := (monic_multisetProd_X_sub_C S).ne_zero
  have hdiv : q∣p := (Multiset.prod_X_sub_C_dvd_iff_le_roots hp S).mpr (Multiset.filter_le _ _)
  obtain ⟨r,he⟩ := hdiv
  have hr : r≠0 := right_ne_zero_of_mul (he ▸ hp)
  refine ⟨q,r,he,hq,hr,natDegree_multiset_prod_X_sub_C_eq_card S,?_⟩
  have hroots : p.roots=S+r.roots := by rw [he,roots_mul (mul_ne_zero hq hr),roots_multiset_prod_X_sub_C]
  intro t ht hzero
  have hc := congrArg (Multiset.count t) hroots
  have hfilter : S.count t=p.roots.count t := Multiset.count_filter_of_pos ht
  rw [Multiset.count_add,hfilter] at hc
  have hpos : 0<r.roots.count t := Multiset.count_pos.mpr ((mem_roots hr).mpr hzero)
  omega

end
end jacobi.Jacobi
