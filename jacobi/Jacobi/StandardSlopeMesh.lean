import jacobi.Jacobi.StandardBounds
import jacobi.Analysis.RealDoubleMesh

/-!
The true triangular Green-pair mesh for the standard flow's initial slope.
The proved global Green bound controls the full double mesh. Moving kernel
limits and the strict physical cutoff determine its almost-everywhere
limit, and the existing dominated integration theorem evaluates the sum.
Use: StandardSlope identifies the actual finite energy derivative with
this same mesh, before evaluating its continuum integral exactly.
Article: jacobi, Theorem 5.6, proof using Equation (5.12).
Article role: the limit of the actual initial finite-matrix energy derivative.
-/
namespace jacobi.Jacobi
noncomputable section
open Real Set Filter MeasureTheory jacobi.Analysis chebyshev1.Analysis
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The dimension-normalized summand of the actual energy derivative.
Article: jacobi, Theorem 5.6, proof using Equation (5.12).
-/
def standardSlopeSummand (a b : ℝ) (N i j : ℕ) : ℝ :=
  if j < i then 4*(standardGreenTail a b N i i/(N:ℝ)-standardGreenTail a b N j j/(N:ℝ))*
    (standardGreenTail a b N i j/(N:ℝ))^2 else 0

/-- The genuine continuum integral of the initial Green-pair derivative.
Article: jacobi, Theorem 5.6, proof using Equation (5.12).
-/
def standardSlopeIntegral (a : ℝ) : ℝ :=
  ∫ t in (0:ℝ)..1,∫ u in (0:ℝ)..1,if u<t then
    4*(standardLimitKernel a t t-standardLimitKernel a u u)*(standardLimitKernel a t u)^2 else 0

/-- Every finite slope summand has the same genuine absolute bound,
including the small-index corner and the zero-extended terminal rows.
Article: jacobi, Theorem 5.6, proof using Equation (5.12).
-/
theorem standardSlopeSummand_bound {a b : ℝ} (ha : -(1/2:ℝ)<a) (hb : -1<b) :
    ∃ B : ℝ,0<B ∧ ∀ N i j : ℕ,|standardSlopeSummand a b N i j|≤B := by
  obtain ⟨K,hK,hbound⟩ := standardGreenTail_normalized_bound ha hb
  refine ⟨8*K^3,by positivity,fun N i j => ?_⟩
  unfold standardSlopeSummand
  split_ifs
  · rw [abs_mul,abs_mul,abs_of_nonneg (show (0:ℝ)≤4 by norm_num),abs_of_nonneg (sq_nonneg (standardGreenTail a b N i j/(N:ℝ)))]
    have hd : |standardGreenTail a b N i i/(N:ℝ)-standardGreenTail a b N j j/(N:ℝ)|≤2*K :=
      ((abs_sub _ _).trans (add_le_add (hbound N i i) (hbound N j j))).trans_eq (by ring)
    have hs : (standardGreenTail a b N i j/(N:ℝ))^2≤K^2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hbound N i j) 2
    exact (mul_le_mul (mul_le_mul_of_nonneg_left hd (by norm_num)) hs
      (sq_nonneg _) (by positivity)).trans_eq (by ring)
  · simpa only [abs_zero] using (show (0:ℝ)≤8*K^3 by positivity)

/-- Every moving physical pair off the diagonal has the correct actual
triangular slope limit. Its index cutoff stabilizes by strict separation.
Article: jacobi, Theorem 5.6, proof using Equation (5.12).
-/
theorem standardSlopeSummand_mesh_limit {a b : ℝ} (ha : -1<a) (hb : -1<b)
    (n i j : ℕ → ℕ) {s t : ℝ} (hs : s∈Ioc (0:ℝ) 1) (ht : t∈Ioc (0:ℝ) 1) (hne : s≠t)
    (hn : Tendsto n atTop atTop)
    (hi : Tendsto (fun k => (i k:ℝ)/(n k:ℝ)) atTop (𝓝 s))
    (hj : Tendsto (fun k => (j k:ℝ)/(n k:ℝ)) atTop (𝓝 t)) :
    Tendsto (fun k => standardSlopeSummand a b (n k) (i k) (j k)) atTop
      (𝓝 (if t<s then 4*(standardLimitKernel a s s-standardLimitKernel a t t)*
        (standardLimitKernel a s t)^2 else 0)) := by
  by_cases hts : t<s
  · rw [ite_eq_left hts]
    have h1 := standardGreenTail_mesh_limit ha hb n i i hs hs hn hi hi
    have h2 := standardGreenTail_mesh_limit ha hb n j j ht ht hn hj hj
    have h3 := standardGreenTail_mesh_limit ha hb n i j hs ht hn hi hj
    have h := ((h1.sub h2).mul (h3.pow 2)).const_mul 4
    have hconst : 4*((standardLimitKernel a s s-standardLimitKernel a t t)*
        (standardLimitKernel a s t)^2)=4*(standardLimitKernel a s s-standardLimitKernel a t t)*
          (standardLimitKernel a s t)^2 := by ring
    rw [hconst] at h
    apply h.congr'
    filter_upwards [hj.eventually_lt hi hts,hn.eventually_gt_atTop 0] with k hk hnk
    have hij : j k < i k := by
      exact_mod_cast (div_lt_div_iff_of_pos_right (Nat.cast_pos.mpr hnk)).mp hk
    rw [standardSlopeSummand,ite_eq_left hij]
    ring
  · rw [ite_eq_right hts]
    have hst : s<t := lt_of_le_of_ne (le_of_not_gt hts) hne
    apply tendsto_const_nhds.congr'
    filter_upwards [hi.eventually_lt hj hst,hn.eventually_gt_atTop 0] with k hk hnk
    have hij : ¬j k < i k := by
      have h : (i k:ℝ)<j k := (div_lt_div_iff_of_pos_right (Nat.cast_pos.mpr hnk)).mp hk
      exact_mod_cast h.not_gt
    simp [standardSlopeSummand,hij]

/-- The whole actual initial-slope pair mesh converges to its true
continuum integral. No auxiliary uniform corner estimate, quadrature
certificate or chosen sequence of interior indices is assumed.
Article: jacobi, Theorem 5.6, proof using Equation (5.12).
-/
theorem standardSlope_mesh_integral_limit {a b : ℝ} (ha : -(1/2:ℝ)<a) (hb : -1<b) :
    Tendsto (fun N : ℕ => (∑ i∈Finset.range N,∑ j∈Finset.range N,
      standardSlopeSummand a b N i j)/(N:ℝ)^2) atTop (𝓝 (standardSlopeIntegral a)) := by
  obtain ⟨B,_,hB⟩ := standardSlopeSummand_bound ha hb
  apply bounded_real_double_mesh_limit id (standardSlopeSummand a b)
    (fun t u => if u<t then 4*(standardLimitKernel a t t-standardLimitKernel a u u)*
      (standardLimitKernel a t u)^2 else 0) tendsto_id (Eventually.of_forall hB)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  filter_upwards [ae_restrict_mem measurableSet_Ioo,ae_restrict_of_ae (volume.ae_ne t)] with u hu hut
  have hmt := floor_mesh_limit (tendsto_id : Tendsto (id : ℕ → ℕ) atTop atTop)
    (tendsto_const_nhds (x := t)) (Eventually.of_forall (fun _ => ht.1.le))
  have hmu := floor_mesh_limit (tendsto_id : Tendsto (id : ℕ → ℕ) atTop atTop)
    (tendsto_const_nhds (x := u)) (Eventually.of_forall (fun _ => hu.1.le))
  exact standardSlopeSummand_mesh_limit (by linarith : -1<a) hb id
    (fun N => Nat.floor ((N:ℝ)*t)) (fun N => Nat.floor ((N:ℝ)*u))
    ⟨ht.1,ht.2.le⟩ ⟨hu.1,hu.2.le⟩ hut.symm tendsto_id hmt hmu

end
end jacobi.Jacobi
