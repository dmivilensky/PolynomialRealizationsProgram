import jacobi.Analysis.PowerMesh
import jacobi.Analysis.CompactMesh
import jacobi.Analysis.BoundedMesh

/-!
The true inverse-power tail limit for a moving finite mesh.
An actual positive power constant gives moving summand limits. Compactness
away from zero supplies their common bound, and the existing bounded mesh
integration theorem computes the tail. No uniform asymptotic is assumed.
Use: standard Jacobi Green tails have precisely these genuine conductances.
Article: jacobi, Theorem 5.4.
Article role: positive power normalization and Riemann sums for the conductance tails.
Source: elementary real analysis: power Riemann sums and integration on a compact positive interval.
-/
namespace jacobi.Analysis
noncomputable section
open Real Set Filter MeasureTheory chebyshev1.Analysis
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- A strict upper cutoff on the unit interval is exactly the tail
integral. This identity also works when the uncut integrand is singular
at zero, since it compares the actual restricted measures directly.
Article: jacobi, Theorem 5.4.
Source: elementary real analysis: power Riemann sums and integration on a compact positive interval.
-/
theorem unit_tail_cutoff_integral (f : ℝ → ℝ) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    (∫ r in (0:ℝ)..1,if t<r then f r else 0)=∫ r in t..1,f r := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
    intervalIntegral.integral_of_le ht.2]
  change (∫ r in Ioc (0:ℝ) 1,(Ioi t).indicator f r)=_
  rw [integral_indicator measurableSet_Ioi,Measure.restrict_restrict measurableSet_Ioi]
  have hs : Ioi t ∩ Ioc (0:ℝ) 1=Ioc t 1 := by
    ext r
    simp only [mem_inter_iff,mem_Ioi,mem_Ioc]
    constructor
    · rintro ⟨hr,_,hr1⟩
      exact ⟨hr,hr1⟩
    · rintro ⟨hr,hr1⟩
      exact ⟨hr,ht.1.trans_lt hr,hr1⟩
  rw [hs]

/-- Genuine reciprocal power tails converge along every positive moving
endpoint, including an endpoint tending to one. All finite-array bounds
are consequences of the original power limit on a compact positive range.
Article: jacobi, Theorem 5.4.
Source: elementary real analysis: power Riemann sums and integration on a compact positive interval.
-/
theorem reciprocal_power_tail_limit (f : ℕ → ℝ) {p A : ℝ} (hA : 0<A)
    (hf : Tendsto (fun k : ℕ => f k/(k:ℝ)^p) atTop (𝓝 A))
    (n m : ℕ → ℕ) {t : ℝ} (ht : t∈Ioc (0:ℝ) 1)
    (hn : Tendsto n atTop atTop)
    (hm : Tendsto (fun i => (m i:ℝ)/(n i:ℝ)) atTop (𝓝 t)) :
    Tendsto (fun i => (∑ j∈Finset.range (n i),if m i≤j then (n i:ℝ)^p/f j else 0)/(n i:ℝ))
      atTop (𝓝 (∫ s in t..1,1/(A*s^p))) := by
  let g : ℝ → ℝ := fun s => 1/(A*s^p)
  have hc : ∀ s∈Icc (t/2) 1,ContinuousAt g s := by
    intro s hs
    have hs0 : 0<s := lt_of_lt_of_le (by linarith [ht.1] : 0<t/2) hs.1
    have hpow : ContinuousAt (fun x : ℝ => x^p) s :=
      continuousAt_id.rpow_const (Or.inl hs0.ne')
    exact continuousAt_const.div (continuousAt_const.mul hpow)
      (mul_pos hA (rpow_pos_of_pos hs0 p)).ne'
  obtain ⟨B,hB,N,hbound⟩ := compact_mesh_bound (fun N j => (N:ℝ)^p/f j) g (t/2) 1 hc
    (fun ns ms s hs hns hms => reciprocal_power_mesh_limit f hA.ne' hf
      (lt_of_lt_of_le (by linarith [ht.1] : 0<t/2) hs.1) hns hms)
  let a (i j : ℕ) := if m i≤j ∧ j<n i then (n i:ℝ)^p/f j else 0
  have hb : ∀ᶠ i in atTop,∀ j,|a i j|≤B := by
    filter_upwards [hn.eventually_ge_atTop N,hn.eventually_gt_atTop 0,
      hm.eventually (Ioi_mem_nhds (by linarith [ht.1] : t/2<t))] with i hi hni hmi
    intro j
    by_cases hj : m i≤j ∧ j<n i
    · change |(if m i≤j ∧ j<n i then (n i:ℝ)^p/f j else 0)|≤B
      rw [ite_eq_left hj]
      have hnR : (0:ℝ)<n i := Nat.cast_pos.mpr hni
      have hlo : t/2≤(j:ℝ)/(n i:ℝ) :=
        hmi.le.trans (div_le_div_of_nonneg_right (Nat.cast_le.mpr hj.1) hnR.le)
      have hhi : (j:ℝ)/(n i:ℝ)≤1 := (div_le_one hnR).mpr (Nat.cast_le.mpr hj.2.le)
      exact hbound (n i) hi j ⟨hlo,hhi⟩
    · simp only [a,ite_eq_right hj,abs_zero]
      exact hB.le
  have hp : ∀ᵐ s ∂volume.restrict (Ioo (0:ℝ) 1),
      Tendsto (fun i => a i (Nat.floor ((n i:ℝ)*s))) atTop (𝓝 (if t<s then g s else 0)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,ae_restrict_of_ae (volume.ae_ne t)] with s hs hst
    let j i := Nat.floor ((n i:ℝ)*s)
    have hj := floor_mesh_limit hn (tendsto_const_nhds (x := s))
      (Eventually.of_forall (fun _ => hs.1.le))
    have hjN : ∀ᶠ i in atTop,j i<n i := by
      filter_upwards [hj.eventually (Iio_mem_nhds hs.2),hn.eventually_gt_atTop 0] with i hi hni
      exact_mod_cast (div_lt_one (Nat.cast_pos.mpr hni)).mp hi
    by_cases hts : t<s
    · simp only [ite_eq_left hts]
      apply (reciprocal_power_mesh_limit f hA.ne' hf hs.1 hn hj).congr'
      filter_upwards [hm.eventually_lt hj hts,hjN,hn.eventually_gt_atTop 0] with i hi hjn hni
      have hmj : m i≤j i := by
        exact_mod_cast ((div_lt_div_iff_of_pos_right (Nat.cast_pos.mpr hni)).mp hi).le
      change (n i:ℝ)^p/f (j i)=(if m i≤j i ∧ j i<n i then (n i:ℝ)^p/f (j i) else 0)
      rw [ite_eq_left ⟨hmj,hjn⟩]
    · simp only [ite_eq_right hts]
      have hst' : s<t := lt_of_le_of_ne (le_of_not_gt hts) hst
      apply tendsto_const_nhds.congr'
      filter_upwards [hj.eventually_lt hm hst',hn.eventually_gt_atTop 0] with i hi hni
      have hjm : ¬m i≤j i := by
        have h : (j i:ℝ)<m i := (div_lt_div_iff_of_pos_right (Nat.cast_pos.mpr hni)).mp hi
        exact_mod_cast h.not_ge
      change (0:ℝ)=(if m i≤j i ∧ j i<n i then (n i:ℝ)^p/f (j i) else 0)
      simp [hjm]
  have h := bounded_mesh_limit n a (fun s => if t<s then g s else 0) hn hb hp
  rw [unit_tail_cutoff_integral g ⟨ht.1.le,ht.2⟩] at h
  apply h.congr
  intro i
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  simp only [a,Finset.mem_range.mp hj,and_true]

end
end jacobi.Analysis
