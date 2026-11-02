import jacobi.Jacobi.ComparisonBoundary
import jacobi.Bessel.NumberedComparison

/-!
Article: jacobi, Proposition B.1.
The genuine finite angle list has exactly the zero-free initial and
successor intervals, with actual first-zero and successor minimality.
These discharge the zero-list hypotheses of the shared numbered Sturm theorem.
Use: the source zero prefix lies in the positive domain of the singular Sturm comparison.
-/
namespace jacobi.Jacobi
noncomputable section
open Real Set
set_option backward.isDefEq.respectTransparency false

/-- Every valid actual Jacobi angle is positive and strictly less than pi.
Use: the source zero prefix lies in the positive domain of the singular Sturm comparison.
Article: jacobi, Proposition B.1.
Proof: identify the padded entry with the true canonical finite angle and use its proved physical interval. -/
theorem finiteAngleAt_interval {a b : ℝ} (ha : -1<a) (hb : -1<b) {n k : ℕ} (hk : k<n) :
    finiteAngleAt a b ha hb n k∈Ioo 0 Real.pi := by
  rw [finiteAngleAt_eq ha hb hk]
  exact (angle_properties ha hb ⟨k,hk⟩).1

/-- Valid original finite Jacobi angles strictly increase with their source indices.
Use: supplies actual nodal order in both directions of the numbered zero comparison.
Article: jacobi, Proposition B.1.
Proof: the finite padded entries agree with the actual strict ordered angle list. -/
theorem finiteAngleAt_lt {a b : ℝ} (ha : -1<a) (hb : -1<b) {n i j : ℕ}
    (hij : i<j) (hj : j<n) : finiteAngleAt a b ha hb n i<finiteAngleAt a b ha hb n j := by
  rw [finiteAngleAt_eq ha hb (hij.trans hj),finiteAngleAt_eq ha hb hj]
  exact angle_strictMono ha hb n hij

/-- Every valid finite angle is a zero of the actual Jacobi Liouville wave.
Use: makes each source nodal endpoint an actual solution zero in the Sturm theorem.
Article: jacobi, Proposition B.1.
Proof: identify it with the genuine angle and use the proved original wave zero identity. -/
theorem finiteAngleAt_is_zero {a b : ℝ} (ha : -1<a) (hb : -1<b) {n k : ℕ} (hk : k<n) :
    liouville a b n (finiteAngleAt a b ha hb n k)=0 := by
  rw [finiteAngleAt_eq ha hb hk]
  exact liouville_angle_zero ha hb ⟨k,hk⟩

/-- The true first Jacobi angle is no larger than any actual positive-angle zero.
Use: discharges the source first-zero minimality in reverse Bessel/Jacobi comparison.
Article: jacobi, Proposition B.1.
Proof: the original finite zero list is exhaustive and strictly ordered. -/
theorem finiteAngleAt_first_le {a b x : ℝ} (ha : -1<a) (hb : -1<b) {n : ℕ}
    (hn : 0<n) (hx : x∈Ioo 0 Real.pi) (hz : liouville a b n x=0) :
    finiteAngleAt a b ha hb n 0≤x := by
  obtain ⟨i,hi⟩ := liouville_zero_exhaustive ha hb n hx hz
  rw [finiteAngleAt_eq ha hb hn,← hi]
  exact (angle_strictMono ha hb n).monotone (show (⟨0,hn⟩ : Fin n)≤ i from Nat.zero_le _)

/-- Every actual zero after the kth Jacobi angle is at least its true successor angle.
Use: advances reverse Sturm comparison with exactly the source's finite zero numbering.
Article: jacobi, Proposition B.1.
Proof: exhaust the actual zero by a true finite index. Any index no
larger than k contradicts the stated strict angle order; the remaining
indices are at least k+1 and monotonicity gives the successor bound. -/
theorem finiteAngleAt_successor_le {a b x : ℝ} (ha : -1<a) (hb : -1<b) {n k : ℕ}
    (hk : k+1<n) (hx : x∈Ioo 0 Real.pi) (hz : liouville a b n x=0)
    (hlt : finiteAngleAt a b ha hb n k<x) : finiteAngleAt a b ha hb n (k+1)≤x := by
  -- Completeness is used before comparing indices, so no zeros can be silently omitted.
  obtain ⟨i,hi⟩ := liouville_zero_exhaustive ha hb n hx hz
  have hk0 : k<n := by omega
  rw [finiteAngleAt_eq ha hb hk0] at hlt
  have hki : k< i.val := by
    by_contra hn
    have hh := (angle_strictMono ha hb n).monotone
      (show i≤(⟨k,hk0⟩ : Fin n) from not_lt.mp hn)
    rw [hi] at hh
    linarith
  rw [finiteAngleAt_eq ha hb hk,← hi]
  exact (angle_strictMono ha hb n).monotone (show (⟨k+1,hk⟩ : Fin n)≤ i from hki)

/-- The actual original Jacobi wave is zero-free before its true first angle.
Use: provides the first genuine nodal interval in forward singular Sturm comparison.
Article: jacobi, Proposition B.1.
Proof: any alleged earlier zero would contradict actual first-zero minimality. -/
theorem finiteAngleAt_no_zero_before {a b : ℝ} (ha : -1<a) (hb : -1<b) {n : ℕ}
    (hn : 0<n) {x : ℝ} (hx : x∈Ioo 0 (finiteAngleAt a b ha hb n 0)) :
    liouville a b n x≠0 := by
  intro hz
  have hxp : x∈Ioo 0 Real.pi := ⟨hx.1,hx.2.trans (finiteAngleAt_interval ha hb hn).2⟩
  exact not_lt_of_ge (finiteAngleAt_first_le ha hb hn hxp hz) hx.2

/-- The actual Jacobi wave has no zero between any consecutive true finite angles.
Use: supplies every original nodal interval in the numbered Sturm induction.
Article: jacobi, Proposition B.1.
Proof: an alleged intermediate actual zero must lie at or beyond the
true successor by its proved minimality, contradicting the interval's upper bound. -/
theorem finiteAngleAt_no_zero_between {a b : ℝ} (ha : -1<a) (hb : -1<b) {n k : ℕ}
    (hk : k+1<n) {x : ℝ}
    (hx : x∈Ioo (finiteAngleAt a b ha hb n k) (finiteAngleAt a b ha hb n (k+1))) :
    liouville a b n x≠0 := by
  intro hz
  have hxp : x∈Ioo 0 Real.pi :=
    ⟨(finiteAngleAt_interval ha hb (show k<n by omega)).1.trans hx.1,
      hx.2.trans (finiteAngleAt_interval ha hb hk).2⟩
  exact not_lt_of_ge (finiteAngleAt_successor_le ha hb hk hxp hz hx.1) hx.2

end
end jacobi.Jacobi
