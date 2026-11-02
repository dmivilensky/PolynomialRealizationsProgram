import jacobi.Support.WeightBounds

/-!
Article: jacobi, Appendix C.4 (target/support weight ratios).
The actual support probabilities give vanishing matrix-size-scaled mass
to the inverse-square distance from either spectral edge. Dominated
convergence replaces the source's explicit power-sum calculation: it gives
exactly the little-o error required by the printed conclusion, using the
already proved uniform support-weight bounds.
Use: right_edge_weight_mass and edge_weight_mass use positive finite sums and dominated convergence for these same original probabilities.
-/
namespace jacobi.Support
noncomputable section
open Real Finset Filter jacobi.Reference
open scoped Topology

/-- The actual zero-extended support probabilities are nonnegative at every scalar index.
Use: right_edge_weight_mass and edge_weight_mass use positive finite sums and dominated convergence for these same original probabilities.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: a valid finite index has the independently proved positive original spectral probability; outside the dimension the extension is zero. -/
theorem naturalWeight_nonneg (a b:ℝ) (ha:-1<a) (hb:-1<b) (n k:ℕ) :
    0≤naturalWeight a b ha hb n k := by
  unfold naturalWeight
  split_ifs with hk
  · exact ((naturalMeasure a b ha hb n).positive ⟨k,hk⟩).le
  · exact le_rfl

/-- The inverse-square weighted mass of the actual right spectral half is little-o of the reciprocal true matrix size.
Use: edge_weight_mass applies the same result to the reflected original parameters, obtaining the normalization error in Weight ratio(b).
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: after multiplication by the true matrix size, each fixed summand tends to zero because gamma_alpha>0. The already proved full growing-index power bound dominates every zero-extended half-row by a constant times the summable inverse-square series. Dominated convergence then gives the whole row, whose infinite sum is its literal finite sum. -/
theorem right_edge_weight_mass {a b:ℝ} (ha:-1<a) (hb:-1<b) :
    Tendsto (fun n:ℕ => ∑k:Fin (n+1),
      if 2*k.val≤n then ((n:ℝ)+1)*naturalWeight a b ha hb n k.val/((k.val:ℝ)+1)^2 else 0)
      atTop (𝓝 0) := by
  -- Keep the full growing spectral half; no fixed truncation is substituted for it.
  obtain ⟨c,C,hc,hC,hbound⟩ := supportWeight_right_bounds ha hb
  let f (n k:ℕ) : ℝ := if 2*k≤n then ((n:ℝ)+1)*naturalWeight a b ha hb n k/((k:ℝ)+1)^2 else 0
  have hg : 0<2*gamma a := by have := (parameter_pos ha hb).1; linarith
  have hn (n k:ℕ) : 0≤f n k := by
    dsimp [f]
    split_ifs
    · exact div_nonneg (mul_nonneg (by positivity) (naturalWeight_nonneg a b ha hb n k)) (sq_nonneg _)
    · exact le_rfl
  have hmajor : ∀ᶠn:ℕ in atTop,∀k:ℕ,
      f n k≤C*((((k:ℝ)+1)/((n:ℝ)+1))^(2*gamma a))/((k:ℝ)+1)^2 ∧
      f n k≤C/((k:ℝ)+1)^2 := by
    filter_upwards [hbound] with n hnb
    intro k
    by_cases hk : 2*k≤n
    · have hN : 0<(n:ℝ)+1 := by positivity
      have hdiv : 0≤((k:ℝ)+1)/((n:ℝ)+1) := by positivity
      have hdiv1 : ((k:ℝ)+1)/((n:ℝ)+1)≤1 := (div_le_one hN).mpr (by exact_mod_cast (show k+1≤n+1 by omega))
      have hp : (((k:ℝ)+1)/((n:ℝ)+1))^(2*gamma a)≤1 :=
        rpow_le_one hdiv hdiv1 hg.le
      have hw := mul_le_mul_of_nonneg_left (hnb k hk).2 hN.le
      have he : ((n:ℝ)+1)*(C*((((k:ℝ)+1)/((n:ℝ)+1))^(2*gamma a))/((n:ℝ)+1))=
          C*((((k:ℝ)+1)/((n:ℝ)+1))^(2*gamma a)) := by field_simp
      rw [he] at hw
      dsimp [f]
      rw [ite_eq_left hk]
      exact ⟨div_le_div_of_nonneg_right hw (sq_nonneg _),
        (div_le_div_of_nonneg_right hw (sq_nonneg _)).trans
          (div_le_div_of_nonneg_right (by nlinarith only [mul_le_mul_of_nonneg_left hp hC.le]) (sq_nonneg _))⟩
    · dsimp [f]
      rw [ite_eq_right hk]
      exact ⟨by positivity,by positivity⟩
  have hp (k:ℕ) : Tendsto (fun n:ℕ => f n k) atTop (𝓝 0) := by
    have hN : Tendsto (fun n:ℕ => (n:ℝ)+1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    have hr := hN.const_div_atTop ((k:ℝ)+1)
    have hpow := (hr.rpow_const (p:=2*gamma a) (Or.inr hg.le)).const_mul C
    have hzero : Tendsto (fun n:ℕ => C*((((k:ℝ)+1)/((n:ℝ)+1))^(2*gamma a))/((k:ℝ)+1)^2)
        atTop (𝓝 0) := by simpa only [zero_rpow hg.ne',mul_zero,zero_div] using hpow.div_const (((k:ℝ)+1)^2)
    exact squeeze_zero' (Eventually.of_forall (fun n => hn n k)) (hmajor.mono (fun n h => (h k).1)) hzero
  have hs : Summable (fun k:ℕ => C/((k:ℝ)+1)^2) := by
    simpa only [one_pow,mul_one_div] using (jacobi.Bessel.inverse_square_majorant_summable 1).mul_left C
  have ht := tendsto_tsum_of_dominated_convergence hs hp
    (hmajor.mono (fun n h k => by rw [Real.norm_eq_abs,abs_of_nonneg (hn n k)]; exact (h k).2))
  simp only [tsum_zero] at ht
  convert ht using 1
  funext n
  rw [tsum_eq_sum (s:=range (n+1)) (fun k hk => by
    have hk' : ¬2*k≤n := by have := not_lt.mp (show ¬k<n+1 by simpa only [mem_range] using hk); omega
    simp only [f,ite_eq_right hk']),← Fin.sum_univ_eq_sum_range]

/-- The actual complete support probability has inverse-square edge mass little-o of the reciprocal true matrix size.
Use: comparisonNormalizer_error proves the original gap-product normalizer differs from one by o(1/N), the uniform error required for the Gram limit in jacobi.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: split each original spectral index according to its closer edge. The right contribution is the proved dominated-convergence half-row. Exact probability reflection identifies the left contribution with the right half-row for the exchanged endpoint parameters. Including a possible middle term twice only increases the nonnegative bound. -/
theorem edge_weight_mass {a b:ℝ} (ha:-1<a) (hb:-1<b) :
    Tendsto (fun n:ℕ => ((n:ℝ)+1)*∑k:Fin (n+1),
      (supportMeasure a b ha hb n).weight k/(jacobi.Jacobi.edgeIndex (n+1) k.val:ℝ)^2)
      atTop (𝓝 0) := by
  -- Reflection is applied to the original measure, with its actual finite index reversal.
  let r (n:ℕ) (k:Fin (n+1)) : ℝ := if 2*k.val≤n then
    ((n:ℝ)+1)*naturalWeight a b ha hb n k.val/((k.val:ℝ)+1)^2 else 0
  let s (n:ℕ) (k:Fin (n+1)) : ℝ := if 2*k.val≤n then
    ((n:ℝ)+1)*naturalWeight b a hb ha n k.val/((k.val:ℝ)+1)^2 else 0
  have hr (n:ℕ) (k:Fin (n+1)) : 0≤r n k := by
    dsimp [r]
    split_ifs
    · exact div_nonneg (mul_nonneg (by positivity) (naturalWeight_nonneg a b ha hb n k.val)) (sq_nonneg _)
    · exact le_rfl
  have hs (n:ℕ) (k:Fin (n+1)) : 0≤s n k := by
    dsimp [s]
    split_ifs
    · exact div_nonneg (mul_nonneg (by positivity) (naturalWeight_nonneg b a hb ha n k.val)) (sq_nonneg _)
    · exact le_rfl
  have hw (n:ℕ) (k:Fin (n+1)) : naturalWeight a b ha hb n k.val=(supportMeasure a b ha hb n).weight k := by
    simp only [naturalWeight,dite_eq_left k.isLt]
    rfl
  have hpoint (n:ℕ) (k:Fin (n+1)) :
      ((n:ℝ)+1)*((supportMeasure a b ha hb n).weight k/(jacobi.Jacobi.edgeIndex (n+1) k.val:ℝ)^2)
        ≤r n k+s n k.rev := by
    by_cases hk : 2*k.val≤n
    · have hd : jacobi.Jacobi.edgeIndex (n+1) k.val=k.val+1 := by dsimp [jacobi.Jacobi.edgeIndex]; omega
      rw [hd,Nat.cast_add,Nat.cast_one]
      have he : ((n:ℝ)+1)*((supportMeasure a b ha hb n).weight k/((k.val:ℝ)+1)^2)=r n k := by
        simp only [r,ite_eq_left hk,hw]
        ring
      rw [he]
      exact le_add_of_nonneg_right (hs n k.rev)
    · have hk' : 2*k.rev.val≤n := by simp only [Fin.val_rev]; omega
      have hd : jacobi.Jacobi.edgeIndex (n+1) k.val=k.rev.val+1 := by simp only [jacobi.Jacobi.edgeIndex,Fin.val_rev]; omega
      have hw' : naturalWeight b a hb ha n k.rev.val=(supportMeasure a b ha hb n).weight k := by
        simp only [naturalWeight,dite_eq_left k.rev.isLt]
        exact supportMeasure_weight_reflection b a hb ha n k
      rw [hd,Nat.cast_add,Nat.cast_one]
      have he : ((n:ℝ)+1)*((supportMeasure a b ha hb n).weight k/((k.rev.val:ℝ)+1)^2)=s n k.rev := by
        simp only [s,ite_eq_left hk',hw']
        ring
      rw [he]
      exact le_add_of_nonneg_left (hr n k)
  have hsum (n:ℕ) : ((n:ℝ)+1)*(∑k:Fin (n+1),
      (supportMeasure a b ha hb n).weight k/(jacobi.Jacobi.edgeIndex (n+1) k.val:ℝ)^2)
      ≤(∑k,r n k)+(∑k,s n k) := by
    rw [mul_sum]
    have h := sum_le_sum (fun k (_:k∈univ) => hpoint n k)
    have hsrev : (∑k:Fin (n+1),s n k.rev)=∑k,s n k := Equiv.sum_comp Fin.revPerm (s n)
    rw [sum_add_distrib,hsrev] at h
    exact h
  have ht := (right_edge_weight_mass ha hb).add (right_edge_weight_mass hb ha)
  simp only [add_zero] at ht
  exact squeeze_zero (fun n => mul_nonneg (by positivity)
    (sum_nonneg (fun k _ => div_nonneg ((supportMeasure a b ha hb n).positive k).le (sq_nonneg _)))) hsum ht

end
end jacobi.Support
