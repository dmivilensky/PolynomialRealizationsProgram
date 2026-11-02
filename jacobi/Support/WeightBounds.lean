import jacobi.Support.WeightRatioBounds

/-!
Article: jacobi, Appendix C.3 (support weights and segment bounds).
The actual original support probabilities satisfy the full two-edge
uniform power bounds. Exact reflection reduces the second half to the
first. The first probability is normalized by its proved positive limit;
the full growing-index ratio is already controlled independently.
Use: supportWeight_bounds obtains the full left-edge weight estimate from the independently proved right-edge estimate, with the correct original beta exponent.
-/
namespace jacobi.Support
noncomputable section
open Real Filter jacobi.Reference
open scoped Topology

/-- The actual scalar-indexed probabilities reflect exactly under exchange of the two endpoint parameters.
Use: supportWeight_bounds obtains the full left-edge weight estimate from the independently proved right-edge estimate, with the correct original beta exponent.
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Proof: both scalar indices lie in the true finite dimension. Their finite representatives are exchanged by Fin.rev, so the existing actual spectral-measure reflection theorem applies. -/
theorem naturalWeight_reflection {a b:ℝ} (ha:-1<a) (hb:-1<b) {n k:ℕ} (hk:k≤n) :
    naturalWeight a b ha hb n (n-k)=naturalWeight b a hb ha n k := by
  simp only [naturalWeight,dite_eq_left (show n-k<n+1 by omega),dite_eq_left (show k<n+1 by omega)]
  have hi : (⟨n-k,show n-k<n+1 by omega⟩:Fin (n+1))=(⟨k,show k<n+1 by omega⟩:Fin (n+1)).rev := by
    apply Fin.ext
    simp only [Fin.val_rev]
    omega
  rw [hi]
  exact naturalMeasure_weight_reflection a b ha hb n _

/-- The actual original right-edge probabilities satisfy the full uniform power bounds in the degree normalization.
Use: supportWeight_bounds transfers the same quantitative result to the article's true matrix-size mesh and reflects it to the opposite endpoint.
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Proof: the exact original first weight has a positive proved scaled limit, hence is uniformly bounded above and below in that scale. Multiply these actual bounds by the proved growing-index probability-ratio bounds, cancelling the same positive original first probability. -/
theorem supportWeight_half_bounds {a b:ℝ} (ha:-1<a) (hb:-1<b) :
    ∃c C:ℝ,0<c ∧ 0<C ∧ ∀ᶠn:ℕ in atTop,∀k:ℕ,2*k≤n→
      c*((k:ℝ)+1)^(2*gamma a)≤(n:ℝ)^(1+2*gamma a)*naturalWeight a b ha hb n k ∧
      (n:ℝ)^(1+2*gamma a)*naturalWeight a b ha hb n k≤C*((k:ℝ)+1)^(2*gamma a) := by
  -- The positive limiting amplitude comes from the original norming integral, not a numerical enclosure.
  obtain ⟨c,C,hc,hC,hbound⟩ := supportWeight_ratio_bounds ha hb
  let L := (topAmplitudeSquare a b*norming a 0)⁻¹
  have hL : 0<L := inv_pos.mpr (mul_pos (topAmplitudeSquare_pos ha hb) (norming_pos ha 0))
  have htop := (fixedWeight_limit ha hb 0).eventually
    (Ioo_mem_nhds (show L/2<L by linarith) (show L<2*L by linarith))
  refine ⟨c*(L/2),C*(2*L),by positivity,by positivity,?_⟩
  filter_upwards [hbound,htop] with n hn ht
  intro k hk
  have hw : 0<naturalWeight a b ha hb n 0 := by
    simp only [naturalWeight,dite_eq_left (show 0<n+1 by omega)]
    exact (naturalMeasure a b ha hb n).positive _
  have hwp : 0<naturalWeight a b ha hb n k := by
    simp only [naturalWeight,dite_eq_left (show k<n+1 by omega)]
    exact (naturalMeasure a b ha hb n).positive _
  have hlo := mul_le_mul (hn k hk).1 ht.1.le (by positivity) (div_pos hwp hw).le
  have hhi := mul_le_mul (hn k hk).2 ht.2.le
    (mul_nonneg (rpow_nonneg (Nat.cast_nonneg n) _) hw.le) (by positivity)
  have he : (naturalWeight a b ha hb n k/naturalWeight a b ha hb n 0)*
      ((n:ℝ)^(1+2*gamma a)*naturalWeight a b ha hb n 0)=
        (n:ℝ)^(1+2*gamma a)*naturalWeight a b ha hb n k := by field_simp [hw.ne']
  rw [he] at hlo hhi
  constructor
  · convert hlo using 1
    ring
  · convert hhi using 1
    ring

/-- The physical mesh weight and the positive dimension power have the exact original reciprocal normalization.
Use: supportWeight_right_bounds rewrites the proved degree-normalized probability inequalities in the article's original matrix-size notation.
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Proof: distribute the real power over the genuine nonnegative quotient, combine the two positive dimension powers and cancel the same nonzero dimension. -/
theorem weight_mesh_scale {N d:ℝ} (hN:0<N) (hd:0≤d) (g:ℝ) :
    (d/N)^(2*g)/N=d^(2*g)/N^(1+2*g) := by
  rw [div_rpow hd hN.le,rpow_add hN,rpow_one]
  ring

/-- The actual right-half support probabilities have the complete printed uniform bound with their true finite matrix size.
Use: supportWeight_bounds combines the two original endpoint exponents into the complete source assertion on every actual support node.
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Proof: the original degree and the true matrix size differ by one. Their positive powers differ by at most 2^(1+2*gamma_alpha). Use that exact comparison in the proved normalized inequalities and divide by the genuine positive matrix-size power. -/
theorem supportWeight_right_bounds {a b:ℝ} (ha:-1<a) (hb:-1<b) :
    ∃c C:ℝ,0<c ∧ 0<C ∧ ∀ᶠn:ℕ in atTop,∀k:ℕ,2*k≤n→
      c*(((k:ℝ)+1)/((n:ℝ)+1))^(2*gamma a)/((n:ℝ)+1)≤naturalWeight a b ha hb n k ∧
      naturalWeight a b ha hb n k≤C*(((k:ℝ)+1)/((n:ℝ)+1))^(2*gamma a)/((n:ℝ)+1) := by
  -- Keep the true original matrix dimension n+1 in the final mesh expression.
  obtain ⟨c,C,hc,hC,hbound⟩ := supportWeight_half_bounds ha hb
  have hg : 0<1+2*gamma a := by have := (parameter_pos ha hb).1; linarith
  refine ⟨c,(2:ℝ)^(1+2*gamma a)*C,hc,by positivity,?_⟩
  filter_upwards [hbound,eventually_ge_atTop (1:ℕ)] with n hn hn1
  intro k hk
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hn1r : (1:ℝ)≤n := by exact_mod_cast hn1
  have hN : 0<(n:ℝ)+1 := by positivity
  have hw : 0≤naturalWeight a b ha hb n k := by
    simp only [naturalWeight,dite_eq_left (show k<n+1 by omega)]
    exact ((naturalMeasure a b ha hb n).positive _).le
  have hp₀ := rpow_le_rpow hn0.le (show (n:ℝ)≤(n:ℝ)+1 by linarith) hg.le
  have hp₁ := rpow_le_rpow hN.le (show (n:ℝ)+1≤2*(n:ℝ) by linarith) hg.le
  rw [mul_rpow (by norm_num : (0:ℝ)≤2) hn0.le] at hp₁
  have hlo := (hn k hk).1.trans (mul_le_mul_of_nonneg_right hp₀ hw)
  have htwo : 0≤(2:ℝ)^(1+2*gamma a) := rpow_nonneg (by norm_num) _
  have hhi := (mul_le_mul_of_nonneg_right hp₁ hw).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hn k hk).2 htwo)
  constructor
  · have h : c*((k:ℝ)+1)^(2*gamma a)/((n:ℝ)+1)^(1+2*gamma a)≤naturalWeight a b ha hb n k :=
      (div_le_iff₀ (rpow_pos_of_pos hN (1+2*gamma a))).mpr (by nlinarith only [hlo])
    calc
      _ = c*((((k:ℝ)+1)/((n:ℝ)+1))^(2*gamma a)/((n:ℝ)+1)) := by ring
      _ = c*(((k:ℝ)+1)^(2*gamma a)/((n:ℝ)+1)^(1+2*gamma a)) := by rw [weight_mesh_scale hN (by positivity)]
      _ = c*((k:ℝ)+1)^(2*gamma a)/((n:ℝ)+1)^(1+2*gamma a) := by ring
      _ ≤ _ := h
  · have h : naturalWeight a b ha hb n k≤
        (2:ℝ)^(1+2*gamma a)*C*((k:ℝ)+1)^(2*gamma a)/((n:ℝ)+1)^(1+2*gamma a) :=
      (le_div_iff₀ (rpow_pos_of_pos hN (1+2*gamma a))).mpr (by nlinarith only [hhi])
    calc
      _ ≤ (2:ℝ)^(1+2*gamma a)*C*((k:ℝ)+1)^(2*gamma a)/((n:ℝ)+1)^(1+2*gamma a) := h
      _ = (2:ℝ)^(1+2*gamma a)*C*((((k:ℝ)+1)/((n:ℝ)+1))^(2*gamma a)/((n:ℝ)+1)) := by rw [weight_mesh_scale hN (by positivity)]; ring
      _ = _ := by ring

/-- All actual support probabilities satisfy the complete original two-edge uniform power bound, with the exponent selected by the spectral half.
Use: these genuine full spectral-tail bounds, together with the polynomial Envelope lemma, provide the summable estimates needed for the two-edge Gram limit and Theorems A–B.
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Proof: apply the proved right-half bound for the original parameters or for their exchanged pair. Exact spectral-probability reflection identifies the second case with the same original measure. The distance is the minimum of the two actual endpoint indices; choose one common lower and upper constant. -/
theorem supportWeight_bounds {a b:ℝ} (ha:-1<a) (hb:-1<b) :
    ∃c C:ℝ,0<c ∧ 0<C ∧ ∀ᶠn:ℕ in atTop,∀k:ℕ,k≤n→
      let g := if 2*k≤n then gamma a else gamma b
      let d : ℝ := (min (k+1) (n+1-k):ℕ)
      c*(d/((n:ℝ)+1))^(2*g)/((n:ℝ)+1)≤naturalWeight a b ha hb n k ∧
      naturalWeight a b ha hb n k≤C*(d/((n:ℝ)+1))^(2*g)/((n:ℝ)+1) := by
  -- The same actual finite spectral measure is used on both sides of the chain.
  obtain ⟨c₁,C₁,hc₁,hC₁,h₁⟩ := supportWeight_right_bounds ha hb
  obtain ⟨c₂,C₂,hc₂,hC₂,h₂⟩ := supportWeight_right_bounds hb ha
  refine ⟨min c₁ c₂,max C₁ C₂,lt_min hc₁ hc₂,lt_of_lt_of_le hC₁ (le_max_left _ _),?_⟩
  filter_upwards [h₁,h₂] with n hn₁ hn₂
  intro k hk
  have hN : 0<(n:ℝ)+1 := by positivity
  by_cases hright : 2*k≤n
  · have hd : min (k+1) (n+1-k)=k+1 := min_eq_left (by omega)
    simp only [ite_eq_left hright,hd,Nat.cast_add,Nat.cast_one]
    obtain ⟨hl,hu⟩ := hn₁ k hright
    exact ⟨(div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)) hN.le).trans hl,
      hu.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) hN.le)⟩
  · have hleft : 2*(n-k)≤n := by omega
    have hd : min (k+1) (n+1-k)=n+1-k := min_eq_right (by omega)
    simp only [ite_eq_right hright,hd]
    obtain ⟨hl,hu⟩ := hn₂ (n-k) hleft
    have hw : naturalWeight b a hb ha n (n-k)=naturalWeight a b ha hb n k := by
      simpa only [Nat.sub_sub_self hk] using naturalWeight_reflection hb ha hk
    have he : ((n-k:ℕ):ℝ)+1=((n+1-k:ℕ):ℝ) := by exact_mod_cast (show n-k+1=n+1-k by omega)
    rw [hw,he] at hl hu
    exact ⟨(div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)) hN.le).trans hl,
      hu.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)) hN.le)⟩

end
end jacobi.Support
