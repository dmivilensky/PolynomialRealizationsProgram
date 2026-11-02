import jacobi.Hankel.SquaredExpansion

/-!
Article: jacobi, Lemma E.1.
Use: a single index cutoff absorbs both actual inverse-square spectral perturbation errors in the proof of Lemma E.1.
-/
namespace jacobi.Hankel
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Distinct original one-based quadratic indices have distance at least the larger zero-based index.
Use: a single index cutoff absorbs both actual inverse-square spectral perturbation errors in the proof of Lemma E.1.
Article: jacobi, Lemma E.1.
Proof: factor the genuine squared difference; the distinct integer index difference has absolute value at least one, and the sum factor exceeds either index. -/
theorem quadratic_index_gap_lower {k l : ℕ} (hkl : k≠l) :
    max (k:ℝ) (l:ℝ)≤|(l+1:ℝ)^2-(k+1:ℝ)^2| := by
  -- Both integer signs are handled before the actual quadratic factorization is used.
  have hdiff : 1≤|(l:ℝ)-(k:ℝ)| := by
    rcases lt_or_gt_of_ne hkl with h | h
    · have hh : (k:ℝ)+1≤(l:ℝ) := by exact_mod_cast Nat.add_one_le_iff.mpr h
      rw [abs_of_nonneg (by linarith : (0:ℝ)≤(l:ℝ)-(k:ℝ))]
      linarith
    · have hh : (l:ℝ)+1≤(k:ℝ) := by exact_mod_cast Nat.add_one_le_iff.mpr h
      rw [abs_of_nonpos (by linarith : (l:ℝ)-(k:ℝ)≤0)]
      linarith
  have he : |(l+1:ℝ)^2-(k+1:ℝ)^2|=|(l:ℝ)-(k:ℝ)| * ((l:ℝ)+(k:ℝ)+2) := by
    rw [sq_sub_sq,abs_mul]
    have hh : (l+1:ℝ)-(k+1:ℝ)=(l:ℝ)-(k:ℝ) := by ring
    rw [hh,abs_of_nonneg (by positivity : (0:ℝ)≤(l+1:ℝ)+(k+1:ℝ))]
    ring
  rw [he]
  have hs : 0≤(l:ℝ)+(k:ℝ)+2 := by positivity
  have hh := mul_le_mul_of_nonneg_right hdiff hs
  simp only [one_mul] at hh
  exact (max_le (by linarith [Nat.cast_nonneg (α := ℝ) l])
    (by linarith [Nat.cast_nonneg (α := ℝ) k])).trans hh

/-- The original complex reference spectrum has a uniform genuine quadratic-index separation throughout the actual admissible order half-plane.
Use: full Bessel separation for pairs with a large index follows by subtracting the already proved actual all-index inverse-square errors.
Article: jacobi, Lemma E.1.
Proof: the actual reference difference factors into the genuine grid sum and difference. The order shift cancels from the latter, whose norm is pi times the integer gap. The former has real part pi*(l+k+Re(alpha)+3/2), bounded below by l+k+2 for distinct indices and Re(alpha)>-1. -/
theorem frequencyReference_separated {a : ℂ} (ha : -1<a.re) {k l : ℕ} (hkl : k≠l) :
    2*|(l+1:ℝ)^2-(k+1:ℝ)^2|≤‖frequencyReference a l-frequencyReference a k‖ := by
  -- The original quadratic coefficient cancels exactly, even for nonreal order.
  have hd : frequencyGrid a l-frequencyGrid a k=(Real.pi:ℂ)*((l:ℂ)-(k:ℂ)) := by unfold frequencyGrid; ring
  have hnorm : ‖frequencyGrid a l-frequencyGrid a k‖=Real.pi*|(l:ℝ)-(k:ℝ)| := by
    calc
      _ = ‖((Real.pi*((l:ℝ)-(k:ℝ)):ℝ):ℂ)‖ := by congr 1; rw [hd]; push_cast; rfl
      _ = _ := by rw [Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_pos Real.pi_pos]
  have hsumIndex : (1:ℝ)≤(l:ℝ)+(k:ℝ) := by
    have hh : 1≤l+k := by omega
    exact_mod_cast hh
  have hre : (frequencyGrid a l+frequencyGrid a k).re=Real.pi*((l:ℝ)+(k:ℝ)+a.re+3/2) := by
    rw [Complex.add_re,(frequencyGrid_coordinates a l).1,(frequencyGrid_coordinates a k).1]
    ring
  have hsum : (l:ℝ)+(k:ℝ)+2≤‖frequencyGrid a l+frequencyGrid a k‖ := by
    have hh := Complex.re_le_norm (frequencyGrid a l+frequencyGrid a k)
    rw [hre] at hh
    have horder := mul_nonneg Real.pi_pos.le (show 0≤a.re+1 by linarith)
    have hpi := mul_le_mul_of_nonneg_right Real.pi_gt_three.le
      (show 0≤(l:ℝ)+(k:ℝ)+1/2 by linarith)
    nlinarith
  have hdiff : 2*|(l:ℝ)-(k:ℝ)|≤‖frequencyGrid a l-frequencyGrid a k‖ := by
    rw [hnorm]
    nlinarith [Real.pi_gt_three,abs_nonneg ((l:ℝ)-(k:ℝ))]
  have he : |(l+1:ℝ)^2-(k+1:ℝ)^2|=((l:ℝ)+(k:ℝ)+2)*|(l:ℝ)-(k:ℝ)| := by
    have hsum' : (l+1:ℝ)+(k+1:ℝ)=(l:ℝ)+(k:ℝ)+2 := by ring
    have hdiff' : (l+1:ℝ)-(k+1:ℝ)=(l:ℝ)-(k:ℝ) := by ring
    rw [sq_sub_sq,abs_mul,hsum',hdiff',abs_of_nonneg (by positivity : (0:ℝ)≤(l:ℝ)+(k:ℝ)+2)]
  have href : frequencyReference a l-frequencyReference a k=
      (frequencyGrid a l+frequencyGrid a k)*(frequencyGrid a l-frequencyGrid a k) := by unfold frequencyReference; ring
  rw [href,norm_mul,he]
  calc
    _ = ((l:ℝ)+(k:ℝ)+2)*(2*|(l:ℝ)-(k:ℝ)|) := by ring
    _ ≤ _ := mul_le_mul hsum hdiff (by positivity) (norm_nonneg _)

end
end jacobi.Hankel
