import jacobi.Hankel.FrequencyGrid

/-!
Article: jacobi, Lemma E.1.
Use: the actual continued Bessel spectral tail has nonzero denominators and the quadratic lower bound in Lemma E.1.
-/
namespace jacobi.Hankel
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Every genuine squared frequency in an original moving grid disk has norm at least its squared original Lean index.
Use: the actual continued Bessel spectral tail has nonzero denominators and the quadratic lower bound in Lemma E.1.
Article: jacobi, Lemma E.1.
Proof: the actual grid disk has real part at least k, so the genuine frequency norm is at least k; square the true norm inequality. -/
theorem frequency_disk_squared_lower {a : ℂ} {a0 r : ℝ} (ha : ‖a-(a0:ℂ)‖<r)
    (hr : r≤1) (har : -1<a.re) (k : ℕ) {ζ : ℂ} (hζ : ‖ζ‖≤1/4) :
    (k:ℝ)^2≤‖(frequencyGrid a k+ζ)^2‖ := by
  rw [norm_pow]
  exact pow_le_pow_left₀ (Nat.cast_nonneg k)
    ((frequencyGrid_disk_geometry ha hr har k hζ).1.trans (Complex.re_le_norm _)) 2

/-- Two genuine squared frequencies in different original moving grid disks have the full uniform quadratic-index separation.
Use: the original continued Bessel zero tail satisfies Lemma E.1 directly from its actual disk construction.
Article: jacobi, Lemma E.1.
Proof: the actual difference of frequencies differs from pi*(l-k) by at most one half; distinct integer indices have distance at least one. The sum of frequencies has real part at least l+k. Factor the original squared difference and multiply these two genuine norm lower bounds. -/
theorem frequency_disks_squared_separated {a : ℂ} {a0 r : ℝ} (ha : ‖a-(a0:ℂ)‖<r)
    (hr : r≤1) (har : -1<a.re) {k l : ℕ} (hkl : k≠l) {ζ η : ℂ}
    (hζ : ‖ζ‖≤1/4) (hη : ‖η‖≤1/4) :
    |(l:ℝ)^2-(k:ℝ)^2|≤‖(frequencyGrid a l+η)^2-(frequencyGrid a k+ζ)^2‖ := by
  -- The original order shift cancels from the true grid difference, including for nonreal order.
  let z := frequencyGrid a k+ζ
  let w := frequencyGrid a l+η
  have hd : frequencyGrid a l-frequencyGrid a k=(Real.pi:ℂ)*((l:ℂ)-(k:ℂ)) := by unfold frequencyGrid; ring
  have hn : ‖frequencyGrid a l-frequencyGrid a k‖=Real.pi*|(l:ℝ)-(k:ℝ)| := by
    calc
      _ = ‖((Real.pi*((l:ℝ)-(k:ℝ)):ℝ):ℂ)‖ := by
        congr 1
        rw [hd]
        push_cast
        rfl
      _ = _ := by rw [Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_pos Real.pi_pos]
  have he : frequencyGrid a l-frequencyGrid a k=(w-z)-(η-ζ) := by dsimp [w,z]; ring
  have hsmall : ‖η-ζ‖≤1/2 := (norm_sub_le _ _).trans (by linarith)
  have htriangle := norm_sub_le (w-z) (η-ζ)
  rw [← he,hn] at htriangle
  have hindex : 1≤|(l:ℝ)-(k:ℝ)| := by
    rcases lt_or_gt_of_ne hkl with hlt | hgt
    · have hh : (k:ℝ)+1≤(l:ℝ) := by exact_mod_cast Nat.add_one_le_iff.mpr hlt
      rw [abs_of_nonneg (by linarith : (0:ℝ)≤(l:ℝ)-(k:ℝ))]
      linarith
    · have hh : (l:ℝ)+1≤(k:ℝ) := by exact_mod_cast Nat.add_one_le_iff.mpr hgt
      rw [abs_of_nonpos (by linarith : (l:ℝ)-(k:ℝ)≤0)]
      linarith
  have hdiff : |(l:ℝ)-(k:ℝ)|≤‖w-z‖ := by nlinarith [Real.pi_gt_three]
  have hkre := (frequencyGrid_disk_geometry ha hr har k hζ).1
  have hlre := (frequencyGrid_disk_geometry ha hr har l hη).1
  have hsum : (l:ℝ)+(k:ℝ)≤‖w+z‖ := by
    have hh := Complex.re_le_norm (w+z)
    rw [Complex.add_re] at hh
    dsimp only [w,z] at hh
    linarith
  have hsumnonneg : 0≤(l:ℝ)+(k:ℝ) := by positivity
  have hpoly : |(l:ℝ)^2-(k:ℝ)^2|=((l:ℝ)+(k:ℝ))*|(l:ℝ)-(k:ℝ)| := by
    rw [sq_sub_sq,abs_mul,abs_of_nonneg hsumnonneg]
  rw [hpoly,sq_sub_sq,norm_mul]
  exact mul_le_mul hsum hdiff (abs_nonneg _) (norm_nonneg _)

end
end jacobi.Hankel
