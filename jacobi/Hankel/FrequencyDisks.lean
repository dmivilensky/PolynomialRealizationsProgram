import jacobi.Hankel.FrequencyGrid

/-!
Article: jacobi, Lemma E.1.
Use: the actual unique simple-zero construction uses the same uniform index cutoff, order disk, original nonzero connection factor and true derivative remainder.
-/
namespace jacobi.Hankel
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- One common complex-order disk has a genuine cubic Bessel Hankel value-and-slope bound on every original sufficiently large phase-grid frequency disk.
Use: the actual unique simple-zero construction uses the same uniform index cutoff, order disk, original nonzero connection factor and true derivative remainder.
Article: jacobi, Lemma E.1.
Proof: specialize the independently proved actual strip theorem to width four, shrink the original order radius to at most one, and choose one natural cutoff beyond the strip's true real-part threshold. The genuine affine-grid geometry places every original moving disk there, and its real part is at least its original index. -/
theorem uniform_bessel_frequency_disks {a0 : ℝ} (ha0 : -1<a0) :
    ∃ R r C : ℝ,∃ hR : 0<R,∃ N : ℕ,0<r ∧ r≤1 ∧ r<a0+1 ∧ 0<C ∧ 1≤N ∧
      ∀ a : ℂ,‖a-(a0:ℂ)‖<r → ‖besselCoefficient a‖/R≤1/2 ∧ -1<a.re ∧ outgoingBesselCoefficient hR a≠0 ∧
      ∀ k : ℕ,N≤k → ∀ ζ : ℂ,‖ζ‖≤1/4 →
        1≤(frequencyGrid a k+ζ).re ∧
        ‖frequencyError hR a (frequencyGrid a k+ζ)‖≤C/(k:ℝ)^3 ∧
        ‖frequencyErrorSlope hR a (frequencyGrid a k+ζ)‖≤C/(k:ℝ)^3 := by
  -- A single original frequency-strip theorem covers every moving disk, not only finitely many frequencies.
  obtain ⟨R,r,C,hR,hr,hra,hC,hdata⟩ := uniform_bessel_frequency_strip (b := 4) ha0
  obtain ⟨N,hN⟩ := exists_nat_gt (max (R+1) 1)
  have hN1 : 1≤N := by exact_mod_cast (lt_of_le_of_lt (le_max_right (R+1) 1) hN).le
  refine ⟨R,min r 1,C,hR,N,lt_min hr zero_lt_one,min_le_right _ _,
    (min_le_left _ _).trans_lt hra,hC,hN1,fun a ha => ?_⟩
  obtain ⟨hcoef,hreal,hA,herror⟩ := hdata a (ha.trans_le (min_le_left _ _))
  refine ⟨hcoef,hreal,hA,fun k hk ζ hζ => ?_⟩
  obtain ⟨hre,him⟩ := frequencyGrid_disk_geometry ha (min_le_right r 1) hreal k hζ
  have hNk : (N:ℝ)≤(k:ℝ) := by exact_mod_cast hk
  have hlarge : max (R+1) 1≤(frequencyGrid a k+ζ).re := (hN.le.trans hNk).trans hre
  have hpair := herror (frequencyGrid a k+ζ) hlarge him
  have hkpos : 0<(k:ℝ) := lt_of_lt_of_le zero_lt_one
    ((by exact_mod_cast hN1 : (1:ℝ)≤(N:ℝ)).trans hNk)
  have hquot : C/(frequencyGrid a k+ζ).re^3≤C/(k:ℝ)^3 := by gcongr
  exact ⟨(le_max_right (R+1) 1).trans hlarge,hpair.1.trans hquot,hpair.2.trans hquot⟩

end
end jacobi.Hankel
