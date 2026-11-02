import jacobi.Variational.FredholmKKT
import jacobi.Variational.TopActivity
import jacobi.Variational.FredholmLowerSemicontinuity

/-!
Article: jacobi, Theorem D.7.
Every actual minimizer at a finite Fredholm threshold lies strictly below
its spectral pole. An explicit sequence of smaller amplitudes approaches
the pole, where the proved extended Fredholm lower semicontinuity forces
feasibility. Each such feasible amplitude strictly lowers the actual energy.
Source: actual amplitude homogeneity and the full extended spectral series.
Use: the genuine density sequence approaching a pole satisfies the existing L1 semicontinuity theorem.
-/
namespace jacobi.Fredholm
noncomputable section
open Real Set MeasureTheory Filter jacobi.Variational
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false

/-- Actual nonnegative amplitude changes have precisely their scalar L1 distance.
Use: the genuine density sequence approaching a pole satisfies the existing L1 semicontinuity theorem.
Article: jacobi, Theorem D.7.
Proof: factor the nonnegative original density from the absolute difference and its integral. -/
theorem amplitude_distance (m : Density) {a b : ℝ} (ha : 0≤a) (hb : 0≤b) :
    (∫ x,|(m.scale a ha).value x-(m.scale b hb).value x|)=|a-b| *m.mass := by
  change (∫ x,|a*m.value x-b*m.value x|)=_
  simp_rw [← sub_mul,abs_mul,abs_of_nonneg (m.nonneg _)]
  exact integral_const_mul _ _

/-- Every actual nonzero minimizer of a finite-threshold Fredholm problem lies strictly below the true top spectral pole.
Use: discharges the pole premise in the Fredholm KKT theorem and every subsequent optimizer profile identity.
Article: jacobi, Theorem D.7.
Proof: a sequence of amplitudes strictly below the critical factor converges
to a source whose determinant is infinite. Actual L1 lower semicontinuity
makes some smaller-amplitude source feasible at the finite target. Its
strictly smaller actual energy contradicts the original minimizing property. -/
theorem minimizer_subcritical {s M d : ℝ} (hs : 0<s) (m : Density) (hm : 0<m.mass)
    (hmM : m.mass≤M) (hmin : m.cost=fredholmInfimum s M (ENNReal.ofReal d)) :
    s*observe m .top<1 := by
  -- The pole is approached by actual densities with amplitudes strictly below one.
  by_contra! hp
  let a0 : ℝ := (s*observe m .top)⁻¹
  have hprod : 0<s*observe m .top := zero_lt_one.trans_le hp
  have ha0 : 0<a0 := inv_pos.mpr hprod
  have ha01 : a0≤1 := (inv_le_one₀ hprod).mpr hp
  let a (n : ℕ) : ℝ := a0*(1-1/((n:ℝ)+2))
  have ha (n : ℕ) : 0<a n ∧ a n<a0 := by
    have hn : 0<(1:ℝ)/((n:ℝ)+2) := by positivity
    have hn1 : (1:ℝ)/((n:ℝ)+2)<1 := (div_lt_one (by positivity)).mpr (by have hn0 : (0:ℝ)≤n := Nat.cast_nonneg n; linarith)
    exact ⟨mul_pos ha0 (by linarith),(mul_lt_mul_of_pos_left (by linarith : 1-1/((n:ℝ)+2)<1) ha0).trans_eq (mul_one a0)⟩
  have halim : Tendsto a atTop (𝓝 a0) := by
    have hdiv : Tendsto (fun n : ℕ => (1:ℝ)/((n:ℝ)+2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop (2:ℝ) tendsto_natCast_atTop_atTop)
    have hh := ((tendsto_const_nhds (x := (1:ℝ))).sub hdiv).const_mul a0
    simpa only [sub_zero,mul_one] using hh
  let q (n : ℕ) := m.scale (a n) (ha n).1.le
  let w := m.scale a0 ha0.le
  have htop : s*observe w .top=1 := by
    rw [Density.scale_top m hm a0 ha0]
    dsimp only [a0]
    have htopne : observe m .top≠0 := by intro hz; rw [hz,mul_zero] at hprod; exact hprod.false
    field_simp [htopne]
  have hwinf : w.fredholm s=∞ := fredholmSpectrum_eq_top (j := 0) htop.ge
  have hL1 : Tendsto (fun n => ∫ x,|(q n).value x-w.value x|) atTop (𝓝 0) := by
    change Tendsto (fun n => ∫ x,|(m.scale (a n) (ha n).1.le).value x-(m.scale a0 ha0.le).value x|) atTop (𝓝 0)
    simp_rw [amplitude_distance m (ha _).1.le ha0.le]
    simpa only [sub_self,abs_zero,zero_mul] using ((halim.sub_const a0).abs.mul_const m.mass)
  have hlim : liminf (fun n => (q n).fredholm s) atTop=∞ := by
    have hh := fredholm_le_liminf_of_l1 q w.toL1Source hL1 hs.le
    rw [hwinf] at hh
    exact top_le_iff.mp hh
  obtain ⟨n,hn⟩ := (eventually_lt_of_lt_liminf (show ENNReal.ofReal d<liminf (fun n => (q n).fredholm s) atTop by
    rw [hlim]; exact ENNReal.ofReal_lt_top)).exists
  have hqM : (q n).mass≤M := by
    rw [Density.scale_mass]
    exact (mul_le_of_le_one_left (integral_nonneg m.nonneg) ((ha n).2.le.trans ha01)).trans hmM
  have hcost : m.cost≤(q n).cost := by rw [hmin]; exact sInf_le ⟨q n,⟨hqM,hn.le⟩,rfl⟩
  have hE := (ENNReal.ofReal_le_ofReal_iff (q n).energy_nonneg).mp hcost
  rw [Density.scale_energy] at hE
  have hpow : a n^(3/2:ℝ)<1 := rpow_lt_one (ha n).1.le ((ha n).2.trans_le ha01) (by norm_num)
  nlinarith [m.energy_pos hm]

end
end jacobi.Fredholm
