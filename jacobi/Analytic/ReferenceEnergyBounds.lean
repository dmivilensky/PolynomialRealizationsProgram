import jacobi.Analytic.ReferenceEnergyGeometry

/-!
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Uniform bounds for the genuine reference solution on bounded complex
energy neighborhoods of the original moving reference spectrum.
The finite prefix is included by compactness of the original functions.
Use: gives uniform energy Cauchy bounds for the actual spectral displacement in the GL summands.
-/
namespace jacobi.Analytic
noncomputable section
open Set Metric Filter jacobi.ComplexReference jacobi.Hankel
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The actual complex-order reference solution has its original index-power bound on each fixed-radius reference energy tube in the spectral tail.
Use: gives uniform energy Cauchy bounds for the actual spectral displacement in the GL summands.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the actual perturbed frequencies lie in one proved strip and have norm at least a quarter of the shifted index. Apply the genuine strip amplitude bound, then absorb the bounded order-dependent power of four into one constant. -/
theorem OrderDisk.reference_energy_tail {a0 : ℝ} (D : OrderDisk a0)
    {E : ℝ} (hE : 0≤E) :
    ∃ C : ℝ,0<C ∧ ∀ a : ℂ,‖a-(a0:ℂ)‖≤D.radius →
      ∀ k : ℕ,8*E+4≤(k+1:ℝ) → ∀ z : ℂ,‖z-frequencyReference a k‖≤E →
        ∀ t∈Icc (0:ℝ) (1/2),‖solution a z t‖≤C/(k+1:ℝ)^(gamma a).re := by
  -- The original reference solution is independent of the sign selected for its estimating frequency.
  let G : ℝ := ‖gamma (a0:ℂ)‖+D.radius/2+1
  obtain ⟨C,hC,hbound⟩ := D.reference_strip_bound (Real.pi*D.radius/2+2*E)
  refine ⟨C*4^G,by positivity,fun a ha k hk z hz t ht => ?_⟩
  obtain ⟨w,hw,him,hn⟩ := D.energy_frequency_geometry hE ha k hk hz
  have hkp : 0<(k+1:ℝ) := by positivity
  have hg : 0<(gamma a).re := by have har := D.admissible ha; unfold gamma; norm_num; linarith
  have hgn : (gamma a).re≤G := by
    have hshift : gamma a-gamma (a0:ℂ)=(a-(a0:ℂ))/2 := by unfold gamma; ring
    have hd : ‖gamma a-gamma (a0:ℂ)‖≤D.radius/2 := by
      rw [hshift,norm_div]
      norm_num
      exact div_le_div_of_nonneg_right ha (by norm_num)
    have hh := norm_le_norm_sub_add (gamma a) (gamma (a0:ℂ))
    have hr := Complex.re_le_norm (gamma a)
    dsimp [G]
    linarith
  have hwne : w≠0 := norm_pos_iff.mp ((div_pos hkp (by norm_num)).trans_le hn)
  have hp : ‖w‖^(-(gamma a).re)≤4^G/(k+1:ℝ)^(gamma a).re := by
    calc
      _ ≤ ((k+1:ℝ)/4)^(-(gamma a).re) := Real.rpow_le_rpow_of_nonpos (by positivity) hn (by linarith)
      _ = 4^(gamma a).re/(k+1:ℝ)^(gamma a).re := by
        rw [Real.rpow_neg (by positivity),Real.div_rpow hkp.le (by norm_num),inv_div]
      _ ≤ _ := div_le_div_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) hgn) (by positivity)
  rw [solution_eq_wave a hw t]
  exact ((hbound a ha w hwne him t ht).trans
    (mul_le_mul_of_nonneg_left (min_le_right _ _) hC.le)).trans
      (by have hh := mul_le_mul_of_nonneg_left hp hC.le; simpa only [mul_div_assoc] using hh)

/-- Every fixed actual reference energy tube has a finite uniform normalized solution bound on the whole closed order disk and physical half interval.
Use: absorbs all genuine finite spectral indices into the all-index estimate required by analytic GL.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: parametrize the energy tube by its compact displacement disk. Joint continuity of the original energy solution and continuity of its exact positive-index complex power give a compact bound on their product. Its norm is precisely the desired normalization. -/
theorem OrderDisk.reference_energy_prefix {a0 : ℝ} (D : OrderDisk a0)
    (E : ℝ) (k : ℕ) :
    ∃ C : ℝ,0<C ∧ ∀ a : ℂ,‖a-(a0:ℂ)‖≤D.radius →
      ∀ z : ℂ,‖z-frequencyReference a k‖≤E → ∀ t∈Icc (0:ℝ) (1/2),
        ‖solution a z t‖≤C/(k+1:ℝ)^(gamma a).re := by
  -- The finite-index bound concerns the actual energy function at the original reference tube.
  let K := closedBall (a0:ℂ) D.radius ×ˢ (closedBall (0:ℂ) E ×ˢ Icc (0:ℝ) (1/2))
  let f := fun p : ℂ × ℂ × ℝ =>
    solution p.1 (frequencyReference p.1 k+p.2.1) p.2.2*((k+1:ℝ):ℂ)^(gamma p.1)
  have hK : IsCompact K := (isCompact_closedBall _ _).prod ((isCompact_closedBall _ _).prod isCompact_Icc)
  have hf : ContinuousOn f K := by
    intro p hp
    have ha : ‖p.1-(a0:ℂ)‖≤D.radius := by simpa only [mem_closedBall,dist_eq_norm] using hp.1
    have hg : 0<(gamma p.1).re := by have har := D.admissible ha; unfold gamma; norm_num; linarith
    have hs := (solution_joint_continuous hg
      (show p.2.2∈Ico 0 1 from ⟨hp.2.2.1,by linarith [hp.2.2.2]⟩)).comp_of_eq
      (show ContinuousAt (fun q : ℂ × ℂ × ℝ =>
        (q.1,frequencyReference q.1 k+q.2.1,q.2.2)) p by
        unfold frequencyReference frequencyGrid besselCoefficient
        fun_prop) rfl
    have hpow := (continuousAt_const (x := p) (y := ((k+1:ℝ):ℂ))).cpow
      (show ContinuousAt (fun q : ℂ × ℂ × ℝ => gamma q.1) p by unfold gamma; fun_prop)
      (Or.inl (by simp only [Complex.ofReal_re]; positivity))
    exact (hs.mul hpow).continuousWithinAt
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn hf
  refine ⟨|B|+1,by positivity,fun a ha z hz t ht => ?_⟩
  have hp : (a,z-frequencyReference a k,t)∈K :=
    ⟨by simpa only [mem_closedBall,dist_eq_norm] using ha,
      by simpa only [mem_closedBall,dist_zero_right] using hz,ht⟩
  have hh := hB _ hp
  change ‖solution a (frequencyReference a k+(z-frequencyReference a k)) t*
    ((k+1:ℝ):ℂ)^(gamma a)‖≤B at hh
  rw [show frequencyReference a k+(z-frequencyReference a k)=z by ring,
    norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)] at hh
  exact (le_div_iff₀ (Real.rpow_pos_of_pos (by positivity) _)).mpr
    (hh.trans (by linarith [le_abs_self B]))

/-- The actual complex-order reference solutions have the required uniform index-power bound on every fixed-radius reference energy tube, at every spectral index.
Use: supplies the original reference amplitudes and their unit-circle Cauchy bounds in the normal GL kernel series.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: use the proved frequency-strip estimate in the tail and compact normalized bounds for each remaining original index. A finite sum of prefix constants and the tail constant gives one positive coefficient on the whole disk. -/
theorem OrderDisk.reference_energy_bound {a0 : ℝ} (D : OrderDisk a0)
    {E : ℝ} (hE : 0≤E) :
    ∃ C : ℝ,0<C ∧ ∀ a : ℂ,‖a-(a0:ℂ)‖≤D.radius → ∀ k : ℕ,
      ∀ z : ℂ,‖z-frequencyReference a k‖≤E → ∀ t∈Icc (0:ℝ) (1/2),
        ‖solution a z t‖≤C/(k+1:ℝ)^(gamma a).re := by
  -- Every original spectral index is covered; the compact prefix is not discarded.
  obtain ⟨C,hC,htail⟩ := D.reference_energy_tail hE
  obtain ⟨N,hN⟩ := exists_nat_ge (8*E+4)
  choose B hBpos hB using D.reference_energy_prefix E
  let S := ∑ j∈Finset.range N,B j
  have hS : 0≤S := Finset.sum_nonneg (fun j _ => (hBpos j).le)
  refine ⟨C+S,by linarith,fun a ha k z hz t ht => ?_⟩
  by_cases hk : N≤k
  · have hkn : (N:ℝ)≤k := by exact_mod_cast hk
    exact (htail a ha k (by linarith)
      z hz t ht).trans (div_le_div_of_nonneg_right (by linarith) (by positivity))
  · have hi : B k≤S := Finset.single_le_sum (s := Finset.range N) (f := B)
      (fun j _ => (hBpos j).le) (Finset.mem_range.mpr (by omega))
    exact (hB k a ha z hz t ht).trans (div_le_div_of_nonneg_right (by linarith) (by positivity))

end
end jacobi.Analytic
