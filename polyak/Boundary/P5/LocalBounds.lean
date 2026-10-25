import polyak.Boundary.P5.LocalLimits

/-!
Article: (centralbounds), all quantitative hypotheses of the uniform P5 tail.
Use: every continuous branch through the exact critical point satisfies these
bounds on one common interval to the right of h=0.
-/
noncomputable section
namespace polyak.Boundary.P5
open Spectral Filter
open scoped Topology

/-- Article: the main and auxiliary atoms and all tail bounds exist simultaneously. -/
theorem eventually_tailBounds {Z : ℝ → Coordinates} (hZ : ContinuousAt Z 0)
    (hZ0 : Z 0=criticalPoint) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ),
      ∃ hx : -1≤branchX h (Z h) ∧ branchX h (Z h)≤1,
      ∃ hy : -1≤Z h 2 ∧ Z h 2≤1,
      TailBounds h (branchU h (Z h)) (h*Z h 3) (h*Z h 4)
        ⟨branchX h (Z h),hx⟩ ⟨Z h 2,hy⟩ := by
  have hz (i : Fin 7) : ContinuousAt (fun h => Z h i) 0 :=
    (continuous_apply i).continuousAt.comp hZ
  have hu := branchU_hasDerivAt hZ hZ0
  have hx := branchX_hasDerivAt hZ hZ0
  have hu0 : branchU 0 (Z 0)=(1/2 : ℝ) := by simp [branchU]
  have hx0 : branchX 0 (Z 0)=(-1/2 : ℝ) := by simp [branchX]
  have hP0 : Z 0 3=P₀ := by simp [hZ0]
  have hD0 : Z 0 4=D₀ := by simp [hZ0]
  have hy0 : Z 0 2=y₀ := by simp [hZ0]
  have huBand : ∀ᶠ h in 𝓝 (0 : ℝ), 0<branchU h (Z h) ∧ branchU h (Z h)<11/20 :=
    hu.continuousAt.tendsto.eventually (Ioo_mem_nhds
      (by rw [hu0]; norm_num) (by rw [hu0]; norm_num))
  have hxBand : ∀ᶠ h in 𝓝 (0 : ℝ), -1<branchX h (Z h) ∧ branchX h (Z h)<1 :=
    hx.continuousAt.tendsto.eventually (Ioo_mem_nhds
      (by rw [hx0]; norm_num) (by rw [hx0]; norm_num))
  have hyBand : ∀ᶠ h in 𝓝 (0 : ℝ), -1<Z h 2 ∧ Z h 2<1 :=
    (hz 2).tendsto.eventually (Ioo_mem_nhds
      (by rw [hy0]; exact y₀_interior.1) (by rw [hy0]; exact y₀_interior.2))
  have hpBand : ∀ᶠ h in 𝓝 (0 : ℝ), 0<Z h 3 ∧ Z h 3<3 :=
    (hz 3).tendsto.eventually (Ioo_mem_nhds
      (by rw [hP0]; exact P₀_bounds.1) (by rw [hP0]; linarith [P₀_bounds.2]))
  have hdBand : ∀ᶠ h in 𝓝 (0 : ℝ), 0<Z h 4 ∧ Z h 4<11/5 :=
    (hz 4).tendsto.eventually (Ioo_mem_nhds
      (by rw [hD0]; exact D₀_bounds.1) (by rw [hD0]; linarith [D₀_bounds.2]))
  have hmainCont : ContinuousAt (fun h => mainGapCoefficient h (Z h)) 0 := by
    unfold mainGapCoefficient
    fun_prop
  have hmainCrit : |mainGapCoefficient 0 (Z 0)|<1 := by
    simpa [mainGapCoefficient,hZ0] using critical_local_limits.1
  have hmain := hmainCont.abs.tendsto.eventually (eventually_lt_nhds hmainCrit)
  have hmeanCont : ContinuousAt (fun h => meanGapCoefficient h (Z h)) 0 := by
    unfold meanGapCoefficient mainGapCoefficient branchU branchX g
    fun_prop
  have hmeanCrit : |meanGapCoefficient 0 (Z 0)|<2 := by
    simpa only [hZ0] using critical_meanGapCoefficient
  have hmean := hmeanCont.abs.tendsto.eventually (eventually_lt_nhds hmeanCrit)
  have hgapCont : ContinuousAt (fun h => branchGap h (Z h)) 0 := by
    unfold branchGap branchU branchX g
    fun_prop
  have hgap0 : branchGap 0 (Z 0)=(1/2 : ℝ) := by norm_num [branchGap,branchU,branchX,g]
  have hgap := hgapCont.tendsto.eventually (eventually_gt_nhds
    (show (49/100 : ℝ)<branchGap 0 (Z 0) by rw [hgap0]; norm_num))
  have hchargeCont : ContinuousAt (fun h => regularCharge h (Z h 4)) 0 := by
    unfold regularCharge
    fun_prop (disch := norm_num)
  have hstarCont := hgapCont.sub hchargeCont.abs
  have hstar := hstarCont.tendsto.eventually (eventually_gt_nhds
    (show (1/4 : ℝ)<branchGap 0 (Z 0)-|regularCharge 0 (Z 0 4)| by
      rw [hgap0]; norm_num [regularCharge]))
  have hphase := eventually_abs_difference_lt (branch_phase_hasDerivAt hZ hZ0) critical_phase_derivative
  have hamp := eventually_abs_difference_lt (branch_amplitude_hasDerivAt hZ hZ0) critical_amplitude_derivative
  have hangle0 : Real.arccos (branchX 0 (Z 0))=2*Real.pi/3 := by
    convert Spiral.angle_zero using 1
    norm_num [branchX]
  have hamp0 : 2*branchU 0 (Z 0)*Real.sin (Real.arccos (branchX 0 (Z 0)))=Real.sqrt 3/2 := by
    rw [hu0,hx0,Real.sin_arccos,sqrt_cycle]
    ring
  have hsmall : ∀ᶠ h in 𝓝 (0 : ℝ), h<59/2500 := eventually_lt_nhds (by norm_num)
  filter_upwards [huBand.filter_mono nhdsWithin_le_nhds,hxBand.filter_mono nhdsWithin_le_nhds,
    hyBand.filter_mono nhdsWithin_le_nhds,hpBand.filter_mono nhdsWithin_le_nhds,
    hdBand.filter_mono nhdsWithin_le_nhds,hmain.filter_mono nhdsWithin_le_nhds,
    hmean.filter_mono nhdsWithin_le_nhds,hgap.filter_mono nhdsWithin_le_nhds,
    hstar.filter_mono nhdsWithin_le_nhds,hphase,hamp,hsmall.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with h huB hxB hyB hpB hdB hm hn hg hs hph ha hhmax hh
  refine ⟨⟨hxB.1.le,hxB.2.le⟩,⟨hyB.1.le,hyB.2.le⟩,?_⟩
  refine {
    h_pos := hh
    h_le := hhmax.le
    u_nonneg := huB.1.le
    u_lt := huB.2
    p_nonneg := mul_nonneg hh.le hpB.1.le
    p_le := ?_
    d_nonneg := mul_nonneg hh.le hdB.1.le
    d_le := ?_
    gap_gt := hg
    star_gt := ?_
    main_gap := ?_
    mean_gap := ?_
    amplitude := ?_
    phase := ?_ }
  · nlinarith [mul_le_mul_of_nonneg_left hpB.2.le hh.le]
  · nlinarith [mul_le_mul_of_nonneg_left hdB.2.le hh.le]
  · rw [charge_eq_regular hh]
    exact hs
  · change |g (branchU h (Z h)) (branchX h (Z h))-1/2|<h
    rw [main_gap_difference,abs_mul,abs_of_pos hh]
    nlinarith [mul_lt_mul_of_pos_left hm hh]
  · change |branchGap h (Z h)-1/2|<2*h
    rw [mean_gap_difference,abs_mul,abs_of_pos hh]
    nlinarith [mul_lt_mul_of_pos_left hn hh]
  · simpa only [hamp0] using ha
  · rw [hangle0] at hph
    exact hph.trans_eq (by ring)

end polyak.Boundary.P5
