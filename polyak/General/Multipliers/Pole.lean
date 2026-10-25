import polyak.General.Multipliers.PoleMinimum
import polyak.General.Multipliers.CubicBridge
import polyak.General.RootsPole

/-! Appendix D, Theorem B(b): the actual dominant negative pole.
The source rational function has a negative residue and is bounded below
on the outer side of the tangent circle.  The proved isolated-boundary
minimum principle then transfers the endpoint cubic sign to every larger
radius. -/

namespace polyak.General.Multipliers
noncomputable section
open Set Metric

theorem negative_residue_lower {r k : ℝ} (hr : 0 < r) (hk : k ≤ 0)
    {z : ℂ} (hz : r ≤ ‖z‖) (hne : z+(r:ℂ) ≠ 0) :
    k/(2*r) ≤ ((k:ℂ)/(z+(r:ℂ))).re := by
  have hn : r^2 ≤ Complex.normSq z := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg z]
  have hn' : 2*r*(z+(r:ℂ)).re ≤ Complex.normSq (z+(r:ℂ)) := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.normSq_apply,
      Complex.add_im, Complex.ofReal_im, add_zero] at hn ⊢
    nlinarith
  rw [Complex.div_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_div, add_zero]
  apply (div_le_div_iff₀ (mul_pos (by norm_num) hr) (Complex.normSq_pos.mpr hne)).2
  have hmul := mul_le_mul_of_nonpos_left hn' hk
  nlinarith

def poleRemainder (q : Tuning) (z : ℂ) : ℂ :=
  (q.poleQuotient z-(q.poleResidue:ℂ))/(z+(q.beta/q.rhoB:ℝ))

theorem source_pole_annulus_nonnegative (q : Tuning)
    (hover : Real.sqrt q.beta < q.rhoQ) (hab : q.rhoA ≤ q.rhoB)
    (hL : ∀ c ∈ Icc (-1 : ℝ) 1, 0 ≤ q.L c)
    (hH : ∀ c ∈ Icc (-1 : ℝ) 1, 0 ≤ q.H q.rhoB c)
    {z : ℂ} (hz : z ∈ annulus q.rhoB 1) : 0 ≤ ((1-z)*q.a z/q.b z).re := by
  classical
  obtain ⟨hr, _, hother, hother0⟩ := q.dominant_b_root hover hab
  rw [neg_div] at hother hother0
  have hr1 : q.rhoB < 1 := (le_max_right _ _).trans_lt q.rhoQ_lt_one
  have hc0 : 0 ≤ q.beta/q.rhoB := div_nonneg q.beta_nonneg hr.le
  have hcsmall : q.beta/q.rhoB < q.rhoB := by linarith
  let K : Set ℂ := {w | q.rhoB ≤ ‖w‖ ∧ ‖w‖ ≤ 1}
  have hden (w : ℂ) (hw : w ∈ K) : w+(q.beta/q.rhoB:ℝ) ≠ 0 := by
    intro he
    have hwe : w = -((q.beta/q.rhoB:ℝ):ℂ) := eq_neg_of_add_eq_zero_left he
    have hnorm : ‖w‖ = q.beta/q.rhoB := by
      rw [hwe, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc0]
    have hw' : q.rhoB ≤ ‖w‖ := hw.1
    linarith
  have hKcompact : IsCompact K := by
    apply (isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset
    · exact (isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const)
    · intro w hw; simpa using hw.2
  have hKne : K.Nonempty := ⟨1, by simpa only [K, mem_ofPred_eq, norm_one] using And.intro hr1.le (le_refl 1)⟩
  have hRc : ContinuousOn (poleRemainder q) K := by
    apply ContinuousOn.div
    · unfold Tuning.poleQuotient; fun_prop
    · fun_prop
    · exact hden
  obtain ⟨w0, hw0, hmin⟩ := hKcompact.exists_isMinOn hKne (Complex.continuous_re.comp_continuousOn hRc)
  let F : ℂ → ℂ := fun w => (1-w)*q.a w/q.b w
  let U := annulus q.rhoB 1
  let p : ℂ := -(q.rhoB:ℂ)
  have hcl (w : ℂ) (hw : w ∈ closure U) : w ∈ K := annulus_closure_subset _ _ hw
  have hp : p ∉ U := by simp [U,annulus,p,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
  have hnonzero (w : ℂ) (hw : w ∈ closure U) (hwp : w ≠ p) : q.b w ≠ 0 := by
    rw [q.dominant_b_factor hover hab]
    apply mul_ne_zero
    · exact fun he => hwp (eq_neg_of_add_eq_zero_left he)
    · exact hden w (hcl w hw)
  apply real_nonneg_of_frontier_except (F := F) (p := p) (annulus_bounded _ _)
    ?_ ?_ hp ?_ ((poleRemainder q w0).re+q.poleResidue/(2*q.rhoB)) 2 (by norm_num) ?_ ?_ hz
  · apply DifferentiableOn.div
    · unfold Tuning.a; fun_prop
    · unfold Tuning.b; fun_prop
    · intro w hw; exact b_ne_zero_outside q hw.1
  · apply ContinuousOn.div
    · unfold Tuning.a; fun_prop
    · unfold Tuning.b; fun_prop
    · intro w hw; exact hnonzero w hw.1 hw.2
  · intro w hw hwp
    rcases annulus_frontier_subset _ _ hw with hnorm | hnorm
    · have hb := hnonzero w hw.1 hwp
      have hsign := hH (Real.cos (Complex.arg w)) ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩
      have he := H_norm_arg q hb
      rw [hnorm] at he
      rw [he] at hsign
      exact nonneg_of_mul_nonneg_right hsign (Complex.normSq_pos.mpr hb)
    · exact source_outer_nonnegative q hL w hnorm
  · intro w hw hwp
    have hwK := hcl w hw
    have hneq : w+(q.rhoB:ℂ) ≠ 0 := fun he => hwp (eq_neg_of_add_eq_zero_left he)
    have hRmin : (poleRemainder q w0).re ≤ (poleRemainder q w).re := hmin hwK
    have hres := negative_residue_lower hr (q.poleResidue_neg hover hab).le hwK.1 hneq
    change _ ≤ ((1-w)*q.a w/q.b w).re
    rw [q.negative_pole_decomposition hover hab hneq (hden w hwK), Complex.add_re]
    change (poleRemainder q w0).re ≤
      ((q.poleQuotient w-(q.poleResidue:ℂ))/(w+(q.beta/q.rhoB:ℝ))).re at hRmin
    linarith
  · intro w hw
    have hwK := hcl w hw
    calc
      ‖w-p‖ ≤ ‖w‖+‖p‖ := norm_sub_le _ _
      _ ≤ 1+q.rhoB := by simpa [p,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr] using add_le_add_right hwK.2 q.rhoB
      _ ≤ 2 := by linarith

theorem source_pole_radii (q : Tuning)
    (hover : Real.sqrt q.beta < q.rhoQ) (hab : q.rhoA ≤ q.rhoB)
    (hL : ∀ c ∈ Icc (-1 : ℝ) 1, 0 ≤ q.L c)
    (hH : ∀ c ∈ Icc (-1 : ℝ) 1, 0 ≤ q.H q.rhoB c)
    {r : ℝ} (hr : q.rhoB < r) (hr1 : r < 1) :
    ∀ c ∈ Icc (-1 : ℝ) 1, 0 ≤ q.H r c := by
  apply (source_inner_iff q hr).2
  intro z hz
  exact source_pole_annulus_nonnegative q hover hab hL hH
    (show z ∈ annulus q.rhoB 1 from ⟨hz.symm ▸ hr,hz.symm ▸ hr1⟩)

theorem source_pole_annulus_positive (q : Tuning)
    (hover : Real.sqrt q.beta < q.rhoQ) (hab : q.rhoA ≤ q.rhoB)
    (hL : ∀ c ∈ Icc (-1 : ℝ) 1, 0 < q.L c)
    (hH : ∀ c ∈ Icc (-1 : ℝ) 1, 0 ≤ q.H q.rhoB c)
    {z : ℂ} (hz : z ∈ annulus q.rhoB 1) : 0 < ((1-z)*q.a z/q.b z).re := by
  let r := (q.rhoB+‖z‖)/2
  have hr : q.rhoB < r := by dsimp [r]; linarith [hz.1]
  have hrz : r < ‖z‖ := by dsimp [r]; linarith [hz.1]
  have hr1 : r < 1 := hrz.trans hz.2
  have hHr := source_pole_radii q hover hab (fun c hc => (hL c hc).le) hH hr hr1
  have hi : ∀ w : ℂ, ‖w‖=r → 0 ≤ (lowerRatio q {1} (fun _ => 1) w).re := by
    simpa [lowerRatio,polynomial] using source_inner_nonnegative q hr hHr
  have ho : ∀ w : ℂ, ‖w‖=1 → w≠1 → 0 < (lowerRatio q {1} (fun _ => 1) w).re := by
    simpa [lowerRatio,polynomial] using source_outer_positive q hL
  have hpos := lower_annulus_positive q {1} (fun _ => 1) hr hr1 hi ho
    (show z ∈ annulus r 1 from ⟨hrz,hz.2⟩)
  simpa [lowerRatio,polynomial] using hpos

end
end polyak.General.Multipliers
