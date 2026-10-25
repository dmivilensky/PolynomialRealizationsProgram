import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-! Appendix D: the weak and strong minimum principles used for multiplier
ratios.  They follow from the ordinary complex maximum modulus principle,
applied to `exp (-F)`, so no harmonic minimum principle is assumed. -/

namespace polyak.General.Multipliers
noncomputable section
open Set Metric

theorem real_nonneg_of_frontier {F : ℂ → ℂ} {U : Set ℂ}
    (hU : Bornology.IsBounded U) (hF : DiffContOnCl ℂ F U)
    (hboundary : ∀ z ∈ frontier U, 0 ≤ (F z).re)
    {z : ℂ} (hz : z ∈ closure U) : 0 ≤ (F z).re := by
  have he : DiffContOnCl ℂ (fun z => Complex.exp (-F z)) U :=
    Complex.differentiable_exp.comp_diffContOnCl hF.neg
  have hn : ‖Complex.exp (-F z)‖ ≤ 1 :=
    Complex.norm_le_of_forall_mem_frontier_norm_le hU he (fun w hw => by
      rw [Complex.norm_exp, Complex.neg_re, Real.exp_le_one_iff]
      exact neg_nonpos.mpr (hboundary w hw)) hz
  rw [Complex.norm_exp, Complex.neg_re, Real.exp_le_one_iff] at hn
  exact neg_nonpos.mp hn

theorem real_pos_of_frontier {F : ℂ → ℂ} {U : Set ℂ}
    (hU : Bornology.IsBounded U) (hc : IsPreconnected U) (ho : IsOpen U)
    (hF : DiffContOnCl ℂ F U)
    (hboundary : ∀ z ∈ frontier U, 0 ≤ (F z).re)
    (hpositive : ∃ w ∈ closure U, 0 < (F w).re)
    {z : ℂ} (hz : z ∈ U) : 0 < (F z).re := by
  have hn : ∀ w ∈ closure U, 0 ≤ (F w).re :=
    fun w hw => real_nonneg_of_frontier hU hF hboundary hw
  by_contra h
  have hzero : (F z).re = 0 := le_antisymm (le_of_not_gt h) (hn z (subset_closure hz))
  have he : DiffContOnCl ℂ (fun w => Complex.exp (-F w)) U :=
    Complex.differentiable_exp.comp_diffContOnCl hF.neg
  have hm : IsMaxOn (norm ∘ (fun w => Complex.exp (-F w))) U z := by
    intro w hw
    change ‖Complex.exp (-F w)‖ ≤ ‖Complex.exp (-F z)‖
    rw [Complex.norm_exp, Complex.norm_exp, Complex.neg_re, Complex.neg_re, hzero]
    exact Real.exp_le_exp.mpr (by linarith [hn w (subset_closure hw)])
  obtain ⟨w, hw, hp⟩ := hpositive
  have heq := Complex.norm_eqOn_closure_of_isPreconnected_of_isMaxOn hc ho he hz hm hw
  change ‖Complex.exp (-F w)‖ = ‖Complex.exp (-F z)‖ at heq
  rw [Complex.norm_exp, Complex.norm_exp, Real.exp_eq_exp,
    Complex.neg_re, Complex.neg_re, hzero] at heq
  linarith

theorem real_pos_on_disk {F : ℂ → ℂ}
    (hF : DiffContOnCl ℂ F (ball 0 1))
    (hboundary : ∀ z : ℂ, ‖z‖ = 1 → 0 ≤ (F z).re)
    (hzero : 0 < (F 0).re) {z : ℂ} (hz : ‖z‖ < 1) : 0 < (F z).re := by
  apply real_pos_of_frontier isBounded_ball (convex_ball (0 : ℂ) 1).isPreconnected
    isOpen_ball hF
  · intro w hw
    apply hboundary w
    simpa only [frontier_ball (0 : ℂ) one_ne_zero, mem_sphere, dist_zero_right] using hw
  · exact ⟨0, subset_closure (by simp), hzero⟩
  · simpa using hz

def annulus (r R : ℝ) : Set ℂ := {z | r < ‖z‖ ∧ ‖z‖ < R}

theorem annulus_open (r R : ℝ) : IsOpen (annulus r R) :=
  (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)

theorem annulus_bounded (r R : ℝ) : Bornology.IsBounded (annulus r R) :=
  (isBounded_ball (x := (0 : ℂ)) (r := R)).subset (fun _ hz => by simpa using hz.2)

theorem annulus_closure_subset (r R : ℝ) :
    closure (annulus r R) ⊆ {z | r ≤ ‖z‖ ∧ ‖z‖ ≤ R} := by
  apply closure_minimal (show annulus r R ⊆ {z | r ≤ ‖z‖ ∧ ‖z‖ ≤ R} from
    fun _ hz => ⟨hz.1.le, hz.2.le⟩)
  exact (isClosed_le continuous_const continuous_norm).inter
    (isClosed_le continuous_norm continuous_const)

theorem annulus_frontier_subset (r R : ℝ) {z : ℂ} (hz : z ∈ frontier (annulus r R)) :
    ‖z‖ = r ∨ ‖z‖ = R := by
  have hb := annulus_closure_subset r R hz.1
  by_contra h
  push Not at h
  have hi : z ∈ annulus r R := ⟨lt_of_le_of_ne hb.1 h.1.symm, lt_of_le_of_ne hb.2 h.2⟩
  exact hz.2 (by simpa only [(annulus_open r R).interior_eq] using hi)

theorem unit_mem_closure_annulus {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    {z : ℂ} (hz : ‖z‖ = 1) : z ∈ closure (annulus r 1) := by
  rw [Metric.mem_closure_iff]
  intro e he
  let a : ℝ := (max r (1-e)+1)/2
  have ha0 : 0 < a := by dsimp [a]; have := le_max_left r (1-e); linarith
  have ha1 : a < 1 := by dsimp [a]; have := max_lt hr1 (by linarith : 1-e<1); linarith
  have har : r < a := by dsimp [a]; have := le_max_left r (1-e); linarith
  have hae : 1-a < e := by dsimp [a]; have := le_max_right r (1-e); linarith
  refine ⟨(a:ℂ)*z, ?_, ?_⟩
  · change r < ‖(a:ℂ)*z‖ ∧ ‖(a:ℂ)*z‖ < 1
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha0, hz, mul_one]
    exact ⟨har,ha1⟩
  · rw [dist_comm, dist_eq_norm, show (a:ℂ)*z-z = ((a-1:ℝ):ℂ)*z by push_cast; ring,
      norm_mul, Complex.norm_real, Real.norm_eq_abs, hz, mul_one,
      abs_of_neg (sub_neg.mpr ha1)]
    linarith

theorem annulus_preconnected {r R : ℝ} (hr : 0 < r) (hR : 0 < R) : IsPreconnected (annulus r R) := by
  let S : Set ℂ := {w | Real.log r < w.re ∧ w.re < Real.log R}
  have hc : Convex ℝ S := by
    exact (convex_Ioo (Real.log r) (Real.log R)).linear_preimage Complex.reLm
  have himage : Complex.exp '' S = annulus r R := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      change r < ‖Complex.exp w‖ ∧ ‖Complex.exp w‖ < R
      rw [Complex.norm_exp]
      constructor
      · simpa only [Real.exp_log hr] using Real.exp_lt_exp.mpr hw.1
      · simpa only [Real.exp_log hR] using Real.exp_lt_exp.mpr hw.2
    · intro hz
      have hz0 : z ≠ 0 := norm_pos_iff.mp (hr.trans hz.1)
      refine ⟨Complex.log z, ?_, Complex.exp_log hz0⟩
      change Real.log r < (Complex.log z).re ∧ (Complex.log z).re < Real.log R
      rw [Complex.log_re]
      exact ⟨Real.log_lt_log hr hz.1,
        Real.log_lt_log (hr.trans hz.1) hz.2⟩
  rw [← himage]
  exact hc.isPreconnected.image _ Complex.continuous_exp.continuousOn

theorem real_nonneg_on_annulus {F : ℂ → ℂ} {r R : ℝ}
    (hF : DiffContOnCl ℂ F (annulus r R))
    (hinner : ∀ z : ℂ, ‖z‖ = r → 0 ≤ (F z).re)
    (houter : ∀ z : ℂ, ‖z‖ = R → 0 ≤ (F z).re)
    {z : ℂ} (hz : z ∈ closure (annulus r R)) : 0 ≤ (F z).re := by
  apply real_nonneg_of_frontier (annulus_bounded r R) hF _ hz
  intro w hw
  rcases annulus_frontier_subset r R hw with h | h
  · exact hinner w h
  · exact houter w h

theorem real_pos_on_annulus {F : ℂ → ℂ} {r R : ℝ} (hr : 0 < r) (hR : 0 < R)
    (hF : DiffContOnCl ℂ F (annulus r R))
    (hinner : ∀ z : ℂ, ‖z‖ = r → 0 ≤ (F z).re)
    (houter : ∀ z : ℂ, ‖z‖ = R → 0 ≤ (F z).re)
    (hpositive : ∃ w ∈ closure (annulus r R), 0 < (F w).re)
    {z : ℂ} (hz : z ∈ annulus r R) : 0 < (F z).re := by
  apply real_pos_of_frontier (annulus_bounded r R) (annulus_preconnected hr hR)
    (annulus_open r R) hF _ hpositive hz
  intro w hw
  rcases annulus_frontier_subset r R hw with h | h
  · exact hinner w h
  · exact houter w h

end
end polyak.General.Multipliers
