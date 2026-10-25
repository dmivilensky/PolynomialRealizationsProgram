import polyak.Growth.Envelope

/-!
Article: Appendix A, positivity and quadratic lower bound for Γ.
Use: genuine quadratic potentials generate geometric free-state segments.
Proof: a complex characteristic root is realized as a real planar trajectory.
-/

namespace polyak.Growth
noncomputable section

/-- Article: quadratic test functions. Use: exact normalized scalar quadratics. -/
theorem normalized_quadratic {c : ℝ} (hc : |c| ≤ 1) :
    NormalizedSmooth (fun z : ℂ => c/2 * ‖z‖^2) := by
  have hg (z : ℂ) : HasGradientAt (fun z : ℂ => c/2 * ‖z‖^2) (c • z) z := by
    simpa using hasGradientAt_quadratic_add (hasGradientAt_const z (0 : ℝ)) c 0
  refine ⟨fun z => (hg z).differentiableAt, ?_, by simp, ?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [dist_eq_norm, (hg x).gradient, (hg y).gradient, NNReal.coe_one, one_mul]
    rw [← smul_sub, norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right hc (norm_nonneg _)).trans_eq (one_mul _)
  · rw [(hg 0).gradient, smul_zero]

/-- Article: geometric quadratic segment. Use: complex roots give real Hilbert trajectories. -/
def Segment.ofQuadraticRoot {A B β c : ℝ} (hc : |c| ≤ 1) (z : ℂ)
    (hz : z^2-((A+B*c : ℝ) : ℂ)*z+(β : ℂ)=0) (n : ℕ) :
    Segment ℂ A B β n :=
  Segment.ofNormalized (normalized_quadratic hc) (fun k => z^k) n (by
    intro k _
    have hg : gradient (fun w : ℂ => c/2*‖w‖^2) (z^(k+1)) = c • z^(k+1) := by
      have hh : HasGradientAt (fun w : ℂ => c/2*‖w‖^2) (c • z^(k+1)) (z^(k+1)) := by
        simpa using hasGradientAt_quadratic_add (hasGradientAt_const (z^(k+1)) (0 : ℝ)) c 0
      exact hh.gradient
    rw [hg]
    simp only [Complex.real_smul, Complex.ofReal_add, Complex.ofReal_mul] at hz ⊢
    rw [pow_add z k 2, pow_add z k 1, pow_one]
    linear_combination hz * z^k)

/-- Article: planar quadratic norm. Use: exact geometric norm ratios including complex roots. -/
theorem quadratic_stateNorm (z : ℂ) (k : ℕ) :
    stateNorm (fun k => z^k) k = ‖z‖^k * Real.sqrt (1+‖z‖^2) := by
  apply (sq_eq_sq₀ (stateNorm_nonneg _ _) (by positivity)).mp
  rw [stateNorm_sq, norm_pow, norm_pow, mul_pow, Real.sq_sqrt (by positivity), pow_succ]
  ring

/-- Article: quadratic lower bound. Use: every characteristic root contributes its exact modulus. -/
theorem quadraticRoot_pow_le_envelope {A B β c : ℝ} (hc : |c| ≤ 1) (z : ℂ)
    (hz : z^2-((A+B*c : ℝ) : ℂ)*z+(β : ℂ)=0) (n : ℕ) :
    ‖z‖^n ≤ envelope A B β n := by
  have hh := stateNorm_le_envelope_hilbert (Segment.ofQuadraticRoot hc z hz n)
  change stateNorm (fun k => z^k) n ≤ envelope A B β n * stateNorm (fun k => z^k) 0 at hh
  rw [quadratic_stateNorm, quadratic_stateNorm, pow_zero, one_mul] at hh
  exact (mul_le_mul_iff_left₀ (Real.sqrt_pos.2 (by positivity))).mp hh

/-- Article: strictly positive free growth. Use: logarithms have a uniform exponential lower bound. -/
theorem envelope_lower_base {A B β : ℝ} (hB : B ≠ 0) :
    ∃ b : ℝ, 0 < b ∧ ∀ n, b^n ≤ envelope A B β n := by
  by_cases hβ : β = 0
  · by_cases ha : A+B = 0
    · have hn : A-B ≠ 0 := by intro hh; apply hB; linarith
      refine ⟨|A-B|, abs_pos.mpr hn, ?_⟩
      intro n
      simpa only [Complex.norm_real, Real.norm_eq_abs] using quadraticRoot_pow_le_envelope (A := A) (B := B) (β := β)
        (c := -1) (by norm_num) ((A-B : ℝ) : ℂ) (by simp [hβ]; ring) n
    · refine ⟨|A+B|, abs_pos.mpr ha, ?_⟩
      intro n
      simpa only [Complex.norm_real, Real.norm_eq_abs] using quadraticRoot_pow_le_envelope (A := A) (B := B) (β := β)
        (c := 1) (by norm_num) ((A+B : ℝ) : ℂ) (by simp [hβ]; ring) n
  · obtain ⟨z,hz⟩ := Dynamics.exists_complex_quadratic_root A β
    have hn : z ≠ 0 := by
      intro hh
      rw [hh] at hz
      simp only [zero_pow (by norm_num : 2 ≠ 0), mul_zero, sub_self, zero_add,
        Complex.ofReal_eq_zero] at hz
      exact hβ hz
    refine ⟨‖z‖, norm_pos_iff.mpr hn, fun n => ?_⟩
    exact quadraticRoot_pow_le_envelope (c := 0) (by norm_num) z (by simpa using hz) n

/-- Article: positive Γ. Use: no division or logarithm of zero is hidden. -/
theorem envelope_pos {A B β : ℝ} (hB : B ≠ 0) (n : ℕ) : 0 < envelope A B β n := by
  obtain ⟨b,hb,hl⟩ := envelope_lower_base (A := A) (β := β) hB
  exact (pow_pos hb n).trans_le (hl n)

/-- Article: original quadratic lower bound. Use: curvature roots match normalized segments exactly. -/
theorem curvatureRoot_pow_le_envelope {μ L α β lam : ℝ} (hL : μ < L)
    (hlam : lam ∈ Set.Icc μ L) (z : ℂ)
    (hz : z^2-((1+β-α*lam : ℝ) : ℂ)*z+(β : ℂ)=0) (n : ℕ) :
    ‖z‖^n ≤ envelope (Dynamics.normalizedA μ L α β) (Dynamics.normalizedB μ L α) β n := by
  let c := (L+μ-2*lam)/(L-μ)
  have hM : 0 < L-μ := sub_pos.mpr hL
  have hc : |c| ≤ 1 := by
    apply abs_le.mpr
    constructor
    · exact (le_div_iff₀ hM).mpr (by nlinarith [hlam.2])
    · exact (div_le_iff₀ hM).mpr (by nlinarith [hlam.1])
  have ha : Dynamics.normalizedA μ L α β+Dynamics.normalizedB μ L α*c = 1+β-α*lam := by
    dsimp [Dynamics.normalizedA, Dynamics.normalizedB, c]
    field_simp
    ring
  exact quadraticRoot_pow_le_envelope hc z (by simpa only [ha] using hz) n

/-- Article: Γ(n)≥ρqⁿ. Use: the maximal actual quadratic root is attained. -/
theorem quadraticRate_pow_le_envelope {μ L α β : ℝ} (hμ : 0 < μ) (hL : μ < L)
    (hα : 0 < α) (hβ : 0 ≤ β) (hβ1 : β < 1) (hquad : α*L < 2*(1+β)) (n : ℕ) :
    Dynamics.quadraticRate μ L α β ^ n ≤
      envelope (Dynamics.normalizedA μ L α β) (Dynamics.normalizedB μ L α) β n := by
  obtain ⟨lam,hlam,z,hz,hr⟩ := (Dynamics.quadraticRate_isGreatest hμ hL hα hβ hβ1 hquad).1
  rw [hr]
  exact curvatureRoot_pow_le_envelope hL hlam z hz n

/-- Article: ρq>0. Use: the interval of curvatures contains a nonzero characteristic root. -/
theorem quadraticRate_pos {μ L α β : ℝ} (hμ : 0 < μ) (hL : μ < L)
    (hα : 0 < α) (hβ : 0 ≤ β) (hβ1 : β < 1) (hquad : α*L < 2*(1+β)) :
    0 < Dynamics.quadraticRate μ L α β := by
  have hg := Dynamics.quadraticRate_isGreatest hμ hL hα hβ hβ1 hquad
  suffices hh : ∃ lam ∈ Set.Icc μ L, ∃ z : ℂ,
      z^2-((1+β-α*lam : ℝ) : ℂ)*z+(β : ℂ)=0 ∧ z ≠ 0 by
    obtain ⟨lam,hlam,z,hz,hn⟩ := hh
    exact (norm_pos_iff.mpr hn).trans_le (hg.2 ⟨lam,hlam,z,hz,rfl⟩)
  by_cases hβ0 : β = 0
  · have hne : 1-α*μ ≠ 0 ∨ 1-α*L ≠ 0 := by
      by_contra hh
      simp only [not_or, not_not] at hh
      nlinarith [mul_pos hα (sub_pos.mpr hL)]
    rcases hne with hn | hn
    · refine ⟨μ,⟨le_rfl,hL.le⟩,((1-α*μ : ℝ) : ℂ),?_,by exact_mod_cast hn⟩
      simp only [hβ0, add_zero, Complex.ofReal_zero, add_zero]
      ring
    · refine ⟨L,⟨hL.le,le_rfl⟩,((1-α*L : ℝ) : ℂ),?_,by exact_mod_cast hn⟩
      simp only [hβ0, add_zero, Complex.ofReal_zero, add_zero]
      ring
  · obtain ⟨z,hz⟩ := Dynamics.exists_complex_quadratic_root (1+β-α*μ) β
    refine ⟨μ,⟨le_rfl,hL.le⟩,z,hz,?_⟩
    intro hh
    rw [hh] at hz
    simp only [zero_pow (by norm_num : 2 ≠ 0), mul_zero, sub_self, zero_add,
      Complex.ofReal_eq_zero] at hz
    exact hβ0 hz

end
end polyak.Growth
